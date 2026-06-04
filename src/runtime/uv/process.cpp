/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include "runtime/uv/process.h"
#include "runtime/array_ref.h"
#include "runtime/string_ref.h"
#include "runtime/option_ref.h"
#include "runtime/pair_ref.h"
#include <cstring>
#include <string>
#include <vector>
#include <iostream>

#if defined(LEAN_WINDOWS)
#include <windows.h>
#include <fcntl.h>
#include <io.h>
#include <signal.h>
#include <errno.h>
#else
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <errno.h>
#if defined(__APPLE__)
// `environ` is not directly accessible from a shared library on macOS; `_NSGetEnviron` is required.
#include <crt_externs.h>
#endif
#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

using namespace std;

enum stdio_mode { STDIO_PIPED = 0, STDIO_INHERIT = 1, STDIO_NUL = 2 };

// The finalizer of the `Child`'s libuv process wrapper.
void lean_uv_process_finalizer(void * ptr) {
    lean_uv_process_object * p = (lean_uv_process_object *) ptr;

    event_loop_lock(&global_ev);
    if (p->m_spawned) {
        // The handle is registered with the loop; close it asynchronously and free it in the close
        // callback. After `uv_close` no further callbacks (including `exit_cb`) fire for it.
        uv_close((uv_handle_t *)p->m_uv_process, [](uv_handle_t * handle) {
            free(handle);
        });
    } else {
        // `uv_spawn` never succeeded, so the handle was never registered with the loop.
        free(p->m_uv_process);
    }
    event_loop_unlock(&global_ev);

    uv_mutex_destroy(&p->m_mutex);
    uv_cond_destroy(&p->m_cond);
    free(p);
}

void initialize_libuv_process() {
    g_uv_process_external_class = lean_register_external_class(lean_uv_process_finalizer,
        [](void * /* obj */, b_obj_arg /* fn */) {});
}

// Called by libuv on the event loop thread once the child has exited (and has been reaped).
static void process_exit_cb(uv_process_t * handle, int64_t exit_status, int term_signal) {
    lean_object * obj = (lean_object *)handle->data;
    lean_uv_process_object * p = lean_to_uv_process(obj);

    uv_mutex_lock(&p->m_mutex);
    p->m_exit_status = exit_status;
    p->m_term_signal = term_signal;
    p->m_exited      = true;
    uv_cond_broadcast(&p->m_cond);
    uv_mutex_unlock(&p->m_mutex);
}

// =======================================
// stdio setup helpers.

#if defined(LEAN_WINDOWS)
static bool make_pipe(int fds[2], int * err) {
    SECURITY_ATTRIBUTES sa;
    sa.nLength = sizeof(SECURITY_ATTRIBUTES);
    sa.bInheritHandle = TRUE;
    sa.lpSecurityDescriptor = NULL;
    HANDLE readh, writeh;
    if (!CreatePipe(&readh, &writeh, &sa, 0)) { *err = GetLastError(); return false; }
    fds[0] = _open_osfhandle(reinterpret_cast<intptr_t>(readh), _O_RDONLY);
    fds[1] = _open_osfhandle(reinterpret_cast<intptr_t>(writeh), _O_APPEND);
    return true;
}
static int open_devnull(bool read, int * err) {
    int fd = _open("NUL", read ? _O_RDONLY : _O_WRONLY);
    if (fd < 0) *err = errno;
    return fd;
}
static void close_fd(int fd) { _close(fd); }
// `CreateProcess` (used by libuv with `bInheritHandles = TRUE`) inherits every inheritable handle,
// so the parent end of each pipe must be made non-inheritable; otherwise the child would hold a copy
// of, e.g., the parent's stdin write end and never observe EOF.
static void mark_not_inheritable(int fd) {
    SetHandleInformation((HANDLE)_get_osfhandle(fd), HANDLE_FLAG_INHERIT, 0);
}
#else
static bool make_pipe(int fds[2], int * err) {
#ifdef __APPLE__
    // No atomic `pipe2` on macOS; this is inherently racy, but there is nothing we can do.
    if (::pipe(fds) == -1) { *err = errno; return false; }
    if (::fcntl(fds[0], F_SETFD, FD_CLOEXEC) == -1) { *err = errno; return false; }
    if (::fcntl(fds[1], F_SETFD, FD_CLOEXEC) == -1) { *err = errno; return false; }
#else
    if (::pipe2(fds, O_CLOEXEC) == -1) { *err = errno; return false; }
#endif
    return true;
}
static int open_devnull(bool read, int * err) {
    int fd = ::open("/dev/null", read ? O_RDONLY : O_WRONLY);
    if (fd < 0) *err = errno;
    return fd;
}
static void close_fd(int fd) { ::close(fd); }
// On POSIX the pipe ends are `O_CLOEXEC`, so nothing leaks across `exec`; this is a no-op.
static void mark_not_inheritable(int) {}
#endif

// Configures stdio slot `slot` (0=stdin, 1=stdout, 2=stderr) with the given `mode`.
// On success, sets `*parent` to the parent-side handle object (or `box(0)` if none) and, if a
// child-side fd needs to be closed in the parent after `uv_spawn`, sets `*close_fd` to it.
static bool setup_child_stdio(int slot, stdio_mode mode, uv_stdio_container_t * c,
                              lean_object ** parent, int * close_fd_out, int * err) {
    bool is_in = (slot == 0);
    *parent = box(0);
    *close_fd_out = -1;
    switch (mode) {
    case STDIO_INHERIT:
        c->flags = UV_INHERIT_FD;
        c->data.fd = slot;
        return true;
    case STDIO_PIPED: {
        int fds[2];
        if (!make_pipe(fds, err)) return false;
        // fds[0] is the read end, fds[1] the write end.
        int child_fd  = is_in ? fds[0] : fds[1];
        int parent_fd = is_in ? fds[1] : fds[0];
        mark_not_inheritable(parent_fd);
        c->flags = UV_INHERIT_FD;
        c->data.fd = child_fd;
        *close_fd_out = child_fd;
        *parent = io_wrap_handle(fdopen(parent_fd, is_in ? "w" : "r"));
        return true;
    }
    case STDIO_NUL: {
        int fd = open_devnull(is_in, err);
        if (fd < 0) return false;
        c->flags = UV_INHERIT_FD;
        c->data.fd = fd;
        *close_fd_out = fd;
        return true;
    }
    }
    lean_unreachable();
}

// Builds the child environment as a NULL-terminated array of "KEY=VALUE" strings, or returns
// `nullptr` to inherit the parent environment unchanged. `storage` keeps the strings alive for the
// duration of the `uv_spawn` call.
static char ** build_env(array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & env,
                         bool inherit_env, std::vector<std::string> & storage) {
    if (inherit_env && env.size() == 0)
        return nullptr;

    // Each entry is a verbatim "KEY=VALUE" string paired with its KEY (the substring before the
    // first '='), so that user-provided overrides can replace or remove inherited entries by key.
    std::vector<std::pair<std::string, std::string>> entries; // (key, "key=value")

    auto key_of = [](char const * s) {
        char const * eq = strchr(s, '=');
        return eq ? std::string(s, eq - s) : std::string(s);
    };

    if (inherit_env) {
#if defined(LEAN_WINDOWS)
        char * esp = GetEnvironmentStrings();
        for (char * p = esp; *p; p += strlen(p) + 1)
            entries.push_back({key_of(p), std::string(p)});
        FreeEnvironmentStrings(esp);
#else
#if defined(__APPLE__)
        char ** env_block = *_NSGetEnviron();
#else
        char ** env_block = environ;
#endif
        for (char ** e = env_block; *e; ++e)
            entries.push_back({key_of(*e), std::string(*e)});
#endif
    }

    for (auto & entry : env) {
        std::string key = entry.fst().to_std_string();
        auto it = entries.begin();
        for (; it != entries.end(); ++it)
            if (it->first == key) break;
        if (entry.snd()) {
            std::string kv = key + "=" + entry.snd().get()->to_std_string();
            if (it != entries.end())
                it->second = kv;
            else
                entries.push_back({key, kv});
        } else if (it != entries.end()) {
            entries.erase(it);
        }
    }

    storage.reserve(entries.size());
    for (auto & e : entries)
        storage.push_back(std::move(e.second));

    char ** envp = (char **)malloc((storage.size() + 1) * sizeof(char *));
    for (size_t i = 0; i < storage.size(); i++)
        envp[i] = (char *)storage[i].c_str();
    envp[storage.size()] = nullptr;
    return envp;
}

extern "C" LEAN_EXPORT obj_res lean_io_process_spawn(obj_arg args_) {
    object_ref args(args_);
    object_ref stdio_cfg = cnstr_get_ref(args, 0);
    stdio_mode stdin_mode  = static_cast<stdio_mode>(cnstr_get_uint8(stdio_cfg.raw(), 0));
    stdio_mode stdout_mode = static_cast<stdio_mode>(cnstr_get_uint8(stdio_cfg.raw(), 1));
    stdio_mode stderr_mode = static_cast<stdio_mode>(cnstr_get_uint8(stdio_cfg.raw(), 2));

    if (stdin_mode == STDIO_INHERIT)
        std::cout.flush();

    string_ref proc_name = cnstr_get_ref_t<string_ref>(args, 1);
    array_ref<string_ref> proc_args = cnstr_get_ref_t<array_ref<string_ref>>(args, 2);
    option_ref<string_ref> cwd = cnstr_get_ref_t<option_ref<string_ref>>(args, 3);
    array_ref<pair_ref<string_ref, option_ref<string_ref>>> env =
        cnstr_get_ref_t<array_ref<pair_ref<string_ref, option_ref<string_ref>>>>(args, 4);
    bool inherit_env = cnstr_get_uint8(args.raw(), 5 * sizeof(object *));
    bool do_setsid   = cnstr_get_uint8(args.raw(), 5 * sizeof(object *) + 1);

    // Set up stdio for all three streams.
    uv_stdio_container_t stdio[3];
    object * parent_handles[3] = { box(0), box(0), box(0) };
    int close_fds[3] = { -1, -1, -1 };
    stdio_mode modes[3] = { stdin_mode, stdout_mode, stderr_mode };

    int err = 0;
    int configured = 0;
    bool ok = true;
    for (; configured < 3; configured++) {
        if (!setup_child_stdio(configured, modes[configured], &stdio[configured],
                               &parent_handles[configured], &close_fds[configured], &err)) {
            ok = false;
            break;
        }
    }
    if (!ok) {
        // Undo whatever was set up so far.
        for (int i = 0; i < configured; i++) {
            if (close_fds[i] >= 0) close_fd(close_fds[i]);
            lean_dec(parent_handles[i]); // closes the parent-side FILE* if it was a handle
        }
        return lean_io_result_mk_error(decode_io_error(err, nullptr));
    }

    // Build args (argv[0] is the program name) and environment.
    std::vector<char *> argv;
    argv.push_back(const_cast<char *>(proc_name.data()));
    for (auto & a : proc_args)
        argv.push_back(const_cast<char *>(a.data()));
    argv.push_back(nullptr);

    std::vector<std::string> env_storage;
    char ** envp = build_env(env, inherit_env, env_storage);

    uv_process_options_t options;
    memset(&options, 0, sizeof(options));
    options.exit_cb     = process_exit_cb;
    options.file        = proc_name.data();
    options.args        = argv.data();
    options.cwd         = cwd ? cwd.get()->data() : nullptr;
    options.env         = envp;
    options.flags       = do_setsid ? UV_PROCESS_DETACHED : 0;
    options.stdio_count = 3;
    options.stdio       = stdio;

    // Allocate the wrapper and the libuv handle.
    lean_uv_process_object * p = (lean_uv_process_object *)malloc(sizeof(lean_uv_process_object));
    p->m_uv_process  = (uv_process_t *)malloc(sizeof(uv_process_t));
    uv_mutex_init(&p->m_mutex);
    uv_cond_init(&p->m_cond);
    p->m_exited      = false;
    p->m_exit_status = 0;
    p->m_term_signal = 0;
    p->m_setsid      = do_setsid;
    p->m_spawned     = false;

    lean_object * obj = lean_uv_process_new(p);
    lean_mark_mt(obj);
    // `exit_cb` reads `data`, but it cannot fire until the loop runs again, which only happens after
    // we release the loop below, so setting this before `uv_spawn` is safe.
    p->m_uv_process->data = obj;

    event_loop_lock(&global_ev);
    int spawn_result = uv_spawn(global_ev.loop, p->m_uv_process, &options);
    if (spawn_result == 0)
        p->m_spawned = true;
    event_loop_unlock(&global_ev);

    free(envp);

    // The child has its own copies of the inherited fds now; close our child-side ends.
    for (int i = 0; i < 3; i++)
        if (close_fds[i] >= 0) close_fd(close_fds[i]);

    if (spawn_result != 0) {
        for (int i = 0; i < 3; i++)
            lean_dec(parent_handles[i]);
        lean_dec(obj); // finalizer frees the wrapper and handle (not spawned, so no `uv_close`)
        // Pass the command as the filename: some `lean_decode_uv_error` cases (e.g. `ENOENT` for a
        // missing executable) require a non-null name.
        return lean_io_result_mk_error(lean_decode_uv_error(spawn_result, proc_name.raw()));
    }

    object_ref r = mk_cnstr(0, parent_handles[0], parent_handles[1], parent_handles[2], obj);
    return lean_io_result_mk_ok(r.steal());
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_wait(b_obj_arg, b_obj_arg child) {
    lean_uv_process_object * p = lean_to_uv_process(cnstr_get(child, 3));
    uv_mutex_lock(&p->m_mutex);
    while (!p->m_exited)
        uv_cond_wait(&p->m_cond, &p->m_mutex);
    int64_t status = p->m_exit_status;
    int sig = p->m_term_signal;
    uv_mutex_unlock(&p->m_mutex);
    // use bash's convention for signal terminations
    unsigned code = sig != 0 ? static_cast<unsigned>(128 + sig) : static_cast<unsigned>(status);
    return lean_io_result_mk_ok(box_uint32(code));
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_try_wait(b_obj_arg, b_obj_arg child) {
    lean_uv_process_object * p = lean_to_uv_process(cnstr_get(child, 3));
    uv_mutex_lock(&p->m_mutex);
    bool exited = p->m_exited;
    int64_t status = p->m_exit_status;
    int sig = p->m_term_signal;
    uv_mutex_unlock(&p->m_mutex);
    if (!exited)
        return lean_io_result_mk_ok(mk_option_none());
    unsigned code = sig != 0 ? static_cast<unsigned>(128 + sig) : static_cast<unsigned>(status);
    return lean_io_result_mk_ok(mk_option_some(box_uint32(code)));
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_kill(b_obj_arg, b_obj_arg child) {
    lean_uv_process_object * p = lean_to_uv_process(cnstr_get(child, 3));
#if defined(LEAN_WINDOWS)
    // mingw does not define `SIGKILL`; libuv maps `SIGTERM` to `TerminateProcess` on Windows, which
    // matches the previous `CreateProcess`-based implementation.
    int result = uv_process_kill(p->m_uv_process, SIGTERM);
    if (result != 0)
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
#else
    pid_t pid = p->m_uv_process->pid;
    if ((p->m_setsid ? killpg(pid, SIGKILL) : kill(pid, SIGKILL)) == -1)
        return lean_io_result_mk_error(decode_io_error(errno, nullptr));
#endif
    return lean_io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_obj_arg, b_obj_arg child) {
    lean_uv_process_object * p = lean_to_uv_process(cnstr_get(child, 3));
    return p->m_uv_process->pid;
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_take_stdin(b_obj_arg, obj_arg lchild) {
    object_ref child(lchild);
    object_ref child2 = mk_cnstr(0, object_ref(box(0)), cnstr_get_ref(child, 1),
                                 cnstr_get_ref(child, 2), cnstr_get_ref(child, 3));
    object_ref r = mk_cnstr(0, cnstr_get_ref(child, 0), child2);
    return lean_io_result_mk_ok(r.steal());
}

#else

void initialize_libuv_process() {}

extern "C" LEAN_EXPORT obj_res lean_io_process_spawn(obj_arg) {
    lean_always_assert(false && ("Please build a version of Lean4 with libuv to invoke this."));
}
extern "C" LEAN_EXPORT obj_res lean_io_process_child_wait(b_obj_arg, b_obj_arg) {
    lean_always_assert(false && ("Please build a version of Lean4 with libuv to invoke this."));
}
extern "C" LEAN_EXPORT obj_res lean_io_process_child_try_wait(b_obj_arg, b_obj_arg) {
    lean_always_assert(false && ("Please build a version of Lean4 with libuv to invoke this."));
}
extern "C" LEAN_EXPORT obj_res lean_io_process_child_kill(b_obj_arg, b_obj_arg) {
    lean_always_assert(false && ("Please build a version of Lean4 with libuv to invoke this."));
}
extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_obj_arg, b_obj_arg) {
    lean_always_assert(false && ("Please build a version of Lean4 with libuv to invoke this."));
}
extern "C" LEAN_EXPORT obj_res lean_io_process_child_take_stdin(b_obj_arg, obj_arg) {
    lean_always_assert(false && ("Please build a version of Lean4 with libuv to invoke this."));
}

#endif

}
