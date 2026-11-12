/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich, Julia M. Himmel
*/
#include "runtime/uv/process.h"
#include "runtime/uv/util.h"
#include "runtime/array_ref.h"
#include "runtime/option_ref.h"
#include "runtime/pair_ref.h"
#include "runtime/string_ref.h"
#include <algorithm>
#include <iostream>
#include <new>
#include <optional>
#include <string>
#include <utility>
#include <vector>
#include <sys/stat.h>

#include <string.h>

#if defined(LEAN_WINDOWS)
#include <fcntl.h>
#include <io.h>
#else
#include <errno.h>
#include <fcntl.h>
#include <paths.h>
#include <signal.h>
#include <unistd.h>
extern "C" char ** environ;
#endif

namespace lean {
#ifndef LEAN_EMSCRIPTEN

static void process_close_cb(uv_handle_t * handle) {
    delete static_cast<lean_uv_process_object *>(handle->data);
}

// The finalizer of the `Child`'s process object.
static void process_finalizer(void * ptr) {
    lean_uv_process_object * p = static_cast<lean_uv_process_object *>(ptr);
    event_loop_guard guard;
    if (p->m_exited) {
        uv_close((uv_handle_t *)&p->m_uv_process, process_close_cb);
    } else {
        // The exit callback closes the handle once libuv has reaped the child.
        p->m_dropped = true;
    }
}

void initialize_libuv_process() {
    g_uv_process_external_class = lean_register_external_class(process_finalizer, [](void *, b_obj_arg) {});
}

// Runs on the loop thread once libuv has reaped the child.
static void process_exit_cb(uv_process_t * handle, int64_t exit_status, int term_signal) {
    lean_uv_process_object * p = static_cast<lean_uv_process_object *>(handle->data);
#if defined(LEAN_WINDOWS)
    // `term_signal` only echoes the signal given to `uv_process_kill`; the exit code is the real one.
    (void)term_signal;
    uint32_t exit_code = static_cast<uint32_t>(exit_status);
#else
    // bash's convention for a child terminated by a signal
    uint32_t exit_code = term_signal != 0 ? 128 + term_signal : static_cast<uint32_t>(exit_status);
#endif
    {
        lock_guard<mutex> lock(p->m_mutex);
        p->m_exit_code = exit_code;
        p->m_exited = true;
        p->m_exited_cond.notify_all();
    }
    if (p->m_dropped) {
        uv_close((uv_handle_t *)handle, process_close_cb);
    }
}

static void close_fd(uv_file fd) {
#if defined(LEAN_WINDOWS)
    _close(fd);
#else
    close(fd);
#endif
}

// The child's ends of its stdio pipes, which the parent closes once `uv_spawn` has returned.
struct child_pipe_ends {
    uv_file m_fds[3] = {-1, -1, -1};
    ~child_pipe_ends() {
        for (uv_file fd : m_fds) {
            if (fd >= 0) close_fd(fd);
        }
    }
};

// The values of `IO.Process.Stdio`.
enum class stdio_mode : uint8_t { piped = 0, inherit = 1, null = 2 };

// Connects the child's stream `fd` according to `mode`, creating a pipe for `piped` with the parent's
// end in `parent_end`. Returns an error result on failure and `nullptr` otherwise.
static obj_res setup_stdio(int fd, stdio_mode mode, uv_stdio_container_t & container, child_pipe_ends & child_ends,
                           object_ref & parent_end) {
    switch (mode) {
    case stdio_mode::inherit:
#if !defined(LEAN_WINDOWS)
        // `posix_spawn` fails on a closed descriptor, which `fork` used to pass on as closed.
        if (fcntl(fd, F_GETFD) == -1 && errno == EBADF) {
            container.flags = UV_IGNORE;
            return nullptr;
        }
#endif
        container.flags = UV_INHERIT_FD;
        container.data.fd = fd;
        return nullptr;
    case stdio_mode::null:
        // libuv connects ignored standard streams to the null device.
        container.flags = UV_IGNORE;
        return nullptr;
    case stdio_mode::piped: {
        // Neither end is inherited by children; `uv_spawn` passes the child's end to this child only.
        uv_file ends[2];
        if (int err = uv_pipe(ends, 0, 0)) {
            return io_result_mk_uv_error(err);
        }
        bool to_child = fd == 0;
        uv_file parent_fd = ends[to_child ? 1 : 0];
        child_ends.m_fds[fd] = ends[to_child ? 0 : 1];
#if defined(LEAN_WINDOWS)
        // Without this, the CRT translates line endings and stops reading at `\x1a`.
        _setmode(parent_fd, _O_BINARY);
#endif
        FILE * file = fdopen(parent_fd, to_child ? "wb" : "rb");
        if (file == nullptr) {
            obj_res err = io_result_mk_error(decode_io_error(errno, nullptr));
            close_fd(parent_fd);
            return err;
        }
        parent_end = object_ref(io_wrap_handle(file));
        container.flags = UV_INHERIT_FD;
        container.data.fd = child_ends.m_fds[fd];
        return nullptr;
    }
    }
    lean_unreachable();
}

static bool env_names_equal(std::string const & a, char const * b) {
#if defined(LEAN_WINDOWS)
    return _stricmp(a.c_str(), b) == 0;
#else
    return a == b;
#endif
}

// Builds the child's environment as `NAME=VALUE` strings into `entries`.
static int build_env(array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & env, bool inherit_env,
                     std::vector<std::string> & entries) {
    std::vector<std::pair<std::string, std::string>> vars;
    if (inherit_env) {
        uv_env_item_t * items;
        int count;
        if (int err = uv_os_environ(&items, &count)) return err;
        uv_owned_array<uv_env_item_t, uv_os_free_environ> parent_env(items, count);
        for (uv_env_item_t const & item : parent_env) {
            vars.emplace_back(item.name, item.value);
        }
    }
    for (auto const & entry : env) {
        char const * name = entry.fst().data();
        // `setenv` rejects such names
        if (!is_env_var_name(name)) continue;
        auto it = std::find_if(vars.begin(), vars.end(), [&](auto const & var) { return env_names_equal(var.first, name); });
        if (entry.snd()) {
            std::string value = entry.snd().get()->data();
            if (it != vars.end()) {
                it->second = std::move(value);
            } else {
                vars.emplace_back(name, std::move(value));
            }
        } else if (it != vars.end()) {
            vars.erase(it);
        }
    }
    entries.reserve(vars.size());
    for (auto const & var : vars) {
        entries.push_back(var.first + "=" + var.second);
    }
    return 0;
}

// libuv fails with the same error for a missing working directory as for a missing executable.
static obj_res mk_spawn_error(int err, string_ref const & cmd, option_ref<string_ref> const & cwd) {
    if (cwd) {
        uv_fs_t req;
        int stat_err = uv_fs_stat(nullptr, &req, cwd.get()->data(), nullptr);
        bool is_dir = stat_err == 0 && (req.statbuf.st_mode & S_IFMT) == S_IFDIR;
        uv_fs_req_cleanup(&req);
        if (!is_dir) {
            return io_result_mk_error(decode_uv_error(stat_err != 0 ? stat_err : UV_ENOTDIR, cwd.get()->raw()));
        }
    }
    return io_result_mk_error(decode_uv_error(err, cmd.raw()));
}

// Returns the first string in the arguments that cannot be passed to the child as a C string.
static b_obj_arg find_nul(string_ref const & cmd, array_ref<string_ref> const & cmd_args,
                          option_ref<string_ref> const & cwd,
                          array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & env) {
    if (string_has_nul(cmd.raw())) return cmd.raw();
    for (string_ref const & arg : cmd_args) {
        if (string_has_nul(arg.raw())) return arg.raw();
    }
    if (cwd && string_has_nul(cwd.get()->raw())) return cwd.get()->raw();
    for (auto const & entry : env) {
        if (string_has_nul(entry.fst().raw())) return entry.fst().raw();
        if (entry.snd() && string_has_nul(entry.snd().get()->raw())) return entry.snd().get()->raw();
    }
    return nullptr;
}

#if !defined(LEAN_WINDOWS)
static bool is_executable_file(std::string const & file, char const * cwd) {
    std::string resolved = file[0] != '/' && cwd != nullptr ? std::string(cwd) + "/" + file : file;
    struct stat st;
    return stat(resolved.c_str(), &st) == 0 && S_ISREG(st.st_mode) && access(resolved.c_str(), X_OK) == 0;
}

// Finds the file that `uv_spawn` tried to execute for `cmd`, searching `PATH` in `envp` as libuv
// does. Relative paths are relative to the child's working directory `cwd`.
static std::optional<std::string> find_executed_file(char const * cmd, char * const * envp, char const * cwd) {
    if (strchr(cmd, '/') != nullptr) {
        return std::string(cmd);
    }
    char const * path = _PATH_DEFPATH;
    for (char * const * e = envp; *e != nullptr; e++) {
        if (strncmp(*e, "PATH=", 5) == 0) {
            path = *e + 5;
            break;
        }
    }
    while (true) {
        char const * end = strchr(path, ':');
        if (end == nullptr) end = path + strlen(path);
        std::string file = end == path ? std::string(cmd) : std::string(path, end) + "/" + cmd;
        if (is_executable_file(file, cwd)) {
            return file;
        }
        if (*end == '\0') {
            return std::nullopt;
        }
        path = end + 1;
    }
}
#endif

// Returns the new process object, or `nullptr` and the error in `err`.
static lean_uv_process_object * spawn_process(uv_process_options_t const & options, bool setsid, int & err) {
    lean_uv_process_object * p = new (std::nothrow) lean_uv_process_object;
    if (p == nullptr) {
        err = UV_ENOMEM;
        return nullptr;
    }
    p->m_setsid = setsid;
    event_loop_guard guard;
    err = uv_spawn(global_ev.m_loop, &p->m_uv_process, &options);
    p->m_uv_process.data = p;
    if (err != 0) {
        // A handle that failed to spawn still has to be closed.
        uv_close((uv_handle_t *)&p->m_uv_process, process_close_cb);
        return nullptr;
    }
    return p;
}

/* IO.Process.spawn (args : SpawnArgs) : IO (Child args.toStdioConfig) */
extern "C" LEAN_EXPORT obj_res lean_io_process_spawn(obj_arg args_) {
    object_ref args(args_);
    object_ref stdio_cfg = cnstr_get_ref(args, 0);
    string_ref const & cmd = cnstr_get_ref_t<string_ref>(args, 1);
    array_ref<string_ref> const & cmd_args = cnstr_get_ref_t<array_ref<string_ref>>(args, 2);
    option_ref<string_ref> const & cwd = cnstr_get_ref_t<option_ref<string_ref>>(args, 3);
    auto const & env = cnstr_get_ref_t<array_ref<pair_ref<string_ref, option_ref<string_ref>>>>(args, 4);
    bool inherit_env = cnstr_get_uint8(args.raw(), 5 * sizeof(object *));
    bool setsid      = cnstr_get_uint8(args.raw(), 5 * sizeof(object *) + 1);
    if (b_obj_arg s = find_nul(cmd, cmd_args, cwd, env)) {
        return mk_embedded_nul_error(s);
    }

    uv_stdio_container_t stdio[3];
    child_pipe_ends child_ends;
    object_ref parent_ends[3];
    for (int fd = 0; fd < 3; fd++) {
        stdio_mode mode = static_cast<stdio_mode>(cnstr_get_uint8(stdio_cfg.raw(), fd));
        if (obj_res err = setup_stdio(fd, mode, stdio[fd], child_ends, parent_ends[fd])) {
            return err;
        }
    }
    if (static_cast<stdio_mode>(cnstr_get_uint8(stdio_cfg.raw(), 0)) == stdio_mode::inherit) {
        std::cout.flush();
    }

    std::vector<char *> argv;
    argv.reserve(cmd_args.size() + 2);
    argv.push_back(const_cast<char *>(cmd.data()));
    for (string_ref const & arg : cmd_args) {
        argv.push_back(const_cast<char *>(arg.data()));
    }
    argv.push_back(nullptr);

    std::vector<std::string> env_entries;
    std::vector<char *> envp;
    bool own_env = !inherit_env || env.size() > 0;
    if (own_env) {
        if (int err = build_env(env, inherit_env, env_entries)) {
            return io_result_mk_uv_error(err);
        }
        envp.reserve(env_entries.size() + 1);
        for (std::string & entry : env_entries) {
            envp.push_back(entry.data());
        }
        envp.push_back(nullptr);
    }

    uv_process_options_t options = {};
    options.exit_cb     = process_exit_cb;
    options.file        = cmd.data();
    options.args        = argv.data();
    options.env         = own_env ? envp.data() : nullptr;
    options.cwd         = cwd ? cwd.get()->data() : nullptr;
    options.stdio_count = 3;
    options.stdio       = stdio;
#if !defined(LEAN_WINDOWS)
    // On Windows, this would also detach the child from the console.
    if (setsid) {
        options.flags |= UV_PROCESS_DETACHED;
    }
#endif

    int err;
    lean_uv_process_object * p = spawn_process(options, setsid, err);
#if !defined(LEAN_WINDOWS)
    // Unlike `execvp`, `posix_spawn` does not run executable files without a shebang via `/bin/sh`.
    if (err == UV_ENOEXEC) {
        if (auto file = find_executed_file(cmd.data(), own_env ? envp.data() : environ, options.cwd)) {
            std::vector<char *> sh_argv = { const_cast<char *>(_PATH_BSHELL), file->data() };
            sh_argv.insert(sh_argv.end(), argv.begin() + 1, argv.end());
            uv_process_options_t sh_options = options;
            sh_options.file = _PATH_BSHELL;
            sh_options.args = sh_argv.data();
            int sh_err;
            if ((p = spawn_process(sh_options, setsid, sh_err)) != nullptr) {
                err = 0;
            }
        }
    }
#endif
    if (p == nullptr) {
        return err == UV_ENOMEM ? io_result_mk_enomem() : mk_spawn_error(err, cmd, cwd);
    }

    object_ref child = mk_cnstr(0, parent_ends[0].steal(), parent_ends[1].steal(), parent_ends[2].steal(),
                                lean_uv_process_new(p));
    return lean_io_result_mk_ok(child.steal());
}

/* IO.Process.Child.wait {cfg : @& StdioConfig} : @& Child cfg → IO UInt32 */
extern "C" LEAN_EXPORT obj_res lean_io_process_child_wait(b_obj_arg, b_obj_arg child) {
    lean_uv_process_object * p = lean_to_uv_process(cnstr_get(child, 3));
    unique_lock<mutex> lock(p->m_mutex);
    // Only the loop thread runs the exit callback, so a wait on that thread would never end.
    if (!p->m_exited && global_ev.on_loop_thread()) {
        return io_result_mk_error("cannot wait for a child process on the event loop thread");
    }
    p->m_exited_cond.wait(lock, [&] { return p->m_exited; });
    return lean_io_result_mk_ok(box_uint32(p->m_exit_code));
}

/* IO.Process.Child.tryWait {cfg : @& StdioConfig} : @& Child cfg → IO (Option UInt32) */
extern "C" LEAN_EXPORT obj_res lean_io_process_child_try_wait(b_obj_arg, b_obj_arg child) {
    lean_uv_process_object * p = lean_to_uv_process(cnstr_get(child, 3));
    lock_guard<mutex> lock(p->m_mutex);
    if (!p->m_exited) {
        return lean_io_result_mk_ok(mk_option_none());
    }
    return lean_io_result_mk_ok(mk_option_some(box_uint32(p->m_exit_code)));
}

/* IO.Process.Child.kill {cfg : @& StdioConfig} (child : @& Child cfg) (force : Bool) : IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_process_child_kill(b_obj_arg, b_obj_arg child, uint8_t force) {
    lean_uv_process_object * p = lean_to_uv_process(cnstr_get(child, 3));
    int sig = force ? SIGKILL : SIGTERM;
    int err;
    {
        // libuv reaps the child under the loop lock, so `uv_process_kill` cannot signal another
        // process that has reused the child's pid.
        event_loop_guard guard;
#if !defined(LEAN_WINDOWS)
        if (p->m_setsid) {
            // The group outlives its leader as long as it has members, so it is killed even after
            // the child has exited.
            err = killpg(uv_process_get_pid(&p->m_uv_process), sig) == 0 ? 0 : uv_translate_sys_error(errno);
        } else
#endif
        {
            err = uv_process_kill(&p->m_uv_process, sig);
        }
    }
    // `UV_ESRCH`: everything to be killed has already exited.
    if (err != 0 && err != UV_ESRCH) {
        return io_result_mk_uv_error(err);
    }
    return lean_io_result_mk_ok(box(0));
}

/* IO.Process.Child.pid {cfg : @& StdioConfig} : @& Child cfg → UInt32 */
extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_obj_arg, b_obj_arg child) {
    return uv_process_get_pid(&lean_to_uv_process(cnstr_get(child, 3))->m_uv_process);
}

#else

void initialize_libuv_process() {}

/* IO.Process.spawn (args : SpawnArgs) : IO (Child args.toStdioConfig) */
extern "C" LEAN_EXPORT obj_res lean_io_process_spawn(obj_arg args) {
    lean_dec(args);
    return io_result_mk_error("spawning processes is not supported");
}

/* IO.Process.Child.wait {cfg : @& StdioConfig} : @& Child cfg → IO UInt32 */
extern "C" LEAN_EXPORT obj_res lean_io_process_child_wait(b_obj_arg, b_obj_arg) {
    lean_unreachable();
}

/* IO.Process.Child.tryWait {cfg : @& StdioConfig} : @& Child cfg → IO (Option UInt32) */
extern "C" LEAN_EXPORT obj_res lean_io_process_child_try_wait(b_obj_arg, b_obj_arg) {
    lean_unreachable();
}

/* IO.Process.Child.kill {cfg : @& StdioConfig} (child : @& Child cfg) (force : Bool) : IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_process_child_kill(b_obj_arg, b_obj_arg, uint8_t) {
    lean_unreachable();
}

/* IO.Process.Child.pid {cfg : @& StdioConfig} : @& Child cfg → UInt32 */
extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_obj_arg, b_obj_arg) {
    lean_unreachable();
}

#endif

/* IO.Process.Child.takeStdin {cfg : @& StdioConfig} : Child cfg → IO (cfg.stdin.toHandleType × Child { cfg with stdin := Stdio.null }) */
extern "C" LEAN_EXPORT obj_res lean_io_process_child_take_stdin(b_obj_arg, obj_arg child_) {
    object_ref child(child_);
    object_ref rest = mk_cnstr(0, object_ref(box(0)), cnstr_get_ref(child, 1), cnstr_get_ref(child, 2),
                               cnstr_get_ref(child, 3));
    object_ref r = mk_cnstr(0, cnstr_get_ref(child, 0), rest);
    return lean_io_result_mk_ok(r.steal());
}

}
