/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include <system_error>
#include <vector>
#include <unordered_map>
#include <cstring>
#include <optional>
#include <mutex>
#include <condition_variable>

#if defined(LEAN_WINDOWS)
#include <unordered_map>
#include <windows.h>
#include <fcntl.h>
#include <io.h>
#include <tchar.h>
#include <stdio.h>
#include <strsafe.h>
#else
#include <unistd.h>
#include <fcntl.h>
#include <sys/wait.h>
#include <signal.h>
#include <limits.h> // NOLINT
#endif

#ifdef __linux
#include <sys/syscall.h>
#endif

#include "runtime/object.h"
#include "runtime/io.h"
#include "runtime/uv/event_loop.h"
#include "runtime/array_ref.h"
#include "runtime/string_ref.h"
#include "runtime/option_ref.h"
#include "runtime/pair_ref.h"
#include "runtime/buffer.h"

namespace lean {

#if !defined(LEAN_WINDOWS)
extern "C" char **environ;
#endif

enum stdio {
    PIPED,
    INHERIT,
    NUL,
};

struct lean_process_child_object {
    uv_process_t * m_uv_process;
    std::mutex m_mutex;
    std::condition_variable m_cv;
    bool m_exited;
    int64_t m_exit_status;

    lean_process_child_object() : m_uv_process(nullptr), m_exited(false), m_exit_status(0) {}
};

static lean_external_class * g_process_child_external_class = nullptr;

static void process_child_finalizer(void * ptr) {
    lean_process_child_object * child = static_cast<lean_process_child_object *>(ptr);
    event_loop_lock(&global_ev);
    if (child->m_uv_process) {
        uv_close((uv_handle_t*)child->m_uv_process, [](uv_handle_t* handle) {
            free(handle);
        });
    }
    event_loop_unlock(&global_ev);
    delete child;
}

static void process_child_foreach(void * /* mod */, b_obj_arg /* fn */) {
}

#if defined(LEAN_WINDOWS)

static lean_external_class * g_win_handle_external_class = nullptr;

static void win_handle_finalizer(void * h) {
    lean_always_assert(CloseHandle(static_cast<HANDLE>(h)));
}

static void win_handle_foreach(void * /* mod */, b_obj_arg /* fn */) {
}

lean_object * wrap_win_handle(HANDLE h) {
    return lean_alloc_external(g_win_handle_external_class, static_cast<void *>(h));
}

extern "C" LEAN_EXPORT obj_res lean_io_process_get_current_dir() {
    char path[MAX_PATH];
    DWORD sz = GetCurrentDirectory(MAX_PATH, path);
    if (sz != 0) {
        return io_result_mk_ok(lean_mk_string_from_bytes(path, sz));
    } else {
        return io_result_mk_error((sstream() << GetLastError()).str());
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_process_set_current_dir(b_obj_arg path) {
    if (SetCurrentDirectory(string_cstr(path))) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error((sstream() << GetLastError()).str());
    }
}

extern "C" LEAN_EXPORT uint32_t lean_io_process_get_pid() {
    return GetCurrentProcessId();
}

extern "C" LEAN_EXPORT uint64_t lean_io_get_tid() {
    return GetCurrentThreadId();
}





void initialize_process() {
    g_win_handle_external_class = lean_register_external_class(win_handle_finalizer, win_handle_foreach);
    g_process_child_external_class = lean_register_external_class(process_child_finalizer, process_child_foreach);
}
void finalize_process() {}

#else

extern "C" LEAN_EXPORT obj_res lean_io_process_get_current_dir() {
    char path[PATH_MAX];
    if (getcwd(path, PATH_MAX)) {
        return io_result_mk_ok(mk_string(path));
    } else {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_process_set_current_dir(b_obj_arg path) {
    if (!chdir(string_cstr(path))) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(decode_io_error(errno, path));
    }
}

extern "C" LEAN_EXPORT uint32_t lean_io_process_get_pid() {
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    return getpid();
}

extern "C" LEAN_EXPORT uint64_t lean_io_get_tid() {
    uint64_t tid;
#ifdef __APPLE__
    lean_always_assert(pthread_threadid_np(NULL, &tid) == 0);
#elif defined(LEAN_EMSCRIPTEN)
    tid = 0;
#else
    // since Linux 2.4.11, our glibc 2.27 requires at least 3.2
    // glibc 2.30 would provide a wrapper
    tid = (pid_t)syscall(SYS_gettid);
#endif
    return tid;
}





void initialize_process() {
    g_process_child_external_class = lean_register_external_class(process_child_finalizer, process_child_foreach);
}
void finalize_process() {}

#endif

struct pipe { int m_read_fd; int m_write_fd; };

static pipe create_pipe() {
    int fds[2];
#if defined(LEAN_WINDOWS)
    HANDLE readh, writeh;
    SECURITY_ATTRIBUTES saAttr;
    saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
    saAttr.bInheritHandle = TRUE;
    saAttr.lpSecurityDescriptor = NULL;
    if (!CreatePipe(&readh, &writeh, &saAttr, 0))
        throw std::system_error(GetLastError(), std::system_category());
    fds[0] = _open_osfhandle(reinterpret_cast<intptr_t>(readh), 0);
    fds[1] = _open_osfhandle(reinterpret_cast<intptr_t>(writeh), 0);
#else
    if (pipe2(fds, O_CLOEXEC) == -1) throw errno;
#endif
    return pipe { fds[0], fds[1] };
}

static std::pair<std::optional<pipe>, uv_stdio_container_t> setup_stdio(stdio cfg, int default_fd, bool is_in) {
    std::optional<pipe> p;
    uv_stdio_container_t container;
    memset(&container, 0, sizeof(uv_stdio_container_t));

    if (cfg == stdio::PIPED) {
        p = create_pipe();
        container.flags = UV_INHERIT_FD;
        container.data.fd = is_in ? p->m_read_fd : p->m_write_fd;
    } else if (cfg == stdio::NUL) {
        container.flags = UV_IGNORE;
    } else {
        container.flags = UV_INHERIT_FD;
        container.data.fd = default_fd;
    }
    return { p, container };
}

static obj_res spawn(string_ref const & proc_name, array_ref<string_ref> const & args, stdio stdin_mode, stdio stdout_mode,
                     stdio stderr_mode, option_ref<string_ref> const & cwd, array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & env,
                     bool inherit_env, bool do_setsid) {

    uv_stdio_container_t child_stdio[3];

    auto stdin_res = setup_stdio(stdin_mode, 0, true);
    std::optional<pipe> stdin_pipe = stdin_res.first;
    child_stdio[0] = stdin_res.second;

    auto stdout_res = setup_stdio(stdout_mode, 1, false);
    std::optional<pipe> stdout_pipe = stdout_res.first;
    child_stdio[1] = stdout_res.second;

    auto stderr_res = setup_stdio(stderr_mode, 2, false);
    std::optional<pipe> stderr_pipe = stderr_res.first;
    child_stdio[2] = stderr_res.second;


    std::vector<std::string> pargs_strs;
    pargs_strs.push_back(proc_name.to_std_string());
    for (auto & arg : args)
        pargs_strs.push_back(arg.to_std_string());

    buffer<char*> pargs;
    pargs.ensure_capacity(pargs_strs.size() + 1);
    for (auto & s : pargs_strs)
        pargs.push_back(const_cast<char*>(s.c_str()));
    pargs.push_back(NULL);

    std::vector<std::string> penv_strs;
    buffer<char*> penv;

    if (env.size() || !inherit_env) {
        std::unordered_map<std::string, std::string> env_map;

        if (inherit_env) {
#if defined(LEAN_WINDOWS)
            auto *esp = GetEnvironmentStrings();
            char *key_begin = esp;
            while (*key_begin) {
                char *key_end = strchr(key_begin, '=');
                char *entry_end = key_end + strlen(key_end);
                env_map[std::string(key_begin, key_end)] = std::string(key_end + 1, entry_end);
                key_begin = entry_end + 1;
            }
            FreeEnvironmentStrings(esp);
#else

            for (char **e = environ; *e; ++e) {
                char *key_end = strchr(*e, '=');
                if (key_end) {
                    env_map[std::string(*e, key_end)] = std::string(key_end + 1);
                }
            }
#endif
        }

        for (auto & entry : env) {
            if (entry.snd()) {
                env_map[entry.fst().to_std_string()] = entry.snd().get()->to_std_string();
            } else {
                env_map.erase(entry.fst().to_std_string());
            }
        }

        penv_strs.reserve(env_map.size());
        for (auto & pair : env_map) {
            penv_strs.push_back(std::move(pair.first) + "=" + std::move(pair.second));
        }

        penv.ensure_capacity(penv_strs.size() + 1);
        for (auto & s : penv_strs) {
            penv.push_back(const_cast<char*>(s.c_str()));
        }
        penv.push_back(NULL);
    }

    uv_process_options_t options;
    memset(&options, 0, sizeof(uv_process_options_t));
    options.file = proc_name.data();
    options.args = pargs.data();
    options.env = penv.empty() ? NULL : penv.data();
    options.cwd = cwd ? cwd.get()->data() : NULL;
    options.stdio_count = 3;
    options.stdio = child_stdio;

    if (do_setsid) {
        options.flags |= UV_PROCESS_DETACHED;
    }

    lean_process_child_object * child_obj = new lean_process_child_object();
    child_obj->m_uv_process = (uv_process_t*)malloc(sizeof(uv_process_t));
    child_obj->m_uv_process->data = child_obj;

    options.exit_cb = [](uv_process_t* process, int64_t exit_status, int term_signal) {
        lean_process_child_object * child = static_cast<lean_process_child_object *>(process->data);
        std::lock_guard<std::mutex> lock(child->m_mutex);
        child->m_exited = true;
        child->m_exit_status = term_signal ? 128 + term_signal : exit_status;
        child->m_cv.notify_all();
    };

    event_loop_lock(&global_ev);
    int spawn_r = uv_spawn(global_ev.loop, child_obj->m_uv_process, &options);
    event_loop_unlock(&global_ev);

    if (spawn_r != 0) {
        free(child_obj->m_uv_process);
        delete child_obj;
        if (stdin_pipe) { close(stdin_pipe->m_read_fd); close(stdin_pipe->m_write_fd); }
        if (stdout_pipe) { close(stdout_pipe->m_read_fd); close(stdout_pipe->m_write_fd); }
        if (stderr_pipe) { close(stderr_pipe->m_read_fd); close(stderr_pipe->m_write_fd); }
        return lean_io_result_mk_error(lean_decode_uv_error(spawn_r, NULL));
    }

    object * parent_stdin  = box(0);
    object * parent_stdout = box(0);
    object * parent_stderr = box(0);
    if (stdin_pipe) {
        close(stdin_pipe->m_read_fd);
        parent_stdin = io_wrap_handle(fdopen(stdin_pipe->m_write_fd, "w"));
    }

    if (stdout_pipe) {
        close(stdout_pipe->m_write_fd);
        parent_stdout = io_wrap_handle(fdopen(stdout_pipe->m_read_fd, "r"));
    }

    if (stderr_pipe) {
        close(stderr_pipe->m_write_fd);
        parent_stderr = io_wrap_handle(fdopen(stderr_pipe->m_read_fd, "r"));
    }

    object * child_val = lean_alloc_external(g_process_child_external_class, child_obj);
    object_ref r = mk_cnstr(0, parent_stdin, parent_stdout, parent_stderr, child_val);
    return lean_io_result_mk_ok(r.steal());
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_take_stdin(b_obj_arg, obj_arg lchild) {
    object_ref child(lchild);
    object_ref child2 = mk_cnstr(0, object_ref(box(0)), cnstr_get_ref(child, 1), cnstr_get_ref(child, 2), cnstr_get_ref(child, 3));
    object_ref r = mk_cnstr(0, cnstr_get_ref(child, 0), child2);
    return lean_io_result_mk_ok(r.steal());
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_wait(b_obj_arg, b_obj_arg child) {
    lean_object * child_obj = cnstr_get(child, 3);
    lean_process_child_object * data = static_cast<lean_process_child_object *>(lean_get_external_data(child_obj));

    std::unique_lock<std::mutex> lock(data->m_mutex);
    data->m_cv.wait(lock, [data] { return data->m_exited; });

    return lean_io_result_mk_ok(box_uint32(data->m_exit_status));
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_try_wait(b_obj_arg, b_obj_arg child) {
    lean_object * child_obj = cnstr_get(child, 3);
    lean_process_child_object * data = static_cast<lean_process_child_object *>(lean_get_external_data(child_obj));

    std::lock_guard<std::mutex> lock(data->m_mutex);
    if (data->m_exited) {
        return lean_io_result_mk_ok(mk_option_some(box_uint32(data->m_exit_status)));
    } else {
        return lean_io_result_mk_ok(mk_option_none());
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_kill(b_obj_arg, b_obj_arg child) {
    lean_object * child_obj = cnstr_get(child, 3);
    lean_process_child_object * data = static_cast<lean_process_child_object *>(lean_get_external_data(child_obj));

    std::lock_guard<std::mutex> lock(data->m_mutex);
    if (!data->m_exited && data->m_uv_process) {
        int r = uv_process_kill(data->m_uv_process, SIGKILL);
        if (r != 0) {
            return lean_io_result_mk_error(lean_decode_uv_error(r, NULL));
        }
    }
    return lean_io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_obj_arg, b_obj_arg child) {
    lean_object * child_obj = cnstr_get(child, 3);
    lean_process_child_object * data = static_cast<lean_process_child_object *>(lean_get_external_data(child_obj));
    if (data->m_uv_process) {
        return data->m_uv_process->pid;
    }
    return 0;
}

extern "C" lean_object* lean_mk_io_error_other_error(uint32_t, lean_object*);

extern "C" LEAN_EXPORT obj_res lean_io_process_spawn(obj_arg args_) {
    object_ref args(args_);
    object_ref stdio_cfg = cnstr_get_ref(args, 0);
    stdio stdin_mode  = static_cast<stdio>(cnstr_get_uint8(stdio_cfg.raw(), 0));
    stdio stdout_mode = static_cast<stdio>(cnstr_get_uint8(stdio_cfg.raw(), 1));
    stdio stderr_mode = static_cast<stdio>(cnstr_get_uint8(stdio_cfg.raw(), 2));
    if (stdin_mode == stdio::INHERIT) {
        std::cout.flush();
    }
    try {
        return spawn(
                cnstr_get_ref_t<string_ref>(args, 1),
                cnstr_get_ref_t<array_ref<string_ref>>(args, 2),
                stdin_mode,
                stdout_mode,
                stderr_mode,
                cnstr_get_ref_t<option_ref<string_ref>>(args, 3),
                cnstr_get_ref_t<array_ref<pair_ref<string_ref, option_ref<string_ref>>>>(args, 4),
                cnstr_get_uint8(args.raw(), 5 * sizeof(object *)),
                cnstr_get_uint8(args.raw(), 5 * sizeof(object *) + 1));
    } catch (int err) {
        return lean_io_result_mk_error(decode_io_error(err, nullptr));
    } catch (std::system_error const & err) {
        // TODO: decode
        return lean_io_result_mk_error(lean_mk_io_error_other_error(err.code().value(), mk_string(err.code().message())));
    }
}

}
