/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jared Roesch, Robin Arnez
*/
#include <string>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include <system_error>

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
#include "runtime/array_ref.h"
#include "runtime/string_ref.h"
#include "runtime/option_ref.h"
#include "runtime/pair_ref.h"
#include "runtime/buffer.h"
#include "runtime/uv/event_loop.h"

namespace lean {

enum stdio {
    PIPED,
    INHERIT,
    NUL,
};

static lean_external_class * g_uv_handle_external_class = nullptr;

static void uv_handle_close_cb(uv_handle_t * h) {
    free(h);
}

static void uv_handle_finalizer(void * h) {
    uv_handle_t * handle = static_cast<uv_handle_t *>(h);
    object * promise = static_cast<object *>(handle->data);
    dec(promise);
    uv_close(handle, &uv_handle_close_cb);
}

static void uv_handle_foreach(void * h, b_obj_arg fn) {
    uv_process_t * handle = static_cast<uv_process_t *>(h);
    object * promise = static_cast<object *>(handle->data);
    inc(fn);
    inc(promise);
    dec(lean_apply_1(fn, promise));
}

/* assumes that h has been allocated using malloc */
lean_object * wrap_uv_handle(uv_handle_t * h) {
    return lean_alloc_external(g_uv_handle_external_class, static_cast<void *>(h));
}

void initialize_process() {
    g_uv_handle_external_class = lean_register_external_class(uv_handle_finalizer, uv_handle_foreach);
    uv_disable_stdio_inheritance();
}
void finalize_process() {}

extern "C" LEAN_EXPORT obj_res lean_io_process_get_current_dir(obj_arg) {
    char path[4096];
    size_t sz = sizeof(path);
    int err = uv_cwd(path, &sz);
    if (err == 0) {
        return io_result_mk_ok(lean_mk_string_from_bytes(path, sz));
    } else {
        return io_result_mk_error(lean_decode_uv_error(err, nullptr));
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_process_set_current_dir(b_obj_arg path, obj_arg) {
    const char * dir = string_cstr(path);
    if (strlen(dir) != lean_string_size(path) - 1) {
        return mk_embedded_nul_error(path);
    }
    int err = uv_chdir(dir);
    if (err == 0) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(lean_decode_uv_error(err, nullptr));
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_process_get_pid(obj_arg) {
    return lean_io_result_mk_ok(box_uint32(uv_os_getpid()));
}

// No libuv equivalent?
extern "C" LEAN_EXPORT obj_res lean_io_get_tid(obj_arg) {
    uint64_t tid;
#ifdef LEAN_WINDOWS
    tid = GetCurrentThreadId();
#elif defined(__APPLE__)
    lean_always_assert(pthread_threadid_np(NULL, &tid) == 0);
#elif defined(LEAN_EMSCRIPTEN)
    tid = 0;
#else
    // since Linux 2.4.11, our glibc 2.27 requires at least 3.2
    // glibc 2.30 would provide a wrapper
    tid = (pid_t)syscall(SYS_gettid);
#endif
    return lean_io_result_mk_ok(box_uint64(tid));
}

// opaque Child.wait {cfg : @& StdioConfig} : @& Child cfg → IO UInt32
extern "C" LEAN_EXPORT obj_res lean_io_process_child_wait(b_obj_arg, b_obj_arg child, obj_arg) {
    uv_process_t * h = static_cast<uv_process_t *>(lean_get_external_data(cnstr_get(child, 3)));
    object * promise = static_cast<object *>(h->data); // IO.Promise UInt32
    object * task = lean_io_promise_result_opt(promise); // Task (Option UInt32)
    object * result = lean_task_get(task); // Option UInt32
    dec(task);
    lean_always_assert(!lean_is_scalar(result));
    object * status = lean_ctor_get(result, 0); // UInt32
    inc(status);
    return lean_io_result_mk_ok(status);
}

// opaque Child.tryWait {cfg : @& StdioConfig} : @& Child cfg → IO (Option UInt32)
extern "C" LEAN_EXPORT obj_res lean_io_process_child_try_wait(b_obj_arg, b_obj_arg child, obj_arg) {
    uv_process_t * h = static_cast<uv_process_t *>(lean_get_external_data(cnstr_get(child, 3)));
    object * promise = static_cast<object *>(h->data); // IO.Promise UInt32
    object * task = lean_io_promise_result_opt(promise); // Task (Option UInt32)
    if (lean_io_get_task_state_core(task) == 2) {
        object * result = lean_task_get(task); // Option UInt32
        dec(task);
        lean_always_assert(!lean_is_scalar(result));
        inc(result);
        return lean_io_result_mk_ok(result);
    }
    dec(task);
    return io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_kill(b_obj_arg, b_obj_arg child, obj_arg) {
    uv_process_t * h = static_cast<uv_process_t *>(lean_get_external_data(cnstr_get(child, 3)));
    int error = uv_process_kill(h, SIGKILL);
    if (error != 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(error, nullptr));
    }
    return lean_io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_obj_arg, b_obj_arg child) {
    uv_process_t * h = static_cast<uv_process_t *>(lean_get_external_data(cnstr_get(child, 3)));
    return uv_process_get_pid(h);
}

static obj_res setup_stdio(uv_stdio_container_t * out, stdio cfg, int fd, int * pipe_other) {
    switch (cfg) {
    case stdio::INHERIT:
        out->flags = UV_INHERIT_FD;
        out->data.fd = fd;
        return box(0);
    case stdio::PIPED: {
        uv_file fds[2];
        lean_always_assert(uv_pipe(fds, 0, 0) == 0);

        out->flags = UV_INHERIT_FD;
        if (fd == STDIN_FILENO) {
            out->data.fd = fds[0];
            *pipe_other = fds[0];
            FILE * file = fdopen(fds[1], "w");
            return io_wrap_handle(file);
        } else {
            out->data.fd = fds[1];
            *pipe_other = fds[1];
            FILE * file = fdopen(fds[0], "r");
            return io_wrap_handle(file);
        }
    }
    case stdio::NUL:
        out->flags = UV_IGNORE;
        return box(0);
    }
    lean_unreachable();
}

static void process_exit_callback(uv_process_t * handle, int64_t exit_status, int term_signal) {
    object * promise = static_cast<object *>(handle->data);
    uint32_t status = (uint32_t) ((uint64_t) exit_status);
    lean_promise_resolve(box_uint32(status), promise);
}

static obj_res add_env_override(pair_ref<string_ref, option_ref<string_ref>> const & pair, uv_env_item_t * items, int & env_count) {
    auto & key = pair.fst();
    const char * key_str = key.data();
    if (strlen(key_str) != key.num_bytes()) {
        return mk_embedded_nul_error(key.raw());
    }
    if (strchr(key_str, '=') != NULL) {
        object * details = mk_string("environment variable name contains '='");
        return io_result_mk_error(lean_mk_io_error_invalid_argument_file(key.to_obj_arg(), EINVAL, details));
    }
    const char * val_str = nullptr;
    if (pair.snd()) {
        string_ref val = pair.snd().get_val();
        val_str = val.data();
        if (strlen(val_str) != val.num_bytes()) {
            return mk_embedded_nul_error(val.raw());
        }
    }
    int i = 0;
    while (i < env_count) {
        if (strcmp(key_str, items[i].name) == 0) {
            if (val_str != nullptr) {
                items[i].value = const_cast<char *>(val_str);
                return nullptr;
            } else {
                memmove(items + i, items + i + 1, sizeof(uv_env_item_t) * (env_count - i - 1));
                env_count--;
            }
        } else {
            i++;
        }
    }
    if (val_str != nullptr) {
        items[env_count].name = const_cast<char *>(key_str);
        items[env_count].value = const_cast<char *>(val_str);
        env_count++;
    }
    return nullptr;
}

static obj_res spawn(string_ref const & proc_name, array_ref<string_ref> const & args, stdio stdin_mode, stdio stdout_mode,
                     stdio stderr_mode, option_ref<string_ref> const & cwd, array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & env,
                     bool inherit_env, bool do_setsid) {
    const char * proc_name_str = proc_name.data();
    if (strlen(proc_name_str) != proc_name.num_bytes()) {
        return mk_embedded_nul_error(proc_name.raw());
    }
    char ** arg_array = (char **) malloc(sizeof(char *) * (args.size() + 2));
    arg_array[0] = const_cast<char *>(proc_name_str); // Is this safe?
    for (size_t i = 0; i < args.size(); i++) {
        auto & arg = args[i];
        const char * arg_str = arg.data();
        if (strlen(arg_str) != arg.num_bytes()) {
            free(arg_array);
            return mk_embedded_nul_error(arg.raw());
        }
        arg_array[i + 1] = const_cast<char *>(arg_str);
    }
    arg_array[args.size() + 1] = nullptr;

    // Opposite ends of the pipes; we need to close them
    int stdin_pipe_other, stdout_pipe_other, stderr_pipe_other;
    uv_stdio_container_t stdio[3];
    object * parent_stdin = setup_stdio(&stdio[0], stdin_mode, STDIN_FILENO, &stdin_pipe_other);
    object * parent_stdout = setup_stdio(&stdio[1], stdout_mode, STDOUT_FILENO, &stdout_pipe_other);
    object * parent_stderr = setup_stdio(&stdio[2], stderr_mode, STDERR_FILENO, &stderr_pipe_other);

    uv_process_options_t options = {0};
    options.file = proc_name_str;
    options.args = arg_array;
    if (cwd) {
        string_ref cwd_val = cwd.get_val();
        const char * cwd_str = cwd_val.data();
        if (strlen(cwd_str) != cwd_val.num_bytes()) {
            free(arg_array);
            return mk_embedded_nul_error(cwd_val.raw());
        }
        options.cwd = cwd_str;
    }
    if (do_setsid) {
        options.flags |= UV_PROCESS_DETACHED;
    }
    if (!inherit_env || env.size() != 0) {
        uv_env_item_t * items = nullptr;
        int env_base_count = 0;
        if (inherit_env) {
            uv_os_environ(&items, &env_base_count);
        }
        size_t env_alloc_count = env_base_count + env.size(); // maximum env size
        uv_env_item_t * env_vars = static_cast<uv_env_item_t *>(malloc(sizeof(uv_env_item_t) * env_alloc_count));
        memcpy(env_vars, items, env_base_count * sizeof(uv_env_item_t));

        int env_count = env_base_count;
        for (auto & pair : env) {
            object * error = add_env_override(pair, env_vars, env_count);
            if (error != nullptr) {
                uv_os_free_environ(items, env_base_count);
                free(arg_array);
                return error;
            }
        }
        size_t env_size = sizeof(char *) * (env_count + 1); // + terminating NUL pointer
        for (int i = 0; i < env_count; i++) {
            env_size += strlen(env_vars[i].name) + strlen(env_vars[i].value) + 2; // str1 + '=' + str2 + '\0'
        }
        void * env_arena = malloc(env_size);
        char ** env_strs = (char **) env_arena;
        char * env_str_off = (char *) env_arena + sizeof(char *) * (env_count + 1);
        for (int i = 0; i < env_count; i++) {
            env_strs[i] = env_str_off;

            size_t key_size = strlen(env_vars[i].name);
            size_t value_size = strlen(env_vars[i].value);
            memcpy(env_str_off, env_vars[i].name, key_size);
            env_str_off += key_size;
            *env_str_off++ = '=';
            memcpy(env_str_off, env_vars[i].value, value_size);
            env_str_off += value_size;
            *env_str_off++ = 0;
        }
        env_strs[env_count] = NULL;
        options.env = (char **) env_arena;
        if (inherit_env) {
            uv_os_free_environ(items, env_base_count);
        }
    }
    options.stdio_count = 3;
    options.stdio = stdio;
    options.exit_cb = &process_exit_callback;

    object * promise = lean_promise_new();
    mark_mt(promise);
    uv_process_t * child = (uv_process_t *) malloc(sizeof(uv_process_t));
    child->data = promise; // We use `.data` to store an `IO.Promise UInt32` that resolves on exit

    int error = uv_spawn(global_ev.loop, child, &options);

    free(arg_array);
    free(options.env);

    if (stdin_mode == stdio::PIPED) close(stdin_pipe_other);
    if (stdout_mode == stdio::PIPED) close(stdout_pipe_other);
    if (stderr_mode == stdio::PIPED) close(stderr_pipe_other);

    if (error != 0) {
        dec(promise);
        free(child);
        return lean_io_result_mk_error(decode_uv_error(error, proc_name.raw()));
    }
    object_ref r = mk_cnstr(0, parent_stdin, parent_stdout, parent_stderr, wrap_uv_handle(reinterpret_cast<uv_handle_t *>(child)));
    return lean_io_result_mk_ok(r.steal());
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_take_stdin(b_obj_arg, obj_arg lchild, obj_arg) {
    object_ref child(lchild);
    object_ref child2 = mk_cnstr(0, object_ref(box(0)), cnstr_get_ref(child, 1), cnstr_get_ref(child, 2), cnstr_get_ref(child, 3));
    object_ref r = mk_cnstr(0, cnstr_get_ref(child, 0), child2);
    return lean_io_result_mk_ok(r.steal());
}

extern "C" lean_object* lean_mk_io_error_other_error(uint32_t, lean_object*);

extern "C" LEAN_EXPORT obj_res lean_io_process_spawn(obj_arg args_, obj_arg) {
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
