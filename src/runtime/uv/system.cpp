/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#include <cstring>
#include "runtime/uv/system.h"

namespace lean {
#ifndef LEAN_EMSCRIPTEN

using namespace std;

// Stores all the things needed to request a random sequence of bytes.
typedef struct {
    uv_random_t req;
    lean_object* promise;
    lean_object* byte_array;
} random_req_t;

// Std.Internal.UV.System.getProcessTitle : IO String
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_process_title() {
    char title[512];
    int result = uv_get_process_title(title, sizeof(title));

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* lean_title = lean_mk_string(title);
    return lean_io_result_mk_ok(lean_title);
}

// Std.Internal.UV.System.setProcessTitle : String → IO Unit
extern "C" LEAN_EXPORT lean_obj_res lean_uv_set_process_title(b_obj_arg title) {
    const char* title_str = lean_string_cstr(title);
    if (strlen(title_str) != lean_string_size(title) - 1) {
        return mk_embedded_nul_error(title);
    }
    int result = uv_set_process_title(title_str);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

// Std.Internal.UV.System.uptime : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_uptime() {
    double uptime;

    int result = uv_uptime(&uptime);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* lean_uptime = lean_box_uint64((uint64_t)uptime);

    return lean_io_result_mk_ok(lean_uptime);
}

// Std.Internal.UV.System.osGetPid : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getpid() {
    uv_pid_t pid = uv_os_getpid();
    return lean_io_result_mk_ok(lean_box_uint64(pid));
}

// Std.Internal.UV.System.osGetPpid : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getppid() {
    uv_pid_t ppid = uv_os_getppid();
    return lean_io_result_mk_ok(lean_box_uint64(ppid));
}

// Std.Internal.UV.System.cpuInfo : IO (Array CPUInfo)
extern "C" LEAN_EXPORT lean_obj_res lean_uv_cpu_info() {
    uv_cpu_info_t* cpu_infos;
    int count;

    int result = uv_cpu_info(&cpu_infos, &count);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* lean_cpu_infos = lean_alloc_array(count, count);

    for (int i = 0; i < count; i++) {
        lean_object* times = lean_alloc_ctor(0, 0, 40);
        lean_ctor_set_uint64(times, 0, cpu_infos[i].cpu_times.user);
        lean_ctor_set_uint64(times, 8, cpu_infos[i].cpu_times.nice);
        lean_ctor_set_uint64(times, 16, cpu_infos[i].cpu_times.sys);
        lean_ctor_set_uint64(times, 24, cpu_infos[i].cpu_times.idle);
        lean_ctor_set_uint64(times, 32, cpu_infos[i].cpu_times.irq);

        lean_object* model = lean_mk_string(cpu_infos[i].model);

        lean_object* cpu_info = lean_alloc_ctor(0, 2, 8);
        lean_ctor_set(cpu_info, 0, model);
        lean_ctor_set(cpu_info, 1, times);
        lean_ctor_set_uint64(cpu_info, sizeof(void*)*2, (uint64_t)cpu_infos[i].speed);

        lean_array_set_core(lean_cpu_infos, i, cpu_info);
    }

    uv_free_cpu_info(cpu_infos, count);

    return lean_io_result_mk_ok(lean_cpu_infos);
}

// Std.Internal.UV.System.cwd : IO String
extern "C" LEAN_EXPORT lean_obj_res lean_uv_cwd() {
    char buffer[PATH_MAX];
    size_t size = sizeof(buffer);

    int result = uv_cwd(buffer, &size);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* lean_cwd = lean_mk_string(buffer);
    return lean_io_result_mk_ok(lean_cwd);
}

// Std.Internal.UV.System.chdir : String → IO Unit
extern "C" LEAN_EXPORT lean_obj_res lean_uv_chdir(b_obj_arg path) {
    const char* path_str = lean_string_cstr(path);
    if (strlen(path_str) != lean_string_size(path) - 1) {
        return mk_embedded_nul_error(path);
    }

    int result = uv_chdir(path_str);

    if (result < 0) {
        lean_inc(path);
        return lean_io_result_mk_error(lean_decode_uv_error(result, path));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

// Std.Internal.UV.System.osHomedir : IO String
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_homedir() {
    char buffer[PATH_MAX];
    size_t size = sizeof(buffer);

    int result = uv_os_homedir(buffer, &size);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* lean_homedir = lean_mk_string(buffer);
    return lean_io_result_mk_ok(lean_homedir);
}

// Std.Internal.UV.System.osTmpdir : IO String
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_tmpdir() {
    char buffer[PATH_MAX];
    size_t size = sizeof(buffer);

    int result = uv_os_tmpdir(buffer, &size);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* lean_tmpdir = lean_mk_string(buffer);
    return lean_io_result_mk_ok(lean_tmpdir);
}

// Std.Internal.UV.System.osGetPasswd : IO PasswdInfo
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_passwd() {
    uv_passwd_t passwd;

    int result = uv_os_get_passwd(&passwd);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* username = lean_mk_string(passwd.username);
    lean_object* uid = passwd.uid != (unsigned long)(-1) ? mk_option_some(lean_box_uint64(passwd.uid)) : mk_option_none();
    lean_object* gid = passwd.uid != (unsigned long)(-1) ? mk_option_some(lean_box_uint64(passwd.gid)) : mk_option_none();
    lean_object* shell = passwd.shell ? mk_option_some(lean_mk_string(passwd.shell)) : mk_option_none();
    lean_object* homedir = passwd.homedir ? mk_option_some(lean_mk_string(passwd.homedir)) : mk_option_none();

    lean_object* passwd_info = lean_alloc_ctor(0, 5, 0);
    lean_ctor_set(passwd_info, 0, username);
    lean_ctor_set(passwd_info, 1, uid);
    lean_ctor_set(passwd_info, 2, gid);
    lean_ctor_set(passwd_info, 3, shell);
    lean_ctor_set(passwd_info, 4, homedir);

    uv_os_free_passwd(&passwd);

    return lean_io_result_mk_ok(passwd_info);
}

// Std.Internal.UV.System.osGetGroup : IO (Option GroupInfo)
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_group(uint64_t gid) {
#if UV_VERSION_HEX >= 0x012D00
    uv_group_t group;
    int result = uv_os_get_group(&group, gid);

    if (result == UV_ENOENT) {
        return lean_io_result_mk_ok(mk_option_none());
    }

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, lean_mk_string("group")));
    }

    lean_object* groupname = lean_mk_string(group.groupname);

    int count = 0;
    char** mem_ptr = group.members;
    while (mem_ptr && *mem_ptr != nullptr) {
        count++;
        mem_ptr++;
    }

    lean_object* members = lean_mk_empty_array();
    for (int i = 0; i < count; i++) {
        lean_object* member_name = lean_mk_string(group.members[i]);
        members = lean_array_push(members, member_name);
    }

    lean_object* group_info = lean_alloc_ctor(0, 2, 8);
    lean_ctor_set(group_info, 0, groupname);
    lean_ctor_set(group_info, 1, members);
    lean_ctor_set_uint64(group_info, sizeof(void*)*2, group.gid);

    uv_os_free_group(&group);

    return lean_io_result_mk_ok(mk_option_some(group_info));
#else
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv version at least 1.45.0 to invoke this.")
    );
#endif
}

// Std.Internal.UV.System.osEnviron : IO (Array (String × String))
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_environ() {
    uv_env_item_t* env;
    int count;
    int result = uv_os_environ(&env, &count);

    if (result < 0) {
        return lean_io_result_mk_error(lean_mk_string(uv_strerror(result)));
    }

    lean_object* env_array = lean_mk_empty_array();

    for (int i = 0; i < count; i++) {
        lean_object* name = lean_mk_string(env[i].name);
        lean_object* value = lean_mk_string(env[i].value);

        lean_object* pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, name);
        lean_ctor_set(pair, 1, value);

        env_array = lean_array_push(env_array, pair);
    }

    uv_os_free_environ(env, count);

    return lean_io_result_mk_ok(env_array);
}

// Std.Internal.UV.System.osGetenv : String → IO (Option String)
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getenv(b_obj_arg name) {
    const char* name_str = lean_string_cstr(name);
    if (strlen(name_str) != lean_string_size(name) - 1) {
        return lean_io_result_mk_ok(lean_box(0));
    }
    char stack_buffer[1024];
    size_t size = sizeof(stack_buffer);

    int result = uv_os_getenv(name_str, stack_buffer, &size);

    if (result == UV_ENOENT) {
        return lean_io_result_mk_ok(lean_box(0));
    } else if (result == UV_ENOBUFS) {
        char* heap_buffer = static_cast<char*>(malloc(size));

        result = uv_os_getenv(name_str, heap_buffer, &size);

        if (result == UV_ENOENT) {
            free(heap_buffer);
            return lean_io_result_mk_ok(lean_box(0));
        } else if (result < 0) {
            free(heap_buffer);
            return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
        }

        lean_object* value = lean_mk_string(heap_buffer);
        lean_object* some_value = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(some_value, 0, value);
        free(heap_buffer);
        return lean_io_result_mk_ok(some_value);
    } else if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* value = lean_mk_string(stack_buffer);
    lean_object* some_value = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some_value, 0, value);
    return lean_io_result_mk_ok(some_value);
}


// Std.Internal.UV.System.osSetenv : String → String → IO Unit
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_setenv(b_obj_arg name, b_obj_arg value) {
    const char* name_str = lean_string_cstr(name);
    const char* value_str = lean_string_cstr(value);
    if (strlen(name_str) != lean_string_size(name) - 1) {
        return mk_embedded_nul_error(name);
    }
    if (strlen(value_str) != lean_string_size(value) - 1) {
        return mk_embedded_nul_error(value);
    }

    int result = uv_os_setenv(name_str, value_str);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

// Std.Internal.UV.System.osUnsetenv : String → IO Unit
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_unsetenv(b_obj_arg name) {
    const char* name_str = lean_string_cstr(name);
    if (strlen(name_str) != lean_string_size(name) - 1) {
        return mk_embedded_nul_error(name);
    }

    int result = uv_os_unsetenv(name_str);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

// Std.Internal.UV.System.osGetHostname : IO String
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_gethostname() {
    char hostname[256];
    size_t size = sizeof(hostname);

    int result = uv_os_gethostname(hostname, &size);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* lean_hostname = lean_mk_string(hostname);
    return lean_io_result_mk_ok(lean_hostname);
}

// Std.Internal.UV.System.osGetPriority : UInt64 → IO Int64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getpriority(uint64_t pid) {
    int priority;

    int result = uv_os_getpriority(pid, &priority);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box_uint64(priority));
}

// Std.Internal.UV.System.osSetPriority : UInt64 → Int → IO Unit
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_setpriority(uint64_t pid, int64_t priority) {
    int result = uv_os_setpriority(pid, priority);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

// Std.Internal.UV.System.osUname : IO UnameInfo
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_uname() {
    uv_utsname_t uname_info;

    int result = uv_os_uname(&uname_info);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* sysname = lean_mk_string(uname_info.sysname);
    lean_object* release = lean_mk_string(uname_info.release);
    lean_object* version = lean_mk_string(uname_info.version);
    lean_object* machine = lean_mk_string(uname_info.machine);

    lean_object* uname = lean_alloc_ctor(0, 4, 0);
    lean_ctor_set(uname, 0, sysname);
    lean_ctor_set(uname, 1, release);
    lean_ctor_set(uname, 2, version);
    lean_ctor_set(uname, 3, machine);

    return lean_io_result_mk_ok(uname);
}

// Std.Internal.UV.System.hrtime : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_hrtime() {
    uint64_t time = uv_hrtime();
    return lean_io_result_mk_ok(lean_box_uint64(time));
}

// Std.Internal.UV.System.random : UInt64 → IO (IO.Promise (Except IO.Error (Array UInt8)))
extern "C" LEAN_EXPORT lean_obj_res lean_uv_random(uint64_t size) {
    lean_object* promise = lean_promise_new();
    mark_mt(promise);

    lean_object* byte_array = lean_alloc_sarray(1, 0, size);

    random_req_t* req = (random_req_t*)malloc(sizeof(random_req_t));
    req->promise = promise;
    req->byte_array = byte_array;

    req->req.data = req;

    lean_inc(promise);

    event_loop_lock(&global_ev);

    int result = uv_random(
        global_ev.loop,
        &req->req,
        lean_sarray_cptr(byte_array),
        size,
        0,
        [](uv_random_t* uv_req, int status, void* buf, size_t buflen) {
            random_req_t* req = (random_req_t*)uv_req;

            if (status < 0) {
                lean_dec(req->byte_array);
                lean_promise_resolve(mk_except_err(lean_decode_uv_error(status, nullptr)), req->promise);
            } else {
                lean_sarray_set_size(req->byte_array, buflen);
                lean_promise_resolve(mk_except_ok(req->byte_array), req->promise);
            }

            lean_dec(req->promise);
            free(req);
        }
    );

    event_loop_unlock(&global_ev);

    if (result < 0) {
        lean_dec(byte_array);
        lean_dec(promise);
        lean_dec(promise);
        free(req);

        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(promise);
}

static inline uint64_t timeval_to_millis(uv_timeval_t t) {
        return (uint64_t)t.tv_sec * 1000 + (uint64_t)t.tv_usec / 1000;
}

// Std.Internal.UV.System.getrusage : IO RUsage
extern "C" LEAN_EXPORT lean_obj_res lean_uv_getrusage() {
    uv_rusage_t usage;
    int result = uv_getrusage(&usage);
    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* r = lean_alloc_ctor(0, 0, 16 * sizeof(uint64_t));
    lean_ctor_set_uint64(r, 0 * sizeof(uint64_t), timeval_to_millis(usage.ru_utime));
    lean_ctor_set_uint64(r, 1 * sizeof(uint64_t), timeval_to_millis(usage.ru_stime));
    lean_ctor_set_uint64(r, 2 * sizeof(uint64_t), usage.ru_maxrss);
    lean_ctor_set_uint64(r, 3 * sizeof(uint64_t), usage.ru_ixrss);
    lean_ctor_set_uint64(r, 4 * sizeof(uint64_t), usage.ru_idrss);
    lean_ctor_set_uint64(r, 5 * sizeof(uint64_t), usage.ru_isrss);
    lean_ctor_set_uint64(r, 6 * sizeof(uint64_t), usage.ru_minflt);
    lean_ctor_set_uint64(r, 7 * sizeof(uint64_t), usage.ru_majflt);
    lean_ctor_set_uint64(r, 8 * sizeof(uint64_t), usage.ru_nswap);
    lean_ctor_set_uint64(r, 9 * sizeof(uint64_t), usage.ru_inblock);
    lean_ctor_set_uint64(r, 10 * sizeof(uint64_t), usage.ru_oublock);
    lean_ctor_set_uint64(r, 11 * sizeof(uint64_t), usage.ru_msgsnd);
    lean_ctor_set_uint64(r, 12 * sizeof(uint64_t), usage.ru_msgrcv);
    lean_ctor_set_uint64(r, 13 * sizeof(uint64_t), usage.ru_nsignals);
    lean_ctor_set_uint64(r, 14 * sizeof(uint64_t), usage.ru_nvcsw);
    lean_ctor_set_uint64(r, 15 * sizeof(uint64_t), usage.ru_nivcsw);

    return lean_io_result_mk_ok(r);
}

// Std.Internal.UV.System.exePath : IO String
extern "C" LEAN_EXPORT lean_obj_res lean_uv_exepath() {
    char buffer[PATH_MAX];
    size_t size = sizeof(buffer);

    int result = uv_exepath(buffer, &size);
    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* path = lean_mk_string(buffer);
    return lean_io_result_mk_ok(path);
}

// Std.Internal.UV.System.freeMemory : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_free_memory() {
    uint64_t mem = uv_get_free_memory();
    return lean_io_result_mk_ok(lean_box_uint64(mem));
}

// Std.Internal.UV.System.totalMemory : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_total_memory() {
    uint64_t mem = uv_get_total_memory();
    return lean_io_result_mk_ok(lean_box_uint64(mem));
}

// Std.Internal.UV.System.constrainedMemory : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_constrained_memory() {
    uint64_t mem = uv_get_constrained_memory();
    return lean_io_result_mk_ok(lean_box_uint64(mem));
}

// Std.Internal.UV.System.availableMemory : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_available_memory() {
#if UV_VERSION_HEX >= 0x012D00
    uint64_t mem = uv_get_available_memory();
    return lean_io_result_mk_ok(lean_box_uint64(mem));
#else
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv version at least 1.45.0 to invoke this.")
    );
#endif
}

#else

// Std.Internal.UV.System.getProcessTitle : IO String
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_process_title() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.setProcessTitle : @& String → IO Unit
extern "C" LEAN_EXPORT lean_obj_res lean_uv_set_process_title(b_obj_arg title) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.uptime : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_uptime() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osGetPid : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getpid() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osGetPpid : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getppid() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.cpuInfo : IO (Array CPUInfo)
extern "C" LEAN_EXPORT lean_obj_res lean_uv_cpu_info() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.cwd : IO String
extern "C" LEAN_EXPORT lean_obj_res lean_uv_cwd() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.chdir : String → IO Unit
extern "C" LEAN_EXPORT lean_obj_res lean_uv_chdir(b_obj_arg path) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osHomedir : IO String
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_homedir() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osTmpdir : IO String
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_tmpdir() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osGetPasswd : IO PasswdInfo
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_passwd() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osGetGroup : IO (Option GroupInfo)
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_group() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osEnviron : IO (Array (String × String))
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_environ() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osGetenv : String → IO (Option String)
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getenv(b_obj_arg name) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osSetenv : String → String → IO Unit
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_setenv(b_obj_arg name, b_obj_arg value) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osUnsetenv : String → IO Unit
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_unsetenv(b_obj_arg name) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osGetHostname : IO String
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_gethostname() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osGetPriority : UInt64 → IO Int
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getpriority(uint64_t pid) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osSetPriority : UInt64 → Int → IO Unit
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_setpriority(uint64_t pid, int64_t priority) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osUname : IO UnameInfo
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_uname() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.hrtime : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_hrtime() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.random : UInt64 → IO (IO.Promise (Except IO.Error (Array UInt8)))
extern "C" LEAN_EXPORT lean_obj_res lean_uv_random(uint64_t size) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.getrusage : IO RUsage
extern "C" LEAN_EXPORT lean_obj_res lean_uv_getrusage() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}
// Std.Internal.UV.System.exePath : IO String
extern "C" LEAN_EXPORT lean_obj_res lean_uv_exepath() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}
// Std.Internal.UV.System.freeMemory : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_free_memory() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}
// Std.Internal.UV.System.totalMemory : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_total_memory() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}
// Std.Internal.UV.System.constrainedMemory : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_constrained_memory() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}
// Std.Internal.UV.System.availableMemory : IO UInt64
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_available_memory() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

#endif
}
