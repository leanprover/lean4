/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#include <climits>
#include <cstring>
#include <memory>
#include <new>
#include "runtime/uv/system.h"
#include "runtime/uv/util.h"

namespace lean {
#ifndef LEAN_EMSCRIPTEN

using namespace std;

// A `uv_random` request. The callback fills `byte_array` and deletes it, and so does a failed submit.
struct random_req_t {
    uv_random_t uv;
    owned_ref   promise;
    owned_ref   byte_array;
};

/* Std.Internal.UV.System.getProcessTitle : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_process_title() {
    char title[512];
    int result = uv_get_process_title(title, sizeof(title));
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    return lean_io_result_mk_ok(lean_mk_string(title));
}

/* Std.Internal.UV.System.setProcessTitle : @& String → IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_set_process_title(b_obj_arg title) {
    const char* title_str = lean_string_cstr(title);
    if (strlen(title_str) != lean_string_size(title) - 1) {
        return mk_embedded_nul_error(title);
    }
    int result = uv_set_process_title(title_str);
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.System.uptime : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_uptime() {
    double uptime;
    int result = uv_uptime(&uptime);
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)uptime));
}

/* Std.Internal.UV.System.osGetPid : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getpid() {
    return lean_io_result_mk_ok(lean_box_uint64(uv_os_getpid()));
}

/* Std.Internal.UV.System.osGetPpid : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getppid() {
    return lean_io_result_mk_ok(lean_box_uint64(uv_os_getppid()));
}

/* Std.Internal.UV.System.cpuInfo : IO (Array CPUInfo) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_cpu_info() {
    uv_cpu_info_t * infos;
    int count;
    int result = uv_cpu_info(&infos, &count);
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    uv_owned_array<uv_cpu_info_t, uv_free_cpu_info> cpus(infos, count);

    lean_object * lean_cpu_infos = lean_alloc_array(0, count);
    for (uv_cpu_info_t const & cpu : cpus) {
        lean_object* times = lean_alloc_ctor(0, 0, 40);
        lean_ctor_set_uint64(times, 0, cpu.cpu_times.user);
        lean_ctor_set_uint64(times, 8, cpu.cpu_times.nice);
        lean_ctor_set_uint64(times, 16, cpu.cpu_times.sys);
        lean_ctor_set_uint64(times, 24, cpu.cpu_times.idle);
        lean_ctor_set_uint64(times, 32, cpu.cpu_times.irq);

        lean_object* cpu_info = lean_alloc_ctor(0, 2, 8);
        lean_ctor_set(cpu_info, 0, lean_mk_string(cpu.model));
        lean_ctor_set(cpu_info, 1, times);
        lean_ctor_set_uint64(cpu_info, sizeof(void*)*2, (uint64_t)cpu.speed);

        lean_cpu_infos = lean_array_push(lean_cpu_infos, cpu_info);
    }
    return lean_io_result_mk_ok(lean_cpu_infos);
}

// Calls a libuv function that writes a string into a caller-provided buffer, retrying with the size it
// asks for when the buffer is too small.
static lean_obj_res get_uv_string(int (*get)(char *, size_t *)) {
    char stack_buffer[PATH_MAX];
    std::unique_ptr<char[]> heap_buffer;
    char * buffer = stack_buffer;
    size_t size = sizeof(stack_buffer);

    int result = get(buffer, &size);
    if (result == UV_ENOBUFS) {
        heap_buffer.reset(new (std::nothrow) char[size]);
        if (!heap_buffer) {
            return io_result_mk_enomem();
        }
        buffer = heap_buffer.get();
        result = get(buffer, &size);
    }
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    return lean_io_result_mk_ok(lean_mk_string_from_bytes(buffer, size));
}

/* Std.Internal.UV.System.cwd : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_cwd() {
    return get_uv_string(uv_cwd);
}

/* Std.Internal.UV.System.chdir : @& String → IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_chdir(b_obj_arg path) {
    const char* path_str = lean_string_cstr(path);
    if (strlen(path_str) != lean_string_size(path) - 1) {
        return mk_embedded_nul_error(path);
    }
    int result = uv_chdir(path_str);
    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, path));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.System.osHomedir : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_homedir() {
    return get_uv_string(uv_os_homedir);
}

/* Std.Internal.UV.System.osTmpdir : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_tmpdir() {
    return get_uv_string(uv_os_tmpdir);
}

/* Std.Internal.UV.System.osGetPasswd : IO PasswdInfo */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_passwd() {
    uv_passwd_t passwd;
    int result = uv_os_get_passwd(&passwd);
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    // Frees the strings `passwd` points to, not `passwd` itself.
    std::unique_ptr<uv_passwd_t, decltype(&uv_os_free_passwd)> passwd_strings(&passwd, uv_os_free_passwd);

    lean_object* passwd_info = lean_alloc_ctor(0, 5, 0);
    lean_ctor_set(passwd_info, 0, lean_mk_string(passwd.username));
    lean_ctor_set(passwd_info, 1, passwd.uid != (unsigned long)(-1) ? mk_option_some(lean_box_uint64(passwd.uid)) : mk_option_none());
    lean_ctor_set(passwd_info, 2, passwd.uid != (unsigned long)(-1) ? mk_option_some(lean_box_uint64(passwd.gid)) : mk_option_none());
    lean_ctor_set(passwd_info, 3, passwd.shell ? mk_option_some(lean_mk_string(passwd.shell)) : mk_option_none());
    lean_ctor_set(passwd_info, 4, passwd.homedir ? mk_option_some(lean_mk_string(passwd.homedir)) : mk_option_none());
    return lean_io_result_mk_ok(passwd_info);
}

/* Std.Internal.UV.System.osGetGroup : IO (Option GroupInfo) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_group(uint64_t gid) {
#if UV_VERSION_HEX >= 0x012D00
    uv_group_t group;
    int result = uv_os_get_group(&group, gid);
    if (result == UV_ENOENT) {
        return lean_io_result_mk_ok(mk_option_none());
    }
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    // Frees the strings `group` points to, not `group` itself.
    std::unique_ptr<uv_group_t, decltype(&uv_os_free_group)> group_strings(&group, uv_os_free_group);

    lean_object* members = lean_mk_empty_array();
    for (char ** member = group.members; member && *member != nullptr; member++) {
        members = lean_array_push(members, lean_mk_string(*member));
    }

    lean_object* group_info = lean_alloc_ctor(0, 2, 8);
    lean_ctor_set(group_info, 0, lean_mk_string(group.groupname));
    lean_ctor_set(group_info, 1, members);
    lean_ctor_set_uint64(group_info, sizeof(void*)*2, group.gid);
    return lean_io_result_mk_ok(mk_option_some(group_info));
#else
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv version at least 1.45.0 to invoke this.")
    );
#endif
}

/* Std.Internal.UV.System.osEnviron : IO (Array (String × String)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_environ() {
    uv_env_item_t * items;
    int count;
    int result = uv_os_environ(&items, &count);
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    uv_owned_array<uv_env_item_t, uv_os_free_environ> env(items, count);

    lean_object* env_array = lean_mk_empty_array();
    for (uv_env_item_t const & item : env) {
        lean_object* pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, lean_mk_string(item.name));
        lean_ctor_set(pair, 1, lean_mk_string(item.value));
        env_array = lean_array_push(env_array, pair);
    }
    return lean_io_result_mk_ok(env_array);
}

/* Std.Internal.UV.System.osGetenv : @& String → IO (Option String) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getenv(b_obj_arg name) {
    const char* name_str = lean_string_cstr(name);
    if (strlen(name_str) != lean_string_size(name) - 1) {
        return lean_io_result_mk_ok(mk_option_none());
    }
    char stack_buffer[1024];
    std::unique_ptr<char[]> heap_buffer;
    char * buffer = stack_buffer;
    size_t size = sizeof(stack_buffer);

    int result = uv_os_getenv(name_str, buffer, &size);
    if (result == UV_ENOBUFS) {
        heap_buffer.reset(new (std::nothrow) char[size]);
        if (!heap_buffer) {
            return io_result_mk_enomem();
        }
        buffer = heap_buffer.get();
        result = uv_os_getenv(name_str, buffer, &size);
    }
    if (result == UV_ENOENT) {
        return lean_io_result_mk_ok(mk_option_none());
    }
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    return lean_io_result_mk_ok(mk_option_some(lean_mk_string(buffer)));
}

/* Std.Internal.UV.System.osSetenv : @& String → @& String → IO Unit */
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
        return io_result_mk_uv_error(result);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.System.osUnsetenv : @& String → IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_unsetenv(b_obj_arg name) {
    const char* name_str = lean_string_cstr(name);
    if (strlen(name_str) != lean_string_size(name) - 1) {
        return mk_embedded_nul_error(name);
    }
    int result = uv_os_unsetenv(name_str);
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.System.osGetHostname : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_gethostname() {
    char hostname[256];
    size_t size = sizeof(hostname);
    int result = uv_os_gethostname(hostname, &size);
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    return lean_io_result_mk_ok(lean_mk_string(hostname));
}

/* Std.Internal.UV.System.osGetPriority : UInt64 → IO Int64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getpriority(uint64_t pid) {
    int priority;
    int result = uv_os_getpriority(pid, &priority);
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    return lean_io_result_mk_ok(lean_box_uint64(priority));
}

/* Std.Internal.UV.System.osSetPriority : UInt64 → Int64 → IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_setpriority(uint64_t pid, int64_t priority) {
    if (priority < INT_MIN || priority > INT_MAX) {
        return io_result_mk_uv_error(UV_EINVAL);
    }
    int result = uv_os_setpriority(pid, (int)priority);
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.System.osUname : IO UnameInfo */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_uname() {
    uv_utsname_t uname_info;
    int result = uv_os_uname(&uname_info);
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    lean_object* uname = lean_alloc_ctor(0, 4, 0);
    lean_ctor_set(uname, 0, lean_mk_string(uname_info.sysname));
    lean_ctor_set(uname, 1, lean_mk_string(uname_info.release));
    lean_ctor_set(uname, 2, lean_mk_string(uname_info.version));
    lean_ctor_set(uname, 3, lean_mk_string(uname_info.machine));
    return lean_io_result_mk_ok(uname);
}

/* Std.Internal.UV.System.hrtime : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_hrtime() {
    return lean_io_result_mk_ok(lean_box_uint64(uv_hrtime()));
}

/* Std.Internal.UV.System.random : UInt64 → IO (IO.Promise (Except IO.Error ByteArray)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_random(uint64_t size) {
    // libuv rejects larger requests with `UV_E2BIG`; checking first avoids allocating the array.
    if (size > 0x7FFFFFFF) {
        return io_result_mk_uv_error(UV_E2BIG);
    }

    random_req_t * req = new (std::nothrow) random_req_t;
    if (req == nullptr) {
        return io_result_mk_enomem();
    }
    req->uv.data = req;
    req->promise = owned_ref(mk_mt_promise());
    req->byte_array = owned_ref(lean_alloc_sarray(1, 0, size));
    owned_ref promise = owned_ref::retain(req->promise.get());

    auto on_random = [](uv_random_t * uv, int status, void * buf, size_t buflen) {
        std::unique_ptr<random_req_t> req(static_cast<random_req_t*>(uv->data));

        if (status < 0) {
            lean_promise_resolve(mk_except_err(lean_decode_uv_error(status, nullptr)), req->promise.get());
        } else {
            lean_sarray_set_size(req->byte_array.get(), buflen);
            lean_promise_resolve(mk_except_ok(req->byte_array.release()), req->promise.get());
        }
    };

    int result;
    {
        event_loop_guard guard;
        result = uv_random(global_ev.m_loop, &req->uv, lean_sarray_cptr(req->byte_array.get()), size, 0, on_random);
    }

    if (result < 0) {
        delete req;
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(promise.release());
}

static inline uint64_t timeval_to_millis(uv_timeval_t t) {
        return (uint64_t)t.tv_sec * 1000 + (uint64_t)t.tv_usec / 1000;
}

/* Std.Internal.UV.System.getrusage : IO RUsage */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_getrusage() {
    uv_rusage_t usage;
    int result = uv_getrusage(&usage);
    if (result < 0) {
        return io_result_mk_uv_error(result);
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

/* Std.Internal.UV.System.exePath : IO String */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_exepath() {
    char buffer[PATH_MAX];
    size_t size = sizeof(buffer);
    int result = uv_exepath(buffer, &size);
    if (result < 0) {
        return io_result_mk_uv_error(result);
    }
    return lean_io_result_mk_ok(lean_mk_string(buffer));
}

/* Std.Internal.UV.System.freeMemory : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_free_memory() {
    return lean_io_result_mk_ok(lean_box_uint64(uv_get_free_memory()));
}

/* Std.Internal.UV.System.totalMemory : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_total_memory() {
    return lean_io_result_mk_ok(lean_box_uint64(uv_get_total_memory()));
}

/* Std.Internal.UV.System.constrainedMemory : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_constrained_memory() {
    return lean_io_result_mk_ok(lean_box_uint64(uv_get_constrained_memory()));
}

/* Std.Internal.UV.System.availableMemory : IO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_available_memory() {
#if UV_VERSION_HEX >= 0x012D00
    return lean_io_result_mk_ok(lean_box_uint64(uv_get_available_memory()));
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
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_group(uint64_t gid) {
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

// Std.Internal.UV.System.osGetenv : @& String → IO (Option String)
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getenv(b_obj_arg name) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osSetenv : @& String → @& String → IO Unit
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_setenv(b_obj_arg name, b_obj_arg value) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// Std.Internal.UV.System.osUnsetenv : @& String → IO Unit
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

// Std.Internal.UV.System.osSetPriority : UInt64 → Int64 → IO Unit
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

// Std.Internal.UV.System.random : UInt64 → IO (IO.Promise (Except IO.Error ByteArray))
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
