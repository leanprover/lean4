/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include <iostream>

#if defined(LEAN_WINDOWS)
#include <windows.h>
#else
#include <unistd.h>
#include <limits.h> // NOLINT
#ifdef __APPLE__
#include <pthread.h>
#endif
#endif

#ifdef __linux
#include <sys/syscall.h>
#endif

#include "runtime/object.h"
#include "runtime/io.h"
#include "runtime/sstream.h" // `sstream`, used by the Windows helpers below

namespace lean {

#if defined(LEAN_WINDOWS)

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

#endif

void initialize_process() {}
void finalize_process() {}

}
