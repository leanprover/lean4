/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#if defined(LEAN_WINDOWS)
#include <icu.h>
#include <windows.h>
#include <io.h>
#define NOMINMAX // prevent ntdef.h from defining min/max macros
#include <ntdef.h>
#include <bcrypt.h>
#elif defined(__APPLE__)
#include <mach-o/dyld.h>
#include <unistd.h>
#else
#if defined(LEAN_EMSCRIPTEN)
#include <emscripten.h>
#endif
// Linux include files
#include <unistd.h> // NOLINT
#include <sys/mman.h>
#include <sys/file.h>
#ifndef LEAN_EMSCRIPTEN
#include <sys/random.h>
#endif
#endif
#ifndef LEAN_WINDOWS
#include <csignal>
#endif
#include <dirent.h>
#include <fcntl.h>
#include <iostream>
#include <chrono>
#include <sstream>
#include <fstream>
#include <iomanip>
#include <string>
#include <cstdlib>
#include <cctype>
#include <sys/stat.h>
#include <uv.h>
#include "util/io.h"
#include "runtime/alloc.h"
#include "runtime/io.h"
#include "runtime/utf8.h"
#include "runtime/object.h"
#include "runtime/thread.h"
#include "runtime/allocprof.h"
#include "runtime/option_ref.h"

#ifdef _MSC_VER
#define S_ISDIR(mode) ((mode & _S_IFDIR) != 0)
#else
#include <dirent.h>
#endif

namespace lean {

extern "C" LEAN_EXPORT void lean_io_result_show_error(b_obj_arg r) {
    object * err = io_result_get_error(r);
    inc_ref(err);
    object * str = lean_io_error_to_string(err);
    std::cerr << "uncaught exception: " << string_cstr(str) << std::endl;
    dec_ref(str);
}

obj_res io_result_mk_error(char const * msg) {
    return io_result_mk_error(lean_mk_io_user_error(mk_string(msg)));
}

obj_res io_result_mk_error(std::string const & msg) {
    return io_result_mk_error(lean_mk_io_user_error(mk_string(msg)));
}

static bool g_initializing = true;
extern "C" LEAN_EXPORT void lean_io_mark_end_initialization() {
    g_initializing = false;
}
extern "C" LEAN_EXPORT obj_res lean_io_initializing(obj_arg) {
    return io_result_mk_ok(box(g_initializing));
}

static obj_res mk_file_not_found_error(b_obj_arg fname) {
    inc(fname);
    int errnum = ENOENT;
    object * details = mk_string("");
    return io_result_mk_error(lean_mk_io_error_no_file_or_directory(fname, errnum, details));
}

static lean_external_class * g_io_handle_external_class = nullptr;

static void io_handle_finalizer(void * h) {
    // There is no sensible way to handle errors here; in particular, we should
    // not panic as finalizing a handle that already is in an invalid state
    // (broken pipe etc.) should work and not terminate the process. The same
    // decision was made for `std::fs::File` in the Rust stdlib.
    fclose(static_cast<FILE *>(h));
}

static void io_handle_foreach(void * /* mod */, b_obj_arg /* fn */) {
}

lean_object * io_wrap_handle(FILE *hfile) {
    return lean_alloc_external(g_io_handle_external_class, hfile);
}

extern "C" obj_res lean_stream_of_handle(obj_arg h);

static object * g_stream_stdin  = nullptr;
static object * g_stream_stdout = nullptr;
static object * g_stream_stderr = nullptr;
MK_THREAD_LOCAL_GET(object_ref, get_stream_current_stdin,  g_stream_stdin);
MK_THREAD_LOCAL_GET(object_ref, get_stream_current_stdout, g_stream_stdout);
MK_THREAD_LOCAL_GET(object_ref, get_stream_current_stderr, g_stream_stderr);

/* getStdin : BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_stdin(obj_arg /* w */) {
    return io_result_mk_ok(get_stream_current_stdin().to_obj_arg());
}

/* getStdout : BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_stdout(obj_arg /* w */) {
    return io_result_mk_ok(get_stream_current_stdout().to_obj_arg());
}

/* getStderr : BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_stderr(obj_arg /* w */) {
    return io_result_mk_ok(get_stream_current_stderr().to_obj_arg());
}

/* setStdin  : FS.Stream -> BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_set_stdin(obj_arg h, obj_arg /* w */) {
    object_ref & x = get_stream_current_stdin();
    object * r = x.steal();
    x = object_ref(h);
    return io_result_mk_ok(r);
}

/* setStdout  : FS.Stream -> BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_set_stdout(obj_arg h, obj_arg /* w */) {
    object_ref & x = get_stream_current_stdout();
    object * r = x.steal();
    x = object_ref(h);
    return io_result_mk_ok(r);
}

/* setStderr  : FS.Stream -> BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_set_stderr(obj_arg h, obj_arg /* w */) {
    object_ref & x = get_stream_current_stderr();
    object * r = x.steal();
    x = object_ref(h);
    return io_result_mk_ok(r);
}

static FILE * io_get_handle(lean_object * hfile) {
    return static_cast<FILE *>(lean_get_external_data(hfile));
}

extern "C" LEAN_EXPORT obj_res lean_decode_io_error(int errnum, b_obj_arg fname) {
    object * details = mk_string(strerror(errnum));
    // Keep in sync with lean_decode_uv_error below
    switch (errnum) {
    case EINTR:
        lean_assert(fname != nullptr);
        inc_ref(fname);
        return lean_mk_io_error_interrupted(fname, errnum, details);
    case ELOOP: case ENAMETOOLONG: case EDESTADDRREQ:
    case EBADF: case EDOM: case EINVAL: case EILSEQ:
    case ENOEXEC: case ENOSTR: case ENOTCONN:
    case ENOTSOCK:
        if (fname == nullptr) {
            return lean_mk_io_error_invalid_argument(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_invalid_argument_file(fname, errnum, details);
        }
    case ENOENT:
        lean_assert(fname != nullptr);
        inc_ref(fname);
        return lean_mk_io_error_no_file_or_directory(fname, errnum, details);
    case EACCES: case EROFS: case ECONNABORTED: case EFBIG:
    case EPERM:
        if (fname == nullptr) {
            return lean_mk_io_error_permission_denied(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_permission_denied_file(fname, errnum, details);
        }
    case EMFILE: case ENFILE: case ENOSPC:
    case E2BIG:  case EAGAIN: case EMLINK:
    case EMSGSIZE: case ENOBUFS: case ENOLCK:
    case ENOMEM: case ENOSR:
        if (fname == nullptr) {
            return lean_mk_io_error_resource_exhausted(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_resource_exhausted_file(fname, errnum, details);
        }
    case EISDIR: case EBADMSG: case ENOTDIR:
        if (fname == nullptr) {
            return lean_mk_io_error_inappropriate_type(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_inappropriate_type_file(fname, errnum, details);
        }
    case ENXIO: case EHOSTUNREACH: case ENETUNREACH:
    case ECHILD: case ECONNREFUSED: case ENODATA:
    case ENOMSG: case ESRCH:
        if (fname == nullptr) {
            return lean_mk_io_error_no_such_thing(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_no_such_thing_file(fname, errnum, details);
        }
    case EEXIST: case EINPROGRESS: case EISCONN:
        if (fname == nullptr) {
            return lean_mk_io_error_already_exists(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_already_exists_file(fname, errnum, details);
        }
    case EIO:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_hardware_fault(errnum, details);
    case ENOTEMPTY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_unsatisfied_constraints(errnum, details);
    case ENOTTY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_illegal_operation(errnum, details);
    case ECONNRESET: case EIDRM: case ENETDOWN: case ENETRESET:
    case ENOLINK: case EPIPE:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_resource_vanished(errnum, details);
    case EPROTO: case EPROTONOSUPPORT: case EPROTOTYPE:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_protocol_error(errnum, details);
    case ETIME: case ETIMEDOUT:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_time_expired(errnum, details);
    case EADDRINUSE: case EBUSY: case EDEADLK: case ETXTBSY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_resource_busy(errnum, details);
    case EADDRNOTAVAIL: case EAFNOSUPPORT: case ENODEV:
    case ENOPROTOOPT: case ENOSYS: case EOPNOTSUPP:
    case ERANGE: case ESPIPE: case EXDEV:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_unsupported_operation(errnum, details);
    case EFAULT:
    default:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_other_error(errnum, details);
    }
}

extern "C" LEAN_EXPORT obj_res lean_decode_uv_error(int errnum, b_obj_arg fname) {
    object * details = mk_string(uv_strerror(errnum));
    // Keep in sync with lean_decode_io_error above
    switch (errnum) {
    case UV_EINTR:
        lean_assert(fname != nullptr);
        inc_ref(fname);
        return lean_mk_io_error_interrupted(fname, errnum, details);
    /* LibUV does not map EDOM, ENOEXEC and ENOSTR as of version 1.48.0 */
    case UV_ELOOP: case UV_ENAMETOOLONG: case UV_EDESTADDRREQ:
    case UV_EBADF: case UV_EINVAL: case UV_EILSEQ:
    case UV_ENOTCONN: case UV_ENOTSOCK:
        if (fname == nullptr) {
            return lean_mk_io_error_invalid_argument(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_invalid_argument_file(fname, errnum, details);
        }
    case UV_ENOENT:
        lean_assert(fname != nullptr);
        inc_ref(fname);
        return lean_mk_io_error_no_file_or_directory(fname, errnum, details);
    case UV_EACCES: case UV_EROFS: case UV_ECONNABORTED: case UV_EFBIG:
    case UV_EPERM:
        if (fname == nullptr) {
            return lean_mk_io_error_permission_denied(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_permission_denied_file(fname, errnum, details);
        }
    /* LibUV does not map ENOLCK and ENOSR as of version 1.48.0 */
    case UV_EMFILE: case UV_ENFILE: case UV_ENOSPC:
    case UV_E2BIG:  case UV_EAGAIN: case UV_EMLINK:
    case UV_EMSGSIZE: case UV_ENOBUFS:
    case UV_ENOMEM:
        if (fname == nullptr) {
            return lean_mk_io_error_resource_exhausted(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_resource_exhausted_file(fname, errnum, details);
        }
    /* LibUV does not map EBADMSG as of version 1.48.0 */
    case UV_EISDIR: case UV_ENOTDIR:
        if (fname == nullptr) {
            return lean_mk_io_error_inappropriate_type(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_inappropriate_type_file(fname, errnum, details);
        }
    /* LibUV does not map ECHILD as of version 1.48.0 */
    case UV_ENXIO: case UV_EHOSTUNREACH: case UV_ENETUNREACH:
    case UV_ECONNREFUSED:
#if UV_VERSION_HEX >= 0x014500
    case UV_ENODATA:
#endif
    case UV_ESRCH:
        if (fname == nullptr) {
            return lean_mk_io_error_no_such_thing(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_no_such_thing_file(fname, errnum, details);
        }
    /* LibUV does not map EINPROGRESS as of version 1.48.0 */
    case UV_EEXIST: case UV_EISCONN:
        if (fname == nullptr) {
            return lean_mk_io_error_already_exists(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_already_exists_file(fname, errnum, details);
        }
    case UV_EIO:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_hardware_fault(errnum, details);
    case UV_ENOTEMPTY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_unsatisfied_constraints(errnum, details);
    case UV_ENOTTY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_illegal_operation(errnum, details);
    /* LibUV does not map EIDRM, ENETRESET and ENOLINK as of version 1.48.0 */
    case UV_ECONNRESET: case UV_ENETDOWN:
    case UV_EPIPE:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_resource_vanished(errnum, details);
    case UV_EPROTO: case UV_EPROTONOSUPPORT: case UV_EPROTOTYPE:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_protocol_error(errnum, details);
    /* LibUV does not map ETIME as of version 1.48.0 */
    case UV_ETIMEDOUT:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_time_expired(errnum, details);
    /* LibUV does not map EDEADLK as of version 1.48.0 */
    case UV_EADDRINUSE: case UV_EBUSY: case UV_ETXTBSY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_resource_busy(errnum, details);
    case UV_EADDRNOTAVAIL: case UV_EAFNOSUPPORT: case UV_ENODEV:
    case UV_ENOPROTOOPT: case UV_ENOSYS: case UV_ENOTSUP:
    case UV_ERANGE: case UV_ESPIPE: case UV_EXDEV:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_unsupported_operation(errnum, details);
    case UV_EFAULT:
    default:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_other_error(errnum, details);
    }
}

/* IO.setAccessRights (filename : @& String) (mode : UInt32) : IO Handle */
extern "C" LEAN_EXPORT obj_res lean_chmod (b_obj_arg filename, uint32_t mode, obj_arg /* w */) {
    if (!chmod(lean_string_cstr(filename), mode)) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(decode_io_error(errno, filename));
    }
}

/* Handle.mk (filename : @& String) (mode : FS.Mode) : IO Handle */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_mk(b_obj_arg filename, uint8 mode, obj_arg /* w */) {
    int flags = 0;
#ifdef LEAN_WINDOWS
    // do not translate line endings
    flags |= O_BINARY;
    // do not inherit across process creation
    flags |= O_NOINHERIT;
#else
    // do not inherit across process creation
    flags |= O_CLOEXEC;
#endif
    switch (mode) {
    case 0: flags |= O_RDONLY; break;  // read
    case 1: flags |= O_WRONLY | O_CREAT | O_TRUNC; break;  // write
    case 2: flags |= O_WRONLY | O_CREAT | O_TRUNC | O_EXCL; break;  // writeNew
    case 3: flags |= O_RDWR; break;  // readWrite
    case 4: flags |= O_WRONLY | O_CREAT | O_APPEND; break;  // append
    }
    int fd = open(lean_string_cstr(filename), flags, 0666);
    if (fd == -1) {
        return io_result_mk_error(decode_io_error(errno, filename));
    }
    char const * fp_mode;
    switch (mode) {
    case 0: fp_mode = "r"; break;  // read
    case 1: fp_mode = "w"; break;  // write
    case 2: fp_mode = "w"; break;  // writeNew
    case 3: fp_mode = "r+"; break;  // readWrite
    case 4: fp_mode = "a"; break;  // append
    }
    FILE * fp = fdopen(fd, fp_mode);
    if (!fp) {
        return io_result_mk_error(decode_io_error(errno, filename));
    } else {
        return io_result_mk_ok(io_wrap_handle(fp));
    }
}

#ifdef LEAN_WINDOWS

static inline HANDLE win_handle(FILE * fp) {
    return (HANDLE)_get_osfhandle(_fileno(fp));
}

/* Handle.lock : (@& Handle) → (exclusive : Bool) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_lock(b_obj_arg h, uint8_t x, obj_arg /* w */) {
    OVERLAPPED o = {0};
    HANDLE wh = win_handle(io_get_handle(h));
    DWORD flags = x ? LOCKFILE_EXCLUSIVE_LOCK : 0;
    if (LockFileEx(wh, flags, 0, MAXDWORD, MAXDWORD, &o)) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error((sstream() << GetLastError()).str());
    }
}

/* Handle.tryLock : (@& Handle) → (exclusive : Bool) → IO Bool */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_try_lock(b_obj_arg h, uint8_t x, obj_arg /* w */) {
    OVERLAPPED o = {0};
    HANDLE wh = win_handle(io_get_handle(h));
    DWORD flags = (x ? LOCKFILE_EXCLUSIVE_LOCK : 0) | LOCKFILE_FAIL_IMMEDIATELY;
    if (LockFileEx(wh, flags, 0, MAXDWORD, MAXDWORD, &o)) {
        return io_result_mk_ok(box(1));
    } else {
        if (GetLastError() == ERROR_LOCK_VIOLATION) {
            return io_result_mk_ok(box(0));
        } else {
            return io_result_mk_error((sstream() << GetLastError()).str());
        }
    }
}

/* Handle.unlock : (@& Handle) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_unlock(b_obj_arg h, obj_arg /* w */) {
    OVERLAPPED o = {0};
    HANDLE wh = win_handle(io_get_handle(h));
    if (UnlockFileEx(wh, 0, MAXDWORD, MAXDWORD, &o)) {
        return io_result_mk_ok(box(0));
    } else {
        if (GetLastError() == ERROR_NOT_LOCKED) {
            // For consistency with Unix
            return io_result_mk_ok(box(0));
        } else {
            return io_result_mk_error((sstream() << GetLastError()).str());
        }
    }
}

#else

/* Handle.lock : (@& Handle) → (exclusive : Bool) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_lock(b_obj_arg h,  uint8_t x, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    if (!flock(fileno(fp), x ? LOCK_EX : LOCK_SH)) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
}

/* Handle.tryLock : (@& Handle) → (exclusive : Bool) → IO Bool */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_try_lock(b_obj_arg h, uint8_t x, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    if (!flock(fileno(fp), (x ? LOCK_EX : LOCK_SH) | LOCK_NB)) {
        return io_result_mk_ok(box(1));
    } else {
        if (errno == EWOULDBLOCK) {
            return io_result_mk_ok(box(0));
        } else {
            return io_result_mk_error(decode_io_error(errno, nullptr));
        }
    }
}

/* Handle.unlock : (@& Handle) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_unlock(b_obj_arg h, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    if (!flock(fileno(fp), LOCK_UN)) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
}

#endif

/* Handle.isTty : (@& Handle) → BaseIO Bool */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_is_tty(b_obj_arg h, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
#ifdef LEAN_WINDOWS
    /*
    On Windows, there are two approaches for detecting a console.
    1)  _isatty(_fileno(fp)) != 0
        This checks whether the file descriptor is a *character device*,
        not just a terminal (unlike Unix's isatty). Thus, it produces a false
        positive in some edge cases (such as NUL).
        https://stackoverflow.com/q/3648711
    2)  GetConsoleMode(win_handle(fp), &mode) != 0
        Errors if the handle is not a console. Unfortunately, this produces
        a false negative for a terminal emulator like MSYS/Cygwin's Mintty,
        which is not implemented as a Windows-recognized console on
        old Windows versions (e.g., pre-Windows 10, pre-ConPTY).
        https://github.com/msys2/MINGW-packages/issues/14087
    We choose to use GetConsoleMode as that seems like the more modern approach,
    and Lean does not support pre-Windows 10.
    */
    DWORD mode;
    return io_result_mk_ok(box(GetConsoleMode(win_handle(fp), &mode) != 0));
#else
    // We ignore errors for consistency with Windows.
    return io_result_mk_ok(box(isatty(fileno(fp))));
#endif
}

/* Handle.isEof : (@& Handle) → BaseIO Bool */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_is_eof(b_obj_arg h, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    return io_result_mk_ok(box(std::feof(fp) != 0));
}

/* Handle.flush : (@& Handle) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_flush(b_obj_arg h, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    if (!std::fflush(fp)) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
}

/* Handle.rewind : (@& Handle) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_rewind(b_obj_arg h, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    if (!std::fseek(fp, 0, SEEK_SET)) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
}

/* Handle.truncate : (@& Handle) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_truncate(b_obj_arg h, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
#ifdef LEAN_WINDOWS
    if (!_chsize_s(_fileno(fp), _ftelli64(fp))) {
#else
    if (!ftruncate(fileno(fp), ftello(fp))) {
#endif
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
}

/* Handle.read : (@& Handle) → USize → IO ByteArray */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_read(b_obj_arg h, usize nbytes, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    obj_res res = lean_alloc_sarray(1, 0, nbytes);
    usize n = std::fread(lean_sarray_cptr(res), 1, nbytes, fp);
    if (n > 0) {
        lean_sarray_set_size(res, n);
        return io_result_mk_ok(res);
    } else if (feof(fp)) {
        clearerr(fp);
        lean_sarray_set_size(res, n);
        return io_result_mk_ok(res);
    } else {
        dec_ref(res);
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
}

/* Handle.write : (@& Handle) → (@& ByteArray) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_write(b_obj_arg h, b_obj_arg buf, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    usize n = lean_sarray_size(buf);
    usize m = std::fwrite(lean_sarray_cptr(buf), 1, n, fp);
    if (m == n) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
}

/* Handle.getLine : (@& Handle) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_get_line(b_obj_arg h, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);

    std::string result;
    int c; // Note: int, not char, required to handle EOF
    while ((c = std::fgetc(fp)) != EOF) {
        result.push_back(c);
        if (c == '\n') {
            break;
        }
    }

    if (std::ferror(fp)) {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    } else if (std::feof(fp)) {
        clearerr(fp);
        return io_result_mk_ok(mk_string(result));
    } else {
        obj_res ret = io_result_mk_ok(mk_string(result));
        return ret;
    }
}

/* Handle.putStr : (@& Handle) → (@& String) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_put_str(b_obj_arg h, b_obj_arg s, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    usize n = lean_string_size(s) - 1; // - 1 to ignore the terminal NULL byte.
    usize m = std::fwrite(lean_string_cstr(s), 1, n, fp);
    if (m == n) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
}

/* Std.Time.Timestamp.now : IO Timestamp */
extern "C" LEAN_EXPORT obj_res lean_get_current_time(obj_arg /* w */) {
    using namespace std::chrono;

    std::chrono::system_clock::time_point now = std::chrono::system_clock::now();
    long long timestamp = std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();

    long long secs = timestamp / 1000000000;
    long long nano = timestamp % 1000000000;

    lean_object *lean_ts = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(lean_ts, 0, lean_int64_to_int(secs));
    lean_ctor_set(lean_ts, 1, lean_int64_to_int(nano));

    return lean_io_result_mk_ok(lean_ts);
}

/* Std.Time.Database.Windows.getNextTransition : @&String -> Int64 -> Bool -> IO (Option (Int64 × TimeZone)) */
extern "C" LEAN_EXPORT obj_res lean_windows_get_next_transition(b_obj_arg timezone_str, uint64_t tm_obj, uint8 default_time, obj_arg /* w */) {
#if defined(LEAN_WINDOWS)
    UErrorCode status = U_ZERO_ERROR;
    const char* dst_name_id = lean_string_cstr(timezone_str);

    UChar tzID[256];
    u_strFromUTF8(tzID, sizeof(tzID) / sizeof(tzID[0]), NULL, dst_name_id, strlen(dst_name_id), &status);

    if (U_FAILURE(status)) {
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to read identifier")));
    }

    UCalendar *cal = ucal_open(tzID, -1, NULL, UCAL_GREGORIAN, &status);

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to open calendar")));
    }

    int64_t tm = 0;

    if (!default_time) {
        int64_t timestamp_secs = (int64_t)tm_obj;

        ucal_setMillis(cal, timestamp_secs * 1000, &status);
        if (U_FAILURE(status)) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to set calendar time")));
        }

        UDate nextTransition;
        if (!ucal_getTimeZoneTransitionDate(cal, UCAL_TZ_TRANSITION_NEXT, &nextTransition, &status)) {
            ucal_close(cal);
            return io_result_mk_ok(mk_option_none());
        }

        if (U_FAILURE(status)) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to get next transation")));
        }

        tm = (int64_t)(nextTransition / 1000.0);
    }

    int32_t dst_offset = ucal_get(cal, UCAL_DST_OFFSET, &status);

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to get dst_offset")));
    }

    int is_dst = dst_offset != 0;

    int32_t tzIDLength = ucal_getTimeZoneDisplayName(cal, is_dst ? UCAL_DST : UCAL_STANDARD, "en_US", tzID, 32, &status);

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to timezone identifier")));
    }

    char dst_name[256];
    int32_t dst_name_len;
    u_strToUTF8(dst_name, sizeof(dst_name), &dst_name_len, tzID, tzIDLength, &status);

    if (U_FAILURE(status)) {
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to convert DST name to UTF-8")));
    }

    UChar display_name[32];
    int32_t display_name_len = ucal_getTimeZoneDisplayName(cal, is_dst ? UCAL_SHORT_DST : UCAL_SHORT_STANDARD, "en_US", display_name, 32, &status);

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to read abbreaviation")));
    }

    char display_name_str[256];
    int32_t display_name_str_len;
    u_strToUTF8(display_name_str, sizeof(display_name_str), &display_name_str_len, display_name, display_name_len, &status);

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to get abbreviation to cstr")));
    }

    int32_t zone_offset = ucal_get(cal, UCAL_ZONE_OFFSET, &status);
    zone_offset += dst_offset;

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to get zone_offset")));
    }

    ucal_close(cal);

    int offset_seconds = zone_offset / 1000;

    lean_object *lean_tz = lean_alloc_ctor(0, 3, 1);
    lean_ctor_set(lean_tz, 0, lean_int_to_int(offset_seconds));
    lean_ctor_set(lean_tz, 1, lean_mk_string_from_bytes_unchecked(dst_name, dst_name_len));
    lean_ctor_set(lean_tz, 2, lean_mk_string_from_bytes_unchecked(display_name_str, display_name_str_len));
    lean_ctor_set_uint8(lean_tz, sizeof(void*)*3, is_dst);

    lean_object *lean_pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(lean_pair, 0, lean_box_uint64((uint64_t)tm));
    lean_ctor_set(lean_pair, 1, lean_tz);

    return lean_io_result_mk_ok(mk_option_some(lean_pair));
#else
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to get timezone, its windows only.")));
#endif
}

/* Std.Time.Database.Windows.getLocalTimeZoneIdentifierAt : Int64 → IO String */
extern "C" LEAN_EXPORT obj_res lean_get_windows_local_timezone_id_at(uint64_t tm_obj, obj_arg /* w */) {
#if defined(LEAN_WINDOWS)
    UErrorCode status = U_ZERO_ERROR;
    UCalendar* cal = ucal_open(NULL, -1, NULL, UCAL_GREGORIAN, &status);

    if (U_FAILURE(status)) {
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to open calendar")));
    }

    int64_t timestamp_secs = (int64_t)tm_obj;
    ucal_setMillis(cal, timestamp_secs * 1000, &status);

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to set calendar time")));
    }

    UChar tzId[256];
    int32_t tzIdLength = ucal_getTimeZoneID(cal, tzId, sizeof(tzId) / sizeof(tzId[0]), &status);
    ucal_close(cal);

    if (U_FAILURE(status)) {
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to get timezone ID")));
    }

    char tzIdStr[256];
    u_strToUTF8(tzIdStr, sizeof(tzIdStr), NULL, tzId, tzIdLength, &status);

    if (U_FAILURE(status)) {
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("failed to convert timezone ID to UTF-8")));
    }

    return lean_io_result_mk_ok(lean_mk_ascii_string_unchecked(tzIdStr));
#else
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("timezone retrieval is Windows-only")));
#endif
}

/* monoMsNow : BaseIO Nat */
extern "C" LEAN_EXPORT obj_res lean_io_mono_ms_now(obj_arg /* w */) {
    static_assert(sizeof(std::chrono::milliseconds::rep) <= sizeof(uint64), "size of std::chrono::nanoseconds::rep may not exceed 64");
    auto now = std::chrono::steady_clock::now();
    auto tm = std::chrono::duration_cast<std::chrono::milliseconds>(now.time_since_epoch());
    return io_result_mk_ok(uint64_to_nat(tm.count()));
}

/* monoNanosNow : BaseIO Nat */
extern "C" LEAN_EXPORT obj_res lean_io_mono_nanos_now(obj_arg /* w */) {
    static_assert(sizeof(std::chrono::nanoseconds::rep) <= sizeof(uint64), "size of std::chrono::nanoseconds::rep may not exceed 64");
    auto now = std::chrono::steady_clock::now();
    auto tm = std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch());
    return io_result_mk_ok(uint64_to_nat(tm.count()));
}

/* getRandomBytes (nBytes : USize) : IO ByteArray */
extern "C" LEAN_EXPORT obj_res lean_io_get_random_bytes (size_t nbytes, obj_arg /* w */) {
    // Adapted from https://github.com/rust-random/getrandom/blob/30308ae845b0bf3839e5a92120559eaf56048c28/src/

    if (nbytes == 0) return io_result_mk_ok(lean_alloc_sarray(1, 0, 0));

#if !defined(LEAN_WINDOWS)
    int fd_urandom = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
    if (fd_urandom < 0) {
        return io_result_mk_error(decode_io_error(errno, lean_mk_ascii_string_unchecked("/dev/urandom")));
    }
#endif

    obj_res res = lean_alloc_sarray(1, 0, nbytes);
    size_t remain = nbytes;
    uint8_t *dst = lean_sarray_cptr(res);

    while (remain > 0) {
#if defined(LEAN_WINDOWS)
        // Prevent ULONG (32-bit) overflow
        size_t read_sz = std::min(remain, static_cast<size_t>(std::numeric_limits<uint32_t>::max()));
        NTSTATUS status = BCryptGenRandom(
            NULL,
            dst,
            static_cast<ULONG>(read_sz),
            BCRYPT_USE_SYSTEM_PREFERRED_RNG
        );
        if (!NT_SUCCESS(status)) {
            dec_ref(res);
            return io_result_mk_error("BCryptGenRandom failed");
        }
        remain -= read_sz;
        dst += read_sz;
#else
    #if defined(LEAN_EMSCRIPTEN)
        // `Crypto.getRandomValues` documents `dest` should be at most 65536 bytes.
        size_t read_sz = std::min(remain, static_cast<size_t>(65536));
    #else
        size_t read_sz = remain;
    #endif
        ssize_t nread = read(fd_urandom, dst, read_sz);
        if (nread < 0) {
            if (errno != EINTR) {
                close(fd_urandom);
                dec_ref(res);
                return io_result_mk_error(decode_io_error(errno, nullptr));
            }
        } else {
            remain -= nread;
            dst += nread;
        }
#endif
    }

#if !defined(LEAN_WINDOWS)
    close(fd_urandom);
#endif
    lean_sarray_set_size(res, nbytes);
    return io_result_mk_ok(res);
}

/* timeit {α : Type} (msg : @& String) (fn : IO α) : IO α */
extern "C" LEAN_EXPORT obj_res lean_io_timeit(b_obj_arg msg, obj_arg fn, obj_arg w) {
    auto start = std::chrono::steady_clock::now();
    w = apply_1(fn, w);
    auto end   = std::chrono::steady_clock::now();
    auto diff  = std::chrono::duration<double>(end - start);
    sstream out;
    out << std::setprecision(3);
    if (diff < std::chrono::duration<double>(1)) {
        out << string_cstr(msg) << " " << std::chrono::duration<double, std::milli>(diff).count() << "ms";
    } else {
        out << string_cstr(msg) << " " << diff.count() << "s";
    }
    io_eprintln(mk_string(out.str()));
    return w;
}

/* allocprof {α : Type} (msg : @& String) (fn : IO α) : IO α */
extern "C" LEAN_EXPORT obj_res lean_io_allocprof(b_obj_arg msg, obj_arg fn, obj_arg w) {
    std::ostringstream out;
    obj_res res;
    {
        allocprof prof(out, string_cstr(msg));
        res = apply_1(fn, w);
    }
    io_eprintln(mk_string(out.str()));
    return res;
}

/* getNumHeartbeats : BaseIO Nat */
extern "C" LEAN_EXPORT obj_res lean_io_get_num_heartbeats(obj_arg /* w */) {
    return io_result_mk_ok(lean_uint64_to_nat(get_num_heartbeats()));
}

/* addHeartbeats (count : Int64) : BaseIO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_add_heartbeats(int64_t count, obj_arg /* w */) {
    add_heartbeats(count);
    return io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT obj_res lean_io_getenv(b_obj_arg env_var, obj_arg) {
#if defined(LEAN_EMSCRIPTEN)
    // HACK(WN): getenv doesn't seem to work in Emscripten even though it should
    // see https://emscripten.org/docs/porting/connecting_cpp_and_javascript/Interacting-with-code.html#interacting-with-code-environment-variables
    char* val = reinterpret_cast<char*>(EM_ASM_INT({
        var envVar = UTF8ToString($0);
        var val = ENV[envVar];
        if (val) {
            var lengthBytes = lengthBytesUTF8(val)+1;
            var valOnWasmHeap = _malloc(lengthBytes);
            stringToUTF8(val, valOnWasmHeap, lengthBytes);
            return valOnWasmHeap;
        } else {
            return 0;
        }
    }, string_cstr(env_var)));

    if (val) {
        object * valLean = mk_string(val);
        free(val);
        return io_result_mk_ok(mk_option_some(valLean));
    } else {
        return io_result_mk_ok(mk_option_none());
    }
#else
    char * val = std::getenv(string_cstr(env_var));
    if (val) {
        return io_result_mk_ok(mk_option_some(mk_string(val)));
    } else {
        return io_result_mk_ok(mk_option_none());
    }
#endif
}

extern "C" LEAN_EXPORT obj_res lean_io_realpath(obj_arg fname, obj_arg) {
#if defined(LEAN_WINDOWS)
    constexpr unsigned BufferSize = 8192;
    char buffer[BufferSize];
    DWORD retval = GetFullPathName(string_cstr(fname), BufferSize, buffer, nullptr);
    if (retval == 0 || retval > BufferSize) {
        return io_result_mk_ok(fname);
    } else {
        dec_ref(fname);
        // Hack for making sure disk is lower case
        // TODO(Leo): more robust solution
        if (strlen(buffer) >= 2 && buffer[1] == ':') {
            buffer[0] = tolower(buffer[0]);
        }
        return io_result_mk_ok(mk_string(buffer));
    }
#else
    char buffer[PATH_MAX];
    char * tmp = realpath(string_cstr(fname), buffer);
    if (tmp) {
        obj_res s = mk_string(tmp);
        dec_ref(fname);
        return io_result_mk_ok(s);
    } else {
        obj_res res = mk_file_not_found_error(fname);
        dec_ref(fname);
        return res;
    }
#endif
}

/*
structure DirEntry where
  root     : String
  filename : String

constant readDir : @& FilePath → IO (Array DirEntry)
*/
extern "C" LEAN_EXPORT obj_res lean_io_read_dir(b_obj_arg dirname, obj_arg) {
    object * arr = array_mk_empty();
    DIR * dp = opendir(string_cstr(dirname));
    if (!dp) {
        return io_result_mk_error(decode_io_error(errno, dirname));
    }
    while (dirent * entry = readdir(dp)) {
        if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) {
            continue;
        }
        object * lentry = alloc_cnstr(0, 2, 0);
        lean_inc(dirname);
        cnstr_set(lentry, 0, dirname);
        cnstr_set(lentry, 1, lean_mk_string(entry->d_name));
        arr = lean_array_push(arr, lentry);
    }
    lean_always_assert(closedir(dp) == 0);
    return io_result_mk_ok(arr);
}

/*
inductive FileType where
  | dir
  | file
  | symlink
  | other

structure SystemTime where
  sec  : Int
  nsec : UInt32

structure Metadata where
  --permissions : ...
  accessed : SystemTime
  modified : SystemTime
  byteSize : UInt64
  type     : FileType

constant metadata : @& FilePath → IO IO.FS.Metadata
*/
static obj_res timespec_to_obj(timespec const & ts) {
    object * o = alloc_cnstr(0, 1, sizeof(uint32));
    cnstr_set(o, 0, lean_int64_to_int(ts.tv_sec));
    cnstr_set_uint32(o, sizeof(object *), ts.tv_nsec);
    return o;
}

extern "C" LEAN_EXPORT obj_res lean_io_metadata(b_obj_arg fname, obj_arg) {
    struct stat st;
    if (stat(string_cstr(fname), &st) != 0) {
        return io_result_mk_error(decode_io_error(errno, fname));
    }
    object * mdata = alloc_cnstr(0, 2, sizeof(uint64) + sizeof(uint8));
#ifdef __APPLE__
    cnstr_set(mdata, 0, timespec_to_obj(st.st_atimespec));
    cnstr_set(mdata, 1, timespec_to_obj(st.st_mtimespec));
#elif defined(LEAN_WINDOWS)
    // TODO: sub-second precision on Windows
    cnstr_set(mdata, 0, timespec_to_obj(timespec { st.st_atime, 0 }));
    cnstr_set(mdata, 1, timespec_to_obj(timespec { st.st_mtime, 0 }));
#else
    cnstr_set(mdata, 0, timespec_to_obj(st.st_atim));
    cnstr_set(mdata, 1, timespec_to_obj(st.st_mtim));
#endif
    cnstr_set_uint64(mdata, 2 * sizeof(object *), st.st_size);
    cnstr_set_uint8(mdata, 2 * sizeof(object *) + sizeof(uint64),
                    S_ISDIR(st.st_mode) ? 0 :
                    S_ISREG(st.st_mode) ? 1 :
#ifndef LEAN_WINDOWS
                    S_ISLNK(st.st_mode) ? 2 :
#endif
                    3);
    return io_result_mk_ok(mdata);
}

extern "C" LEAN_EXPORT obj_res lean_io_create_dir(b_obj_arg p, obj_arg) {
#ifdef LEAN_WINDOWS
    if (mkdir(string_cstr(p)) == 0) {
#else
    if (mkdir(string_cstr(p), 0777) == 0) {
#endif
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(decode_io_error(errno, p));
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_remove_dir(b_obj_arg p, obj_arg) {
    if (rmdir(string_cstr(p)) == 0) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(decode_io_error(errno, p));
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_rename(b_obj_arg from, b_obj_arg to, lean_object * /* w */) {
#ifdef LEAN_WINDOWS
    // Note: On windows, std::rename gives an error if the `to` file already exists,
    // so we have to call the underlying windows API directly to get behavior consistent
    // with the unix-like OSs
    bool ok = MoveFileEx(string_cstr(from), string_cstr(to), MOVEFILE_REPLACE_EXISTING) != 0;
    if (!ok) {
        // TODO: actually produce the right type of IO error
        return io_result_mk_error((sstream()
            << "failed to rename '" << string_cstr(from) << "' to '" << string_cstr(to) << "': " << GetLastError()).str());
    }
#else
    bool ok = std::rename(string_cstr(from), string_cstr(to)) == 0;
    if (!ok) {
        std::ostringstream s;
        s << string_cstr(from) << " and/or " << string_cstr(to);
        object_ref out{mk_string(s.str())};
        return io_result_mk_error(decode_io_error(errno, out.raw()));
    }
#endif
    return io_result_mk_ok(box(0));
}

/* createTempFile : IO (Handle × FilePath) */
extern "C" LEAN_EXPORT obj_res lean_io_create_tempfile(lean_object * /* w */) {
    char path[PATH_MAX];
    size_t base_len = PATH_MAX;
    int ret = uv_os_tmpdir(path, &base_len);
    if (ret < 0) {
        return io_result_mk_error(decode_uv_error(ret, nullptr));
    } else if (base_len == 0) {
        return lean_io_result_mk_error(decode_uv_error(UV_ENOENT, mk_string("")));
    }

#if defined(LEAN_WINDOWS)
    // On Windows `GetTempPathW` always returns a path ending in \, but libuv removes it.
    // https://learn.microsoft.com/en-us/windows/win32/fileio/creating-and-using-a-temporary-file
    if (path[base_len - 1] != '\\') {
        lean_always_assert(PATH_MAX >= base_len + 1 + 1);
        strcat(path, "\\");
    }
#else
    // No guarantee that we have a trailing / in TMPDIR.
    if (path[base_len - 1] != '/') {
        lean_always_assert(PATH_MAX >= base_len + 1 + 1);
        strcat(path, "/");
    }
#endif

    const char* file_pattern = "tmp.XXXXXXXX";
    const size_t file_pattern_size = strlen(file_pattern);
    lean_always_assert(PATH_MAX >= strlen(path) + file_pattern_size + 1);
    strcat(path, file_pattern);

    uv_fs_t req;
    // Differences from lean_io_create_tempdir start here
    ret = uv_fs_mkstemp(NULL, &req, path, NULL);
    if (ret < 0) {
        // If mkstemp throws an error we cannot rely on path to contain a proper file name.
        return io_result_mk_error(decode_uv_error(ret, nullptr));
    } else {
        FILE* handle = fdopen(req.result, "r+");
        object_ref pair = mk_cnstr(0, io_wrap_handle(handle), mk_string(req.path));
        uv_fs_req_cleanup(&req);
        return lean_io_result_mk_ok(pair.steal());
    }
}

/* createTempDir : IO FilePath */
extern "C" LEAN_EXPORT obj_res lean_io_create_tempdir(lean_object * /* w */) {
    char path[PATH_MAX];
    size_t base_len = PATH_MAX;
    int ret = uv_os_tmpdir(path, &base_len);
    if (ret < 0) {
        return io_result_mk_error(decode_uv_error(ret, nullptr));
    } else if (base_len == 0) {
        return lean_io_result_mk_error(decode_uv_error(UV_ENOENT, mk_string("")));
    }

#if defined(LEAN_WINDOWS)
    // On Windows `GetTempPathW` always returns a path ending in \, but libuv removes it.
    // https://learn.microsoft.com/en-us/windows/win32/fileio/creating-and-using-a-temporary-file
    if (path[base_len - 1] != '\\') {
        lean_always_assert(PATH_MAX >= base_len + 1 + 1);
        strcat(path, "\\");
    }
#else
    // No guarantee that we have a trailing / in TMPDIR.
    if (path[base_len - 1] != '/') {
        lean_always_assert(PATH_MAX >= base_len + 1 + 1);
        strcat(path, "/");
    }
#endif

    const char* file_pattern = "tmp.XXXXXXXX";
    const size_t file_pattern_size = strlen(file_pattern);
    lean_always_assert(PATH_MAX >= strlen(path) + file_pattern_size + 1);
    strcat(path, file_pattern);

    uv_fs_t req;
    // Differences from lean_io_create_tempfile start here
    ret = uv_fs_mkdtemp(NULL, &req, path, NULL);
    if (ret < 0) {
        // If mkdtemp throws an error we cannot rely on path to contain a proper file name.
        return io_result_mk_error(decode_uv_error(ret, nullptr));
    } else {
        obj_res res = lean_io_result_mk_ok(mk_string(req.path));
        uv_fs_req_cleanup(&req);
        return res;
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_remove_file(b_obj_arg fname, obj_arg) {
    if (std::remove(string_cstr(fname)) == 0) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(decode_io_error(errno, fname));
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_app_path(obj_arg) {
#if defined(LEAN_WINDOWS)
    HMODULE hModule = GetModuleHandle(NULL);
    char path[MAX_PATH];
    GetModuleFileName(hModule, path, MAX_PATH);
    std::string pathstr(path);
    // Hack for making sure disk is lower case
    // TODO(Leo): more robust solution
    if (pathstr.size() >= 2 && pathstr[1] == ':') {
        pathstr[0] = tolower(pathstr[0]);
    }
    return io_result_mk_ok(mk_string(pathstr));
#elif defined(__APPLE__)
    char buf1[PATH_MAX];
    char buf2[PATH_MAX];
    uint32_t bufsize = PATH_MAX;
    if (_NSGetExecutablePath(buf1, &bufsize) != 0)
        return io_result_mk_error("failed to locate application");
    if (!realpath(buf1, buf2))
        return io_result_mk_error("failed to resolve symbolic links when locating application");
    return io_result_mk_ok(mk_string(buf2));
#elif defined(LEAN_EMSCRIPTEN)
    // See https://emscripten.org/docs/api_reference/emscripten.h.html#c.EM_ASM_INT
    char* appPath = reinterpret_cast<char*>(EM_ASM_INT({
        if ((typeof process === "undefined") || (process.release.name !== "node")) {
            return 0;
        }

        var lengthBytes = lengthBytesUTF8(__filename)+1;
        var pathOnWasmHeap = _malloc(lengthBytes);
        stringToUTF8(__filename, pathOnWasmHeap, lengthBytes);
        return pathOnWasmHeap;
    }));
    if (appPath == nullptr) {
        return io_result_mk_error("no Lean executable file exists in WASM outside of Node.js");
    }

    object * appPathLean = mk_string(appPath);
    free(appPath);
    return io_result_mk_ok(appPathLean);
#else
    // Linux version
    char path[PATH_MAX];
    char dest[PATH_MAX];
    memset(dest, 0, PATH_MAX);
    pid_t pid = getpid();
    snprintf(path, PATH_MAX, "/proc/%d/exe", pid);
    if (readlink(path, dest, PATH_MAX) == -1) {
        return io_result_mk_error("failed to locate application");
    } else {
        return io_result_mk_ok(mk_string(dest));
    }
#endif
}

extern "C" LEAN_EXPORT obj_res lean_io_current_dir(obj_arg) {
    char buffer[PATH_MAX];
    char * cwd = getcwd(buffer, sizeof(buffer));
    if (cwd) {
        return io_result_mk_ok(mk_string(cwd));
    } else {
        return io_result_mk_error("failed to retrieve current working directory");
    }
}

// =======================================
// ST ref primitives
extern "C" LEAN_EXPORT obj_res lean_st_mk_ref(obj_arg a, obj_arg) {
    lean_ref_object * o = (lean_ref_object*)lean_alloc_small_object(sizeof(lean_ref_object));
    lean_set_st_header((lean_object*)o, LeanRef, 0);
    o->m_value = a;
    return io_result_mk_ok((lean_object*)o);
}

static object * g_io_error_nullptr_read = nullptr;

static inline atomic<object*> * mt_ref_val_addr(object * o) {
    return reinterpret_cast<atomic<object*> *>(&(lean_to_ref(o)->m_value));
}

/*
  Important: we have added support for initializing global constants
  at program startup. This feature is particularly useful for
  initializing `ST.Ref` values. Any `ST.Ref` value created during
  initialization will be marked as persistent. Thus, to make `ST.Ref`
  API thread-safe, we must treat persistent `ST.Ref` objects created
  during initialization as a multi-threaded object. Then, whenever we store
  a value `val` into a global `ST.Ref`, we have to mark `va`l as a multi-threaded
  object as we do for multi-threaded `ST.Ref`s. It makes sense since
  the global `ST.Ref` may be used to communicate data between threads.
*/
static inline bool ref_maybe_mt(b_obj_arg ref) { return lean_is_mt(ref) || lean_is_persistent(ref); }

extern "C" LEAN_EXPORT obj_res lean_st_ref_get(b_obj_arg ref, obj_arg) {
    if (ref_maybe_mt(ref)) {
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        while (true) {
            /*
              We cannot simply read `val` from the ref and `inc` it like in the `else` branch since someone else could
              write to the ref in between and remove the last owning reference to the object. Instead, we must take
              ownership of the RC token in the ref via `exchange`, duplicate it, then put one RC token back. */
            object * val = val_addr->exchange(nullptr);
            if (val != nullptr) {
                inc(val);
                object * tmp = val_addr->exchange(val);
                if (tmp != nullptr) {
                    /* this may happen if another thread wrote `ref` */
                    dec(tmp);
                }
                return io_result_mk_ok(val);
            }
        }
    } else {
        object * val = lean_to_ref(ref)->m_value;
        lean_assert(val != nullptr);
        inc(val);
        return io_result_mk_ok(val);
    }
}

extern "C" LEAN_EXPORT obj_res lean_st_ref_take(b_obj_arg ref, obj_arg) {
    if (ref_maybe_mt(ref)) {
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        while (true) {
            object * val = val_addr->exchange(nullptr);
            if (val != nullptr)
                return io_result_mk_ok(val);
        }
    } else {
        object * val = lean_to_ref(ref)->m_value;
        lean_assert(val != nullptr);
        lean_to_ref(ref)->m_value = nullptr;
        return io_result_mk_ok(val);
    }
}

static_assert(sizeof(atomic<unsigned short>) == sizeof(unsigned short), "`atomic<unsigned short>` and `unsigned short` must have the same size"); // NOLINT

extern "C" LEAN_EXPORT obj_res lean_st_ref_set(b_obj_arg ref, obj_arg a, obj_arg) {
    if (ref_maybe_mt(ref)) {
        /* We must mark `a` as multi-threaded if `ref` is marked as multi-threaded.
           Reason: our runtime relies on the fact that a single-threaded object
           cannot be reached from a multi-thread object. */
        mark_mt(a);
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        object * old_a = val_addr->exchange(a);
        if (old_a != nullptr)
            dec(old_a);
        return io_result_mk_ok(box(0));
    } else {
        if (lean_to_ref(ref)->m_value != nullptr)
            dec(lean_to_ref(ref)->m_value);
        lean_to_ref(ref)->m_value = a;
        return io_result_mk_ok(box(0));
    }
}

extern "C" LEAN_EXPORT obj_res lean_st_ref_swap(b_obj_arg ref, obj_arg a, obj_arg) {
    if (ref_maybe_mt(ref)) {
        /* See io_ref_write */
        mark_mt(a);
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        while (true) {
            object * old_a = val_addr->exchange(a);
            if (old_a != nullptr)
                return io_result_mk_ok(old_a);
        }
    } else {
        object * old_a = lean_to_ref(ref)->m_value;
        if (old_a == nullptr)
            return io_result_mk_error(g_io_error_nullptr_read);
        lean_to_ref(ref)->m_value = a;
        return io_result_mk_ok(old_a);
    }
}

extern "C" LEAN_EXPORT obj_res lean_st_ref_ptr_eq(b_obj_arg ref1, b_obj_arg ref2, obj_arg) {
    // TODO(Leo): ref_maybe_mt
    bool r = lean_to_ref(ref1)->m_value == lean_to_ref(ref2)->m_value;
    return io_result_mk_ok(box(r));
}

/* {α : Type} (act : BaseIO α) (_ : IO.RealWorld) : α */
static obj_res lean_io_as_task_fn(obj_arg act, obj_arg) {
    object_ref r(apply_1(act, io_mk_world()));
    return object_ref(io_result_get_value(r.raw()), true).steal();
}

/* asTask {α : Type} (act : BaseIO α) (prio : Nat) : BaseIO (Task α) */
extern "C" LEAN_EXPORT obj_res lean_io_as_task(obj_arg act, obj_arg prio, obj_arg) {
    object * c = lean_alloc_closure((void*)lean_io_as_task_fn, 2, 1);
    lean_closure_set(c, 0, act);
    object * t = lean_task_spawn_core(c, lean_unbox(prio), /* keep_alive */ true);
    return io_result_mk_ok(t);
}

/* {α β : Type} (f : α → BaseIO β) (a : α) : β */
static obj_res lean_io_bind_task_fn(obj_arg f, obj_arg a) {
    object_ref r(apply_2(f, a, io_mk_world()));
    return object_ref(io_result_get_value(r.raw()), true).steal();
}

/*  mapTask (f : α → BaseIO β) (t : Task α) (prio : Nat) (sync : Bool) : BaseIO (Task β) */
extern "C" LEAN_EXPORT obj_res lean_io_map_task(obj_arg f, obj_arg t, obj_arg prio, uint8 sync,
        obj_arg) {
    object * c = lean_alloc_closure((void*)lean_io_bind_task_fn, 2, 1);
    lean_closure_set(c, 0, f);
    object * t2 = lean_task_map_core(c, t, lean_unbox(prio), sync, /* keep_alive */ true);
    return io_result_mk_ok(t2);
}

/*  bindTask (t : Task α) (f : α → BaseIO (Task β)) (prio : Nat) (sync : Bool) : BaseIO (Task β) */
extern "C" LEAN_EXPORT obj_res lean_io_bind_task(obj_arg t, obj_arg f, obj_arg prio, uint8 sync,
        obj_arg) {
    object * c = lean_alloc_closure((void*)lean_io_bind_task_fn, 2, 1);
    lean_closure_set(c, 0, f);
    object * t2 = lean_task_bind_core(t, c, lean_unbox(prio), sync, /* keep_alive */ true);
    return io_result_mk_ok(t2);
}

extern "C" LEAN_EXPORT obj_res lean_io_check_canceled(obj_arg) {
    return io_result_mk_ok(box(lean_io_check_canceled_core()));
}

extern "C" LEAN_EXPORT obj_res lean_io_cancel(b_obj_arg t, obj_arg) {
    lean_io_cancel_core(t);
    return io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT obj_res lean_io_get_task_state(b_obj_arg t, obj_arg) {
    return io_result_mk_ok(box(lean_io_get_task_state_core(t)));
}

extern "C" LEAN_EXPORT obj_res lean_io_wait(obj_arg t, obj_arg) {
    return io_result_mk_ok(lean_task_get_own(t));
}

extern "C" LEAN_EXPORT obj_res lean_io_wait_any(b_obj_arg task_list, obj_arg) {
    object * t = lean_io_wait_any_core(task_list);
    object * v = lean_task_get(t);
    lean_inc(v);
    return io_result_mk_ok(v);
}

extern "C" LEAN_EXPORT obj_res lean_io_exit(uint8_t code, obj_arg /* w */) {
    exit(code);
}

extern "C" LEAN_EXPORT obj_res lean_runtime_mark_multi_threaded(obj_arg a, obj_arg /* w */) {
    lean_mark_mt(a);
    return io_result_mk_ok(a);
}

extern "C" LEAN_EXPORT obj_res lean_runtime_mark_persistent(obj_arg a, obj_arg /* w */) {
    lean_mark_persistent(a);
    return io_result_mk_ok(a);
}

extern "C" LEAN_EXPORT obj_res lean_runtime_forget(obj_arg /* a */, obj_arg /* w */) {
    return io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT obj_res lean_option_get_or_block(obj_arg o_opt) {
    option_ref<object_ref> opt = option_ref<object_ref>(o_opt);
    if (opt) {
        return opt.get_val().steal();
    } else {
        lean_panic("PANIC: Promise.result!: promise has been dropped without ever being resolved",
          /* force_stderr */ true);
        // this is only reachable when using non-fatal panics
        while (true) {
            this_thread::sleep_for(std::chrono::seconds::max());
        }
    }
}

void initialize_io() {
    g_io_error_nullptr_read = lean_mk_io_user_error(mk_ascii_string_unchecked("null reference read"));
    mark_persistent(g_io_error_nullptr_read);
    g_io_handle_external_class = lean_register_external_class(io_handle_finalizer, io_handle_foreach);
#if defined(LEAN_WINDOWS)
    _setmode(_fileno(stdout), _O_BINARY);
    _setmode(_fileno(stderr), _O_BINARY);
    _setmode(_fileno(stdin), _O_BINARY);
#endif
    g_stream_stdout = lean_stream_of_handle(io_wrap_handle(stdout));
    mark_persistent(g_stream_stdout);
    g_stream_stderr = lean_stream_of_handle(io_wrap_handle(stderr));
    mark_persistent(g_stream_stderr);
    g_stream_stdin  = lean_stream_of_handle(io_wrap_handle(stdin));
    mark_persistent(g_stream_stdin);
#if !defined(LEAN_WINDOWS) && !defined(LEAN_EMSCRIPTEN)
    // We want to handle SIGPIPE ourselves
    lean_always_assert(signal(SIGPIPE, SIG_IGN) != SIG_ERR);
#endif
}

void finalize_io() {
}
}
