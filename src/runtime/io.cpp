/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#if defined(LEAN_WINDOWS)
#include <windows.h>
#elif defined(__APPLE__)
#include <mach-o/dyld.h>
#else
// Linux include files
#include <unistd.h>
#endif
#include <iostream>
#include <chrono>
#include <sstream>
#include <fstream>
#include <iomanip>
#include <string>
#include <cstdlib>
#include <cctype>
#include <sys/stat.h>
#include "util/io.h"
#include "runtime/utf8.h"
#include "runtime/object.h"
#include "runtime/thread.h"
#include "runtime/allocprof.h"

#ifdef _MSC_VER
#define S_ISDIR(mode) ((mode & _S_IFDIR) != 0)
#else
#include <dirent.h>
#endif

namespace lean {

extern "C" lean_object* lean_mk_io_error_permission_denied_file(lean_object*, lean_object*);
extern "C" lean_object* lean_mk_io_error_no_file_or_directory(lean_object*, lean_object*);
extern "C" lean_object* mk_io_user_error(lean_object*);
extern "C" lean_object* lean_string_append(lean_object*, lean_object*);
extern "C" lean_object* lean_mk_io_error_resource_exhausted_file(lean_object*, lean_object*);
extern "C" lean_object* lean_mk_io_error_interrupted(lean_object*, lean_object*);
extern "C" lean_object* lean_mk_io_error_invalid_argument_file(lean_object*, lean_object*);
extern "C" lean_object* lean_mk_io_error_no_such_thing_file(lean_object*, lean_object*);
extern "C" lean_object* lean_mk_io_error_inappropriate_type_file(lean_object*, lean_object*);
extern "C" lean_object* lean_mk_io_error_eof();
extern "C" lean_object* lean_mk_io_error_unsupported_operation(lean_object*);
extern "C" lean_object* lean_mk_io_error_resource_exhausted(lean_object*);
extern "C" lean_object* lean_mk_io_error_already_exists(lean_object*);
extern "C" lean_object* lean_mk_io_error_inappropriate_type(lean_object*);
extern "C" lean_object* lean_mk_io_error_no_such_thing(lean_object*);
extern "C" lean_object* lean_mk_io_error_resource_vanished(lean_object*);
extern "C" lean_object* lean_mk_io_error_resource_busy(lean_object*);
extern "C" lean_object* lean_mk_io_error_invalid_argument(lean_object*);
extern "C" lean_object* lean_mk_io_error_other_error(lean_object*);
extern "C" lean_object* lean_mk_io_error_permission_denied(lean_object*);
extern "C" lean_object* lean_mk_io_error_no_such_thing(lean_object*);
extern "C" lean_object* lean_mk_io_error_unsupported_operation(lean_object*);
extern "C" lean_object* lean_mk_io_error_hardware_fault(lean_object*);
extern "C" lean_object* lean_mk_io_error_unsatisfied_constraints(lean_object*);
extern "C" lean_object* lean_mk_io_error_illegal_operation(lean_object*);
extern "C" lean_object* lean_mk_io_error_protocol_error(lean_object*);
extern "C" lean_object* lean_mk_io_error_time_expired(lean_object*);

extern "C" void lean_io_result_show_error(b_obj_arg r) {
    object * err = io_result_get_error(r);
    inc_ref(err);
    object * str = lean_io_error_to_string(err);
    std::cerr << "uncaught exception: " << string_cstr(str) << std::endl;
    dec_ref(str);
}

obj_res set_io_result(obj_arg a) {
    object * new_r = alloc_cnstr(0, 2, 0);
    cnstr_set(new_r, 0, a);
    cnstr_set(new_r, 1, box(0));
    return new_r;
}

obj_res set_io_error(obj_arg e) {
    object * new_r = alloc_cnstr(1, 2, 0);
    cnstr_set(new_r, 0, e);
    cnstr_set(new_r, 1, box(0));
    return new_r;
}

extern "C" object * mk_io_user_error(object * str);

obj_res set_io_error(char const * msg) {
    return set_io_error(mk_io_user_error(mk_string(msg)));
}

obj_res set_io_error(std::string const & msg) {
    return set_io_error(mk_io_user_error(mk_string(msg)));
}

static bool g_initializing = true;
extern "C" void lean_io_mark_end_initialization() {
    g_initializing = false;
}

static obj_res mk_file_not_found_error(b_obj_arg fname) {
    object * err = mk_string("file '");
    err = string_append(err, fname);
    object * tmp = mk_string("' not found");
    err = string_append(err, tmp);
    dec_ref(tmp);
    return set_io_error(err);
}

extern "C" obj_res lean_io_prim_read_text_file(b_obj_arg fname, obj_arg) {
    std::ifstream in(string_cstr(fname), std::ifstream::binary);
    if (!in.good()) {
        return mk_file_not_found_error(fname);
    } else {
        std::stringstream buf;
        buf << in.rdbuf();
        return set_io_result(mk_string(buf.str()));
    }
}

extern "C" obj_res lean_io_initializing(obj_arg) {
    return set_io_result(box(g_initializing));
}

extern "C" obj_res lean_io_prim_put_str(b_obj_arg s, obj_arg) {
    std::cout << string_to_std(s); // TODO(Leo): use out handle
    return set_io_result(box(0));
}

extern "C" obj_res lean_io_prim_get_line(obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

static lean_external_class * g_io_handle_external_class = nullptr;

static void io_handle_finalizer(void * h) {
    fclose(static_cast<FILE *>(h));
}

static void io_handle_foreach(void * /* mod */, b_obj_arg /* fn */) {
}

static lean_object * io_wrap_handle(FILE *hfile) {
    return lean_alloc_external(g_io_handle_external_class, hfile);
}

static FILE * io_get_handle(lean_object * hfile) {
    return static_cast<FILE *>(lean_get_external_data(hfile));
}

obj_res decode_io_error(int errnum, b_obj_arg fname) {
    object * details = mk_string(strerror(errnum));
    switch (errnum) {
    case EINTR:
        lean_assert(fname != nullptr);
        inc_ref(fname);
        return lean_mk_io_error_interrupted(fname, details);
    case ELOOP: case ENAMETOOLONG: case EDESTADDRREQ:
    case EBADF: case EDOM: case EINVAL: case EILSEQ:
    case ENOEXEC: case ENOSTR: case ENOTCONN:
    case ENOTSOCK:
        if (fname == nullptr) {
            return lean_mk_io_error_invalid_argument(details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_invalid_argument_file(fname, details);
        }
    case ENOENT:
        lean_assert(fname != nullptr);
        inc_ref(fname);
        return lean_mk_io_error_no_file_or_directory(fname, details);
    case EACCES: case EROFS: case ECONNABORTED: case EFBIG:
    case EPERM:
        if (fname == nullptr) {
            return lean_mk_io_error_permission_denied(details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_permission_denied_file(fname, details);
        }
    case EMFILE: case ENFILE: case ENOSPC:
    case E2BIG:  case EAGAIN: case EMLINK:
    case EMSGSIZE: case ENOBUFS: case ENOLCK:
    case ENOMEM: case ENOSR:
        if (fname == nullptr) {
            return lean_mk_io_error_resource_exhausted(details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_resource_exhausted_file(fname, details);
        }
    case EISDIR: case EBADMSG: case ENOTDIR:
        if (fname == nullptr) {
            return lean_mk_io_error_inappropriate_type(details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_inappropriate_type_file(fname, details);
        }
    case ENXIO: case EHOSTUNREACH: case ENETUNREACH:
    case ECHILD: case ECONNREFUSED: case ENODATA:
    case ENOMSG: case ESRCH:
        if (fname == nullptr) {
            return lean_mk_io_error_no_such_thing(details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_no_such_thing_file(fname, details);
        }
    case EEXIST: case EINPROGRESS: case EISCONN:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_already_exists(details);
    case EIO:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_hardware_fault(details);
    case ENOTEMPTY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_unsatisfied_constraints(details);
    case ENOTTY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_illegal_operation(details);
    case ECONNRESET: case EIDRM: case ENETDOWN: case ENETRESET:
    case ENOLINK: case EPIPE:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_resource_vanished(details);
    case EPROTO: case EPROTONOSUPPORT: case EPROTOTYPE:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_protocol_error(details);
    case ETIME: case ETIMEDOUT:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_time_expired(details);
    case EADDRINUSE: case EBUSY: case EDEADLK: case ETXTBSY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_resource_busy(details);
    case EADDRNOTAVAIL: case EAFNOSUPPORT: case ENODEV:
    case ENOPROTOOPT: case ENOSYS: case EOPNOTSUPP:
    case ERANGE: case ESPIPE: case EXDEV:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_unsupported_operation(details);
    case EFAULT:
    default:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_other_error(details);
    }
}

/* IO.setAccessRights (filename : @& String) (mode : UInt32) : IO Handle */
extern "C" obj_res lean_chmod (b_obj_arg filename, uint32_t mode, obj_arg /* w */) {
    if (!chmod(lean_string_cstr(filename), mode)) {
        return set_io_result(box(0));
    } else {
        return set_io_error(decode_io_error(errno, filename));
    }
}

/* Handle.mk (filename : @& String) (mode : @& String) : IO Handle */
extern "C" obj_res lean_io_prim_handle_mk(b_obj_arg filename, b_obj_arg modeStr, obj_arg /* w */) {
    FILE *fp = fopen(lean_string_cstr(filename), lean_string_cstr(modeStr));
    if (!fp) {
        return set_io_error(decode_io_error(errno, filename));
    } else {
        return set_io_result(io_wrap_handle(fp));
    }
}

/* Handle.isEof : (@& Handle) → IO Bool */
extern "C" obj_res lean_io_prim_handle_is_eof(b_obj_arg h, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    return set_io_result(box(std::feof(fp) != 0));
}

/* Handle.flush : (@& Handle) → IO Bool */
extern "C" obj_res lean_io_prim_handle_flush(b_obj_arg h, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    if (!std::fflush(fp)) {
        return set_io_result(box(0));
    } else {
        return set_io_error(decode_io_error(errno, nullptr));
    }
}

/* Handle.readByte : (@& Handle) → IO UInt8 */
extern "C" obj_res lean_io_prim_handle_read_byte(b_obj_arg h, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    int c = std::fgetc(fp);
    if (c != EOF) {
        return set_io_result(box(c));
    } else {
        return set_io_error(decode_io_error(errno, nullptr));
    }
}

/* Handle.writeByte : (@& Handle) → UInt8 → IO unit */
extern "C" obj_res lean_io_prim_handle_write_byte(b_obj_arg h, uint8 c, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    if (std::fputc(c, fp) != EOF) {
        return set_io_result(box(0));
    } else {
        return set_io_error(decode_io_error(errno, nullptr));
    }
}

/* Handle.read : (@& Handle) → USize → IO ByteArray */
extern "C" obj_res lean_io_prim_handle_read(b_obj_arg h, usize nbytes, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    if (feof(fp)) {
        return set_io_error(lean_mk_io_error_eof());
    }
    obj_res res = lean_alloc_sarray(1, 0, nbytes);
    usize n = std::fread(lean_sarray_cptr(res), 1, nbytes, fp);
    if (n > 0) {
        lean_sarray_set_size(res, n);
        return set_io_result(res);
    } else if (feof(fp)) {
        dec_ref(res);
        return set_io_result(alloc_sarray(1, 0, 0));
    } else {
        dec_ref(res);
        return set_io_error(decode_io_error(errno, nullptr));
    }
}

/* Handle.write : (@& Handle) → (@& ByteArray) → IO unit */
extern "C" obj_res lean_io_prim_handle_write(b_obj_arg h, b_obj_arg buf, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    usize n = lean_sarray_size(buf);
    usize m = std::fwrite(lean_sarray_cptr(buf), 1, n, fp);
    if (m == n) {
        return set_io_result(box(0));
    } else {
        return set_io_error(decode_io_error(errno, nullptr));
    }
}

obj_res lean_get_line(FILE * fp) {
    const int buf_sz = 64;
    lean_string_object * buf_str = lean_to_string(lean_alloc_string(0, buf_sz, 0));
    lean_object * res_str        = lean_alloc_string(1, buf_sz, 0);
    lean_to_string(res_str)->m_data[0] = '\0';
    char * out = nullptr;
    do {
        out = std::fgets(buf_str->m_data, buf_sz, fp);
        if (out != nullptr) {
            buf_str->m_size   = strlen(buf_str->m_data);
            buf_str->m_length = buf_str->m_size;
            buf_str->m_size++;
            res_str = lean_string_append(res_str, reinterpret_cast<object *>(buf_str));
        }
    } while (out != nullptr && buf_str->m_size == buf_sz);
    dec_ref(reinterpret_cast<object *>(buf_str));
    lean_to_string(res_str)->m_length = utf8_strlen(lean_to_string(res_str)->m_data);
    if (out == nullptr && !feof(fp)) {
        dec_ref(res_str);
        return nullptr;
    } else {
        return res_str;
    }
}

/* Handle.getLine : (@& Handle) → IO Unit                     */
/*   The line returned by `lean_io_prim_handle_get_line` */
/*   is truncated at the first '\0' character and the    */
/*   rest of the line is discarded.                      */
extern "C" obj_res lean_io_prim_handle_get_line(b_obj_arg h, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    if (feof(fp)) {
        return set_io_error(lean_mk_io_error_eof());
    }
    object * res = lean_get_line(fp);
    if (res != nullptr) {
        return set_io_result(res);
    } else if (feof(fp)) {
        return set_io_result(lean_mk_string(""));
    } else {
        return set_io_error(decode_io_error(errno, nullptr));
    }
}

/* Handle.putStr : (@& Handle) → (@& String) → IO Unit */
extern "C" obj_res lean_io_prim_handle_put_str(b_obj_arg h, b_obj_arg s, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    if (std::fputs(lean_string_cstr(s), fp) != EOF) {
        return set_io_result(box(0));
    } else {
        return set_io_error(decode_io_error(errno, nullptr));
    }
}

/* timeit {α : Type} (msg : @& String) (fn : IO α) : IO α */
extern "C" obj_res lean_io_timeit(b_obj_arg msg, obj_arg fn, obj_arg w) {
    auto start = std::chrono::steady_clock::now();
    w = apply_1(fn, w);
    auto end   = std::chrono::steady_clock::now();
    auto diff  = std::chrono::duration<double>(end - start);
    std::ostream & out = std::cerr; // TODO(Leo): replace?
    out << std::setprecision(3);
    if (diff < std::chrono::duration<double>(1)) {
        out << string_cstr(msg) << " " << std::chrono::duration<double, std::milli>(diff).count() << "ms\n";
    } else {
        out << string_cstr(msg) << " " << diff.count() << "s\n";
    }
    return w;
}

/* allocprof {α : Type} (msg : @& String) (fn : IO α) : IO α */
extern "C" obj_res lean_io_allocprof(b_obj_arg msg, obj_arg fn, obj_arg w) {
    std::ostream & out = std::cerr; // TODO(Leo): replace?
    allocprof prof(out, string_cstr(msg));
    return apply_1(fn, w);
}

extern "C" obj_res lean_io_getenv(b_obj_arg env_var, obj_arg) {
    char * val = std::getenv(string_cstr(env_var));
    if (val) {
        return set_io_result(mk_option_some(mk_string(val)));
    } else {
        return set_io_result(mk_option_none());
    }
}

extern "C" obj_res lean_io_realpath(obj_arg fname, obj_arg) {
#if defined(LEAN_EMSCRIPTEN)
    return set_io_result(fname);
#elif defined(LEAN_WINDOWS)
    constexpr unsigned BufferSize = 8192;
    char buffer[BufferSize];
    DWORD retval = GetFullPathName(string_cstr(fname), BufferSize, buffer, nullptr);
    if (retval == 0 || retval > BufferSize) {
        return set_io_result(fname);
    } else {
        dec_ref(fname);
        // Hack for making sure disk is lower case
        // TODO(Leo): more robust solution
        if (strlen(buffer) >= 2 && buffer[1] == ':') {
            buffer[0] = tolower(buffer[0]);
        }
        return set_io_result(mk_string(buffer));
    }
#else
    constexpr unsigned BufferSize = 8192;
    char buffer[BufferSize];
    char * tmp = realpath(string_cstr(fname), buffer);
    if (tmp) {
        obj_res s = mk_string(tmp);
        dec_ref(fname);
        return set_io_result(s);
    } else {
        obj_res res = mk_file_not_found_error(fname);
        dec_ref(fname);
        return res;
    }
#endif
}

extern "C" obj_res lean_io_is_dir(b_obj_arg fname, obj_arg) {
    struct stat st;
    if (stat(string_cstr(fname), &st) == 0) {
        bool b = S_ISDIR(st.st_mode);
        return set_io_result(box(b));
    } else {
        return set_io_result(box(0));
    }
}

extern "C" obj_res lean_io_file_exists(b_obj_arg fname, obj_arg) {
    bool b = !!std::ifstream(string_cstr(fname));
    return set_io_result(box(b));
}

extern "C" obj_res lean_io_app_dir(obj_arg) {
#if defined(LEAN_WINDOWS)
    HMODULE hModule = GetModuleHandleW(NULL);
    WCHAR path[MAX_PATH];
    GetModuleFileNameW(hModule, path, MAX_PATH);
    std::wstring pathwstr(path);
    std::string pathstr(pathwstr.begin(), pathwstr.end());
    // Hack for making sure disk is lower case
    // TODO(Leo): more robust solution
    if (pathstr.size() >= 2 && pathstr[1] == ':') {
        pathstr[0] = tolower(pathstr[0]);
    }
    return set_io_result(mk_string(pathstr));
#elif defined(__APPLE__)
    char buf1[PATH_MAX];
    char buf2[PATH_MAX];
    uint32_t bufsize = PATH_MAX;
    if (_NSGetExecutablePath(buf1, &bufsize) != 0)
        return set_io_error(mk_string("failed to locate application"));
    if (!realpath(buf1, buf2))
        return set_io_error(mk_string("failed to resolve symbolic links when locating application"));
    return set_io_result(mk_string(buf2));
#else
    // Linux version
    char path[PATH_MAX];
    char dest[PATH_MAX];
    memset(dest, 0, PATH_MAX);
    pid_t pid = getpid();
    snprintf(path, PATH_MAX, "/proc/%d/exe", pid);
    if (readlink(path, dest, PATH_MAX) == -1) {
        return set_io_error(mk_string("failed to locate application"));
    } else {
        return set_io_result(mk_string(dest));
    }
#endif
}

// =======================================
// IO ref primitives
extern "C" obj_res lean_io_mk_ref(obj_arg a, obj_arg) {
    lean_ref_object * o = (lean_ref_object*)lean_alloc_small_object(sizeof(lean_ref_object));
    lean_set_st_header((lean_object*)o, LeanRef, 0);
    o->m_value = a;
    return set_io_result((lean_object*)o);
}

static object * g_io_error_nullptr_read = nullptr;

static inline atomic<object*> * mt_ref_val_addr(object * o) {
    return reinterpret_cast<atomic<object*> *>(&(lean_to_ref(o)->m_value));
}

/*
  Important: we have added support for initializing global constants
  at program startup. This feature is particularly useful for
  initializing `IO.Ref` values. Any `IO.Ref` value created during
  initialization will be marked as persistent. Thus, to make `IO.Ref`
  API thread-safe, we must treat persistent `IO.Ref` objects created
  during initialization as a multi-threaded object. Then, whenever we store
  a value `val` into a global `IO.Ref`, we have to mark `va`l as a multi-threaded
  object as we do for multi-threaded `IO.Ref`s. It makes sense since
  the global `IO.Ref` may be used to communicate data between threads.
*/
static inline bool ref_maybe_mt(b_obj_arg ref) { return lean_is_mt(ref) || lean_is_persistent(ref); }

extern "C" obj_res lean_io_ref_get(b_obj_arg ref, obj_arg) {
    if (ref_maybe_mt(ref)) {
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        object * val = val_addr->exchange(nullptr);
        if (val == nullptr)
            return set_io_error(g_io_error_nullptr_read);
        inc(val);
        object * tmp = val_addr->exchange(val);
        if (tmp != nullptr) {
            /* this may happen if another thread wrote `ref` */
            dec(tmp);
        }
        return set_io_result(val);
    } else {
        object * val = lean_to_ref(ref)->m_value;
        if (val == nullptr)
            return set_io_error(g_io_error_nullptr_read);
        inc(val);
        return set_io_result(val);
    }
}

static_assert(sizeof(atomic<unsigned short>) == sizeof(unsigned short), "`atomic<unsigned short>` and `unsigned short` must have the same size"); // NOLINT

extern "C" obj_res lean_io_ref_reset(b_obj_arg ref, obj_arg) {
    if (ref_maybe_mt(ref)) {
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        object * old_a = val_addr->exchange(nullptr);
        if (old_a != nullptr)
            dec(old_a);
        return set_io_result(box(0));
    } else {
        if (lean_to_ref(ref)->m_value != nullptr)
            dec(lean_to_ref(ref)->m_value);
        lean_to_ref(ref)->m_value = nullptr;
        return set_io_result(box(0));
    }
}

extern "C" obj_res lean_io_ref_set(b_obj_arg ref, obj_arg a, obj_arg) {
    if (ref_maybe_mt(ref)) {
        /* We must mark `a` as multi-threaded if `ref` is marked as multi-threaded.
           Reason: our runtime relies on the fact that a single-threaded object
           cannot be reached from a multi-thread object. */
        mark_mt(a);
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        object * old_a = val_addr->exchange(a);
        if (old_a != nullptr)
            dec(old_a);
        return set_io_result(box(0));
    } else {
        if (lean_to_ref(ref)->m_value != nullptr)
            dec(lean_to_ref(ref)->m_value);
        lean_to_ref(ref)->m_value = a;
        return set_io_result(box(0));
    }
}

extern "C" obj_res lean_io_ref_swap(b_obj_arg ref, obj_arg a, obj_arg) {
    if (ref_maybe_mt(ref)) {
        /* See io_ref_write */
        mark_mt(a);
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        object * old_a = val_addr->exchange(a);
        if (old_a == nullptr)
            return set_io_error(g_io_error_nullptr_read);
        return set_io_result(old_a);
    } else {
        object * old_a = lean_to_ref(ref)->m_value;
        if (old_a == nullptr)
            return set_io_error(g_io_error_nullptr_read);
        lean_to_ref(ref)->m_value = a;
        return set_io_result(old_a);
    }
}

extern "C" obj_res lean_io_ref_ptr_eq(b_obj_arg ref1, b_obj_arg ref2, obj_arg) {
    // TODO(Leo): ref_maybe_mt
    bool r = lean_to_ref(ref1)->m_value == lean_to_ref(ref2)->m_value;
    return set_io_result(box(r));
}

void initialize_io() {
    g_io_error_nullptr_read = mk_string("null reference read");
    mark_persistent(g_io_error_nullptr_read);
    g_io_handle_external_class = lean_register_external_class(io_handle_finalizer, io_handle_foreach);
}

void finalize_io() {
}
}
