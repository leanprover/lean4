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
#include "runtime/object.h"
#include "runtime/thread.h"
#include "runtime/allocprof.h"

#ifdef _MSC_VER
#define S_ISDIR(mode) ((mode & _S_IFDIR) != 0)
#else
#include <dirent.h>
#endif

namespace lean {
extern "C" void lean_io_result_show_error(b_obj_arg r) {
    std::cerr << "uncaught exception: " << string_cstr(io_result_get_error(r)) << std::endl;
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

object * mk_io_user_error(object * str) {
    // TODO(Leo): fix after we expand IO.Error
    return str;
}

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

/* handle.mk (s : string) (m : mode) (bin : bool := ff) : eio handle */
extern "C" obj_res lean_io_prim_handle_mk(b_obj_arg /* s */, uint8 /* mode */, uint8 /* bin */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.is_eof : handle → eio bool */
extern "C" obj_res lean_io_prim_handle_is_eof(b_obj_arg /* h */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.flush : handle → eio bool */
extern "C" obj_res lean_io_prim_handle_flush(b_obj_arg /* h */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.close : handle → eio unit */
extern "C" obj_res lean_io_prim_handle_close(b_obj_arg /* h */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.get_line : handle → eio unit */
extern "C" obj_res lean_io_prim_handle_get_line(b_obj_arg /* h */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* timeit {α : Type} (msg : @& string) (fn : io α) : io α */
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

/* allocprof {α : Type} (msg : string) (fn : io α) : io α */
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
    // TODO: ref_maybe_mt
    bool r = lean_to_ref(ref1)->m_value == lean_to_ref(ref2)->m_value;
    return set_io_result(box(r));
}

void initialize_io() {
    g_io_error_nullptr_read = mk_string("null reference read");
    mark_persistent(g_io_error_nullptr_read);
}

void finalize_io() {
}
}
