/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#if defined(LEAN_WINDOWS)
#include <windows.h>
#include <namedpipeapi.h>
#elif defined(__APPLE__)
#include <mach-o/dyld.h>
#else
// Linux include files
#include <wait.h>
#endif
#include <iostream>
#include <chrono>
#include <sstream>
#include <fstream>
#include <iomanip>
#include <string>
#include <cstdlib>
#include <cctype>
#include "util/io.h"
#include "runtime/utf8.h"
#include "runtime/object.h"
#include "runtime/thread.h"
#include "runtime/allocprof.h"

#include <unistd.h>
#include <sys/stat.h>

#include <stdio.h>
#include <sys/types.h>
#include <fcntl.h>
#include <signal.h>

#ifdef _MSC_VER
#define S_ISDIR(mode) ((mode & _S_IFDIR) != 0)
#else
#include <dirent.h>
#endif

namespace lean {

extern "C" {
lean_object* lean_string_append(lean_object*, lean_object*);

lean_object* lean_mk_io_error_already_exists(uint32_t, lean_object*);
extern lean_object* lean_mk_io_error_eof;
lean_object* lean_mk_io_error_hardware_fault(uint32_t, lean_object*);
lean_object* lean_mk_io_error_illegal_operation(uint32_t, lean_object*);
lean_object* lean_mk_io_error_inappropriate_type(uint32_t, lean_object*);
lean_object* lean_mk_io_error_inappropriate_type_file(lean_object*, uint32_t, lean_object*);
lean_object* lean_mk_io_error_interrupted(lean_object*, uint32_t, lean_object*);
lean_object* lean_mk_io_error_invalid_argument(uint32_t, lean_object*);
lean_object* lean_mk_io_error_invalid_argument_file(lean_object*, uint32_t, lean_object*);
lean_object* lean_mk_io_error_no_file_or_directory(lean_object*, uint32_t, lean_object*);
lean_object* lean_mk_io_error_no_such_thing(uint32_t, lean_object*);
lean_object* lean_mk_io_error_no_such_thing_file(lean_object*, uint32_t, lean_object*);
lean_object* lean_mk_io_error_other_error(uint32_t, lean_object*);
lean_object* lean_mk_io_error_permission_denied(uint32_t, lean_object*);
lean_object* lean_mk_io_error_permission_denied_file(lean_object*, uint32_t, lean_object*);
lean_object* lean_mk_io_error_protocol_error(uint32_t, lean_object*);
lean_object* lean_mk_io_error_resource_busy(uint32_t, lean_object*);
lean_object* lean_mk_io_error_resource_exhausted(uint32_t, lean_object*);
lean_object* lean_mk_io_error_resource_exhausted_file(lean_object*, uint32_t, lean_object*);
lean_object* lean_mk_io_error_resource_vanished(uint32_t, lean_object*);
lean_object* lean_mk_io_error_time_expired(uint32_t, lean_object*);
lean_object* lean_mk_io_error_unsatisfied_constraints(uint32_t, lean_object*);
lean_object* lean_mk_io_error_unsupported_operation(uint32_t, lean_object*);

void lean_io_result_show_error(b_obj_arg r) {
    object * err = io_result_get_error(r);
    inc_ref(err);
    object * str = lean_io_error_to_string(err);
    std::cerr << "uncaught exception: " << string_cstr(str) << std::endl;
    dec_ref(str);
}
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

obj_res decode_io_error(int errnum, b_obj_arg fname);

static obj_res mk_file_not_found_error(b_obj_arg fname) {
    return set_io_error(decode_io_error(ENOENT, fname));
}

extern "C" obj_res lean_io_initializing(obj_arg) {
    return set_io_result(box(g_initializing));
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

static object * g_handle_stdout = nullptr;
static object * g_handle_stderr = nullptr;
static object * g_handle_stdin  = nullptr;
MK_THREAD_LOCAL_GET(object *, get_handle_current_stdout, g_handle_stdout);
MK_THREAD_LOCAL_GET(object *, get_handle_current_stderr, g_handle_stderr);
MK_THREAD_LOCAL_GET(object *, get_handle_current_stdin,  g_handle_stdin);

/* getStdout : IO FS.Handle */
extern "C" obj_res lean_get_stdout(obj_arg /* w */) {
    object * r = get_handle_current_stdout();
    inc_ref(r);
    return set_io_result(r);
}

/* getStderr : IO FS.Handle */
extern "C" obj_res lean_get_stderr(obj_arg /* w */) {
    object * r = get_handle_current_stderr();
    inc_ref(r);
    return set_io_result(r);
}

/* getStdin : IO FS.Handle */
extern "C" obj_res lean_get_stdin(obj_arg /* w */) {
    object * r = get_handle_current_stdin();
    inc_ref(r);
    return set_io_result(r);
}

/* setStdout  : FS.Handle -> IO FS.Handle */
extern "C" obj_res lean_get_set_stdout(obj_arg h, obj_arg /* w */) {
    object * & x = get_handle_current_stdout();
    object * r = x;
    x = h;
    return set_io_result(r);
}

/* setStderr  : FS.Handle -> IO FS.Handle */
extern "C" obj_res lean_get_set_stderr(obj_arg h, obj_arg /* w */) {
    object * & x = get_handle_current_stderr();
    object * r = x;
    x = h;
    return set_io_result(r);
}

/* setStdin  : FS.Handle -> IO FS.Handle */
extern "C" obj_res lean_get_set_stdin(obj_arg h, obj_arg /* w */) {
    object * & x = get_handle_current_stdin();
    object * r = x;
    x = h;
    return set_io_result(r);
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
        lean_assert(fname == nullptr);
        return lean_mk_io_error_already_exists(errnum, details);
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

#if defined(LEAN_WINDOWS)
static FILE * from_win_handle(HANDLE handle, char const * mode) {
    int fd = _open_osfhandle(reinterpret_cast<intptr_t>(handle), _O_APPEND);
    return fdopen(fd, mode);
}
#endif

static obj_res mk_pipe_obj (int read, int write) {
    object * res = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(res, 0, io_wrap_handle(fdopen(read, "r")));
    lean_ctor_set(res, 1, io_wrap_handle(fdopen(write, "w")));
    return res;
}

/* Prim.mkPipe : IO Pipe := arbitrary _ */
extern "C" obj_res lean_io_mk_pipe(bool non_blocking, obj_arg /* w */) {
#if defined(LEAN_WINDOWS)
    HANDLE read, write;
    SECURITY_ATTRIBUTES sec_attr = { 0, nullptr, true };
    bool success = CreatePipe(&read, &write, &sec_attr, 0);
    if (!success) {
        return set_io_error("Failed to create a pipe");
    }
    int in_fd = _open_osfhandle(reinterpret_cast<intptr_t>(read), _O_APPEND);
    int out_fd = _open_osfhandle(reinterpret_cast<intptr_t>(read), _O_APPEND);
    if (non_blocking) {
        fcntl(in_fd, F_GETFL);
    }
    return set_io_result(mk_pipe_obj(in_fd, out_fd));
#else
    int fd[2];
    if (pipe(fd) < 0) {
        return set_io_error(decode_io_error(errno, nullptr));
    }
    if (non_blocking) {
        fcntl(fd[0], F_SETFL, O_NONBLOCK);
    }
    return set_io_result(mk_pipe_obj(fd[0], fd[1]));
#endif
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
        return set_io_error(lean_mk_io_error_eof);
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

/* Handle.getLine : (@& Handle) → IO Unit                */
/*   The line returned by `lean_io_prim_handle_get_line` */
/*   is truncated at the first '\0' character and the    */
/*   rest of the line is discarded.                      */
extern "C" obj_res lean_io_prim_handle_get_line(b_obj_arg h, obj_arg /* w */) {
    FILE * fp = io_get_handle(h);
    if (feof(fp)) {
        return set_io_error(lean_mk_io_error_eof);
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
        fflush(fp);
        return set_io_result(box(0));
    } else {
        return set_io_error(decode_io_error(errno, nullptr));
    }
}

static char * const * copy_cstr_array(const char *cmd, object* from) {
    unsigned i;
    char ** to = new char * [lean_array_size(from)+2];
    to[0] = const_cast<char *>(cmd);
    for (i = 0; i < lean_array_size(from); ++i) {
        to[i+1] = const_cast<char *>(lean_string_cstr(lean_array_get_core(from, i)));
    }
    to[i+1] = nullptr;
    return to;
}

// structure SpawnArgsIntl :=
// (cmd : String)
// (args : Array String := #[])
// (stdin : FS.Handle)
// (stdout : FS.Handle)
// (stderr : FS.Handle)
// (cwd : Option String := none)
// (env : Array String := #[])

extern "C" obj_res lean_proc_spawn(obj_arg spawn_args, b_obj_arg other_handles, obj_arg /* w */) {
    object * cmd  = lean_ctor_get(spawn_args, 0);
    object * args_o = lean_ctor_get(spawn_args, 1);
    FILE * hStdin  = static_cast<FILE *>(external_data(lean_ctor_get(spawn_args, 2)));
    FILE * hStdout = static_cast<FILE *>(external_data(lean_ctor_get(spawn_args, 3)));
    FILE * hStderr = static_cast<FILE *>(external_data(lean_ctor_get(spawn_args, 4)));
    object * cwd = lean_ctor_get(spawn_args, 5);
    object * env_o = lean_ctor_get(spawn_args, 6);
#if defined(LEAN_WINDOWS)
    PROCESS_INFORMATION piProcInfo;
    STARTUPINFO siStartInfo;
    BOOL bSuccess = FALSE;

    // Set up members of the PROCESS_INFORMATION structure.
    ZeroMemory(&piProcInfo, sizeof(PROCESS_INFORMATION));

    // Set up members of the STARTUPINFO structure.
    // This structure specifies the STDIN and STDOUT handles for redirection.

    ZeroMemory(&siStartInfo, sizeof(STARTUPINFO));
    siStartInfo.cb = sizeof(STARTUPINFO);
    siStartInfo.hStdError  = _get_osfhandle(fileno(hStderr));
    siStartInfo.hStdOutput = _get_osfhandle(fileno(hStdout));
    siStartInfo.hStdInput  = _get_osfhandle(fileno(hStdin));
    siStartInfo.dwFlags |= STARTF_USESTDHANDLES;
    bSuccess = CreateProcess(
        NULL,
        lean_string_cstr(cmd), // command line
        NULL,                                // process security attributes
        NULL,                                // primary thread security attributes
        TRUE,                                // handles are inherited
        0,                                   // creation flags
        NULL,                                // use parent's environment
        lean_is_scalar(cwd) ? nullptr : lean_ctor_get(cwd, 0),
                                             // current directory
        &siStartInfo,                        // STARTUPINFO pointer
        &piProcInfo);                        // receives PROCESS_INFORMATION



    CloseHandle(piProcInfo.hThread);

    return piProcInfo.hProcess;

#else
    int pid = fork();
    if (pid == 0) {
        dup2(fileno(hStdin), 0);
        dup2(fileno(hStdout), 1);
        dup2(fileno(hStderr), 2);
        for (unsigned i = 0; i < lean_array_size(other_handles); i++) {
            if (!lean_is_scalar(lean_array_get_core(other_handles, i))) {
                FILE * h = static_cast<FILE *>(external_data(lean_ctor_get(lean_array_get_core(other_handles, i), 0)));
                fclose(h);
            }
        }
        for (unsigned i = 0; i < lean_array_size(env_o); i++) {
            auto entry = lean_array_get_core(env_o, i);
            auto key   = lean_ctor_get(entry, 0);
            auto value = lean_ctor_get(entry, 1);
            if (is_scalar(value)) {
                unsetenv(lean_string_cstr(key));
            } else {
                setenv(lean_string_cstr(key),
                       lean_string_cstr(lean_ctor_get(value, 0)), 1);
            }
        }

        char * const * args = copy_cstr_array(lean_string_cstr(cmd), args_o); // we're leaking memory here but it doesn't matter
        if (!is_scalar(cwd)) {
            chdir(lean_string_cstr(lean_ctor_get(cwd, 0)));
        }
        execvp(lean_string_cstr(cmd), args);
        std::cerr << "failed to start process\n";
        exit(-1);
    } else {
        return set_io_result(box(pid));
    }
#endif
}

extern "C" obj_res lean_proc_kill(b_obj_arg pid, obj_arg /* w */) {
#if defined(LEAN_WINDOWS)
    TerminateProcess(unbox(pid));
#else
    kill(unbox(pid), SIGTERM);
#endif
    return set_io_result(box(0));
}

extern "C" obj_res lean_proc_wait(b_obj_arg pid, obj_arg /* w */) {
    int wstatus, w;
#if defined(LEAN_WINDOWS)
    WaitForSingleObject(unbox(pid), 0);
#else
    w = waitpid(unbox(pid), &wstatus, WUNTRACED | WCONTINUED);
    if (w == -1) {
        return set_io_error(decode_io_error(errno, nullptr));
    }
#endif
    return set_io_result(box(wstatus));
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
    g_io_handle_external_class = lean_register_external_class(io_handle_finalizer, io_handle_foreach);
    g_handle_stdout = io_wrap_handle(stdout);
    g_handle_stderr = io_wrap_handle(stderr);
    g_handle_stdin  = io_wrap_handle(stdin);
    mark_persistent(g_handle_stdout);
    mark_persistent(g_handle_stderr);
    mark_persistent(g_handle_stdin);
    mark_persistent(g_io_error_nullptr_read);
}

void finalize_io() {
}
}
