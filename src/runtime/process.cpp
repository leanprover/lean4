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
#include <spawn.h>
#include <dlfcn.h>
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

namespace lean {

enum stdio {
    PIPED,
    INHERIT,
    NUL,
};

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

extern "C" LEAN_EXPORT obj_res lean_io_process_child_wait(b_obj_arg, b_obj_arg child) {
    HANDLE h = static_cast<HANDLE>(lean_get_external_data(cnstr_get(child, 3)));
    DWORD exit_code;
    if (WaitForSingleObject(h, INFINITE) == WAIT_FAILED) {
        return io_result_mk_error((sstream() << GetLastError()).str());
    }
    if (!GetExitCodeProcess(h, &exit_code)) {
        return io_result_mk_error((sstream() << GetLastError()).str());
    }
    return lean_io_result_mk_ok(box_uint32(exit_code));
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_try_wait(b_obj_arg, b_obj_arg child) {
    HANDLE h = static_cast<HANDLE>(lean_get_external_data(cnstr_get(child, 3)));
    DWORD exit_code;
    DWORD ret = WaitForSingleObject(h, 0);
    if (ret == WAIT_FAILED) {
        return io_result_mk_error((sstream() << GetLastError()).str());
    } else if (ret == WAIT_TIMEOUT) {
        return io_result_mk_ok(mk_option_none());
    } else {
        if (!GetExitCodeProcess(h, &exit_code)) {
            return io_result_mk_error((sstream() << GetLastError()).str());
        }
        return lean_io_result_mk_ok(mk_option_some(box_uint32(exit_code)));
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_kill(b_obj_arg, b_obj_arg child) {
    HANDLE h = static_cast<HANDLE>(lean_get_external_data(cnstr_get(child, 3)));
    if (!TerminateProcess(h, 1)) {
        return io_result_mk_error((sstream() << GetLastError()).str());
    }
    return lean_io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_obj_arg, b_obj_arg child) {
    HANDLE h = static_cast<HANDLE>(lean_get_external_data(cnstr_get(child, 3)));
    return GetProcessId(h);
}

static FILE * from_win_handle(HANDLE handle, char const * mode) {
    int fd = _open_osfhandle(reinterpret_cast<intptr_t>(handle), _O_APPEND);
    return fdopen(fd, mode);
}

static void setup_stdio(SECURITY_ATTRIBUTES * saAttr, HANDLE * theirs, object ** ours, bool in, stdio cfg) {
    /* Setup stdio based on process configuration. */
    switch (cfg) {
    case stdio::INHERIT:
        lean_always_assert(DuplicateHandle(GetCurrentProcess(), *theirs,
                                           GetCurrentProcess(), theirs,
                                           0, TRUE, DUPLICATE_SAME_ACCESS));
        return;
    case stdio::PIPED: {
        HANDLE readh;
        HANDLE writeh;
        if (!CreatePipe(&readh, &writeh, saAttr, 0))
            throw std::system_error(GetLastError(), std::system_category());
        *ours = io_wrap_handle(in ? from_win_handle(writeh, "w") : from_win_handle(readh, "r"));
        *theirs = in ? readh : writeh;
        // Ensure the write handle to the pipe for STDIN is not inherited.
        lean_always_assert(SetHandleInformation(in ? writeh : readh, HANDLE_FLAG_INHERIT, 0));
        return;
    }
    case stdio::NUL:
        HANDLE hNul = CreateFile("NUL",
                                 in ? GENERIC_READ : GENERIC_WRITE,
                                 0, // TODO(WN): does NUL have to be shared?
                                 saAttr,
                                 OPEN_EXISTING,
                                 FILE_ATTRIBUTE_NORMAL,
                                 NULL);
        if (hNul == INVALID_HANDLE_VALUE)
            throw std::system_error(GetLastError(), std::system_category());
        *theirs = hNul;
        return;
    }
    lean_unreachable();
}

// This code is adapted from: https://msdn.microsoft.com/en-us/library/windows/desktop/ms682499(v=vs.85).aspx
static obj_res spawn(string_ref const & proc_name, array_ref<string_ref> const & args, stdio stdin_mode, stdio stdout_mode,
                     stdio stderr_mode, option_ref<string_ref> const & cwd, array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & env,
                     bool inherit_env, bool _do_setsid) {
    HANDLE child_stdin  = GetStdHandle(STD_INPUT_HANDLE);
    HANDLE child_stdout = GetStdHandle(STD_OUTPUT_HANDLE);
    HANDLE child_stderr = GetStdHandle(STD_ERROR_HANDLE);

    SECURITY_ATTRIBUTES saAttr;

    // Set the bInheritHandle flag so pipe/NUL handles are inherited.
    saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
    saAttr.bInheritHandle = TRUE;
    saAttr.lpSecurityDescriptor = NULL;

    object * parent_stdin  = box(0); setup_stdio(&saAttr, &child_stdin,  &parent_stdin,  true, stdin_mode);
    object * parent_stdout = box(0); setup_stdio(&saAttr, &child_stdout, &parent_stdout, false, stdout_mode);
    object * parent_stderr = box(0); setup_stdio(&saAttr, &child_stderr, &parent_stderr, false, stderr_mode);

    std::string program = proc_name.to_std_string();

    // Always escape program in cmdline, in case it contains spaces
    std::string command = "\"";
    command += program;
    command += "\"";

    // This needs some thought, on Windows we must pass a command string
    // which is a valid command, that is a fully assembled command to be executed.
    //
    // We must escape the arguments to preserving spacing and other characters,
    // we might need to revisit escaping here.
    for (auto arg : args) {
        command += " \"";
        for (char const * c = arg.data(); *c != 0; c++) {
            if (*c == '"') {
                command += '\\';
            }
            command += *c;
        }
        command += "\"";
    }

    PROCESS_INFORMATION piProcInfo;
    STARTUPINFO siStartInfo;

    // Set up members of the PROCESS_INFORMATION structure.
    ZeroMemory(&piProcInfo, sizeof(PROCESS_INFORMATION));

    // Set up members of the STARTUPINFO structure.
    // This structure specifies the STDIN and STDOUT handles for redirection.

    ZeroMemory(&siStartInfo, sizeof(STARTUPINFO));
    siStartInfo.cb = sizeof(STARTUPINFO);
    siStartInfo.hStdInput = child_stdin;
    siStartInfo.hStdOutput = child_stdout;
    siStartInfo.hStdError = child_stderr;
    siStartInfo.dwFlags |= STARTF_USESTDHANDLES;

    std::unique_ptr<char[]> new_env(nullptr);

    if (env.size() || !inherit_env) {
        static constexpr auto env_buf_size = 0x7fff; // according to MS docs 0x7fff is the max total size of env block
        new_env = std::make_unique<char[]>(env_buf_size);
        char *new_envp = new_env.get();

        if (env.size()) {
            std::unordered_map<std::string, option_ref<string_ref>> new_env_vars; // C++17 gives us no-copy std::string_view for this, much better!
            for (auto & entry : env) {
                new_env_vars[entry.fst().data()] = entry.snd();
            }

            // First copy old evars not in new evars.
            if (inherit_env) {
                auto *esp = GetEnvironmentStrings();
                char *key_begin = esp;
                while (*key_begin) {
                    char *key_end = strchr(key_begin, '=');
                    char *entry_end = key_end + strlen(key_end);
                    if (!new_env_vars.count({key_begin, key_end})) {
                        new_envp = std::copy(key_begin, entry_end + 1, new_envp);
                    }
                    key_begin = entry_end + 1;
                }
                FreeEnvironmentStrings(esp);
            }

            // Then copy new evars if nonempty
            for(const auto & ev : new_env_vars) {
                if (!ev.second) continue;
                std::string val = ev.second.get()->data();
                // Check if the destination buffer has enough room.
                if (new_envp + ev.first.length() + 1 + val.length() + 1 > new_env.get() + env_buf_size - 1) break;
                new_envp = std::copy(ev.first.cbegin(), ev.first.cend(), new_envp);
                *new_envp++ = '=';
                new_envp = std::copy(val.cbegin(), val.cend(), new_envp);
                *new_envp++ = '\0';
            }
        }

        *new_envp = '\0';
    }

    // Create the child process.
    bool bSuccess = CreateProcess(
        // Passing `program` here should be more robust, but would require adding a `.exe` extension
        // and searching through `PATH` where necessary
        NULL,
        const_cast<char *>(command.c_str()), // command line
        NULL,                                // process security attributes
        NULL,                                // primary thread security attributes
        TRUE,                                // handles are inherited
        0,                                   // creation flags
        new_env.get(),                       // new environment
        cwd ? cwd.get()->data() : NULL,      // current directory
        &siStartInfo,                        // STARTUPINFO pointer
        &piProcInfo);                        // receives PROCESS_INFORMATION

    if (!bSuccess) {
        throw std::system_error(GetLastError(), std::system_category());
    }

    // Close handle to primary thread, we don't need it.
    CloseHandle(piProcInfo.hThread);

    if (stdin_mode  == stdio::PIPED) CloseHandle(child_stdin);
    if (stdout_mode == stdio::PIPED) CloseHandle(child_stdout);
    if (stderr_mode == stdio::PIPED) CloseHandle(child_stderr);

    object_ref r = mk_cnstr(0, parent_stdin, parent_stdout, parent_stderr, wrap_win_handle(piProcInfo.hProcess));
    return lean_io_result_mk_ok(r.steal());
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_take_stdin(b_obj_arg, obj_arg lchild) {
    object_ref child(lchild);
    object_ref child2 = mk_cnstr(0, object_ref(box(0)), cnstr_get_ref(child, 1), cnstr_get_ref(child, 2), cnstr_get_ref(child, 3));
    object_ref r = mk_cnstr(0, cnstr_get_ref(child, 0), child2);
    return lean_io_result_mk_ok(r.steal());
}

void initialize_process() {
    g_win_handle_external_class = lean_register_external_class(win_handle_finalizer, win_handle_foreach);
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

extern "C" LEAN_EXPORT obj_res lean_io_process_child_wait(b_obj_arg, b_obj_arg child) {
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
    int status;
    if (waitpid(pid, &status, 0) == -1) {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
    if (WIFEXITED(status)) {
        return lean_io_result_mk_ok(box_uint32(static_cast<unsigned>(WEXITSTATUS(status))));
    } else {
        lean_assert(WIFSIGNALED(status));
        // use bash's convention
        return lean_io_result_mk_ok(box_uint32(128 + static_cast<unsigned>(WTERMSIG(status))));
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_try_wait(b_obj_arg, b_obj_arg child) {
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
    int status;
    int ret = waitpid(pid, &status, WNOHANG);
    if (ret == -1) {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    } else if (ret == 0) {
        return io_result_mk_ok(mk_option_none());
    } else {
        if (WIFEXITED(status)) {
            obj_res output = box_uint32(static_cast<unsigned>(WEXITSTATUS(status)));
            return lean_io_result_mk_ok(mk_option_some(output));
        } else {
            lean_assert(WIFSIGNALED(status));
            // use bash's convention
            obj_res output = box_uint32(128 + static_cast<unsigned>(WTERMSIG(status)));
            return lean_io_result_mk_ok(mk_option_some(output));
        }
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_kill(b_obj_arg, b_obj_arg child) {
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
    bool setsid = cnstr_get_uint8(child, 3 * sizeof(object *) + sizeof(pid_t));
    if ((setsid ? killpg(pid, SIGKILL) : kill(pid, SIGKILL)) == -1) {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
    return lean_io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_obj_arg, b_obj_arg child) {
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
    return pid;
}

struct pipe { int m_read_fd; int m_write_fd; };

static optional<pipe> setup_stdio(stdio cfg) {
    /* Setup stdio based on process configuration. */
    switch (cfg) {
    case stdio::INHERIT:
        /* We should need to do nothing in this case */
        return optional<pipe>();
    case stdio::PIPED:
        int fds[2];
#ifdef __APPLE__
        // this is inherently racy, but there is nothing we can do on MacOS
        if (::pipe(fds) == -1) { throw errno; }
        if (::fcntl(fds[0], F_SETFD, FD_CLOEXEC)) { throw errno; }
        if (::fcntl(fds[1], F_SETFD, FD_CLOEXEC)) { throw errno; }
#else
        if (::pipe2(fds, O_CLOEXEC) == -1) { throw errno; }
#endif
        return optional<pipe>(pipe { fds[0], fds[1] });
    case stdio::NUL:
        /* We should map /dev/null. */
        return optional<pipe>();
    }
    lean_unreachable();
}

extern "C" char **environ;

/* `posix_spawn_file_actions_addchdir_np` is glibc >= 2.29 / macOS >= 10.15; resolve it at run time so a binary
   built against an older libc still runs (and falls back to `fork` when a `cwd` is requested). */
typedef int (*addchdir_np_fn)(posix_spawn_file_actions_t *, char const *);
static addchdir_np_fn get_posix_spawn_addchdir() {
    static addchdir_np_fn fn = reinterpret_cast<addchdir_np_fn>(dlsym(RTLD_DEFAULT, "posix_spawn_file_actions_addchdir_np"));
    return fn;
}

/* The environment of the child as a private array: the parent's (if `inherit_env`), then the `set`/`unset`
   entries applied in order. */
static void build_child_env(array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & env, bool inherit_env,
                            buffer<char *> & out) {
    if (inherit_env && environ) {
        for (char ** e = environ; *e; e++) out.push_back(strdup(*e));
    }
    for (auto & entry : env) {
        char const * key = entry.fst().data();
        size_t klen = strlen(key);
        size_t j = 0;
        for (size_t k = 0; k < out.size(); k++) {
            if (strncmp(out[k], key, klen) == 0 && out[k][klen] == '=') free(out[k]);
            else out[j++] = out[k];
        }
        out.shrink(j);
        if (entry.snd()) {
            char const * v = entry.snd().get()->data();
            char * kv = static_cast<char *>(malloc(klen + 1 + strlen(v) + 1));
            memcpy(kv, key, klen); kv[klen] = '='; strcpy(kv + klen + 1, v);
            out.push_back(kv);
        }
    }
    out.push_back(nullptr);
}

static void free_strv(buffer<char *> & v) {
    for (char * p : v) if (p) free(p);
}

static obj_res mk_child(optional<pipe> const & stdin_pipe, optional<pipe> const & stdout_pipe,
                        optional<pipe> const & stderr_pipe, pid_t pid, bool do_setsid) {
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
    object_ref r = mk_cnstr(0, parent_stdin, parent_stdout, parent_stderr, sizeof(pid_t) + sizeof(uint8_t));
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    cnstr_set_uint32(r.raw(), 3 * sizeof(object *), pid);
    cnstr_set_uint8(r.raw(), 3 * sizeof(object *) + sizeof(pid_t), do_setsid);
    return lean_io_result_mk_ok(r.steal());
}

/*
Spawn with `posix_spawnp` (glibc: `clone(CLONE_VM|CLONE_VFORK)`) instead of `fork`.

`fork` duplicates the page tables of the parent while holding its mm lock for writing, and every other thread
of the parent that page-faults meanwhile waits for (or spins on) that lock. For a large, heavily threaded
parent such as `lake`, which spawns one `lean` per module, that dominates the parent's own CPU time and stalls
its other threads; `posix_spawn` copies nothing.

Returns `false` (nothing spawned) when this path is unavailable, i.e. a `cwd` was requested but
`posix_spawn_file_actions_addchdir_np` is not provided by the C library; the caller then forks.
*/
static bool spawn_posix(buffer<char *> & pargs, stdio stdin_mode, stdio stdout_mode, stdio stderr_mode,
  option_ref<string_ref> const & cwd, array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & env,
  bool inherit_env, bool do_setsid, obj_res & result) {
    if (cwd && !get_posix_spawn_addchdir()) return false;

    auto stdin_pipe  = setup_stdio(stdin_mode);
    auto stdout_pipe = setup_stdio(stdout_mode);
    auto stderr_pipe = setup_stdio(stderr_mode);

    buffer<char *> penv;
    build_child_env(env, inherit_env, penv);

    posix_spawn_file_actions_t fa;
    posix_spawn_file_actions_init(&fa);
    if (stdin_pipe) posix_spawn_file_actions_adddup2(&fa, stdin_pipe->m_read_fd, STDIN_FILENO);
    else if (stdin_mode == stdio::NUL) posix_spawn_file_actions_addopen(&fa, STDIN_FILENO, "/dev/null", O_RDONLY, 0);
    if (stdout_pipe) posix_spawn_file_actions_adddup2(&fa, stdout_pipe->m_write_fd, STDOUT_FILENO);
    else if (stdout_mode == stdio::NUL) posix_spawn_file_actions_addopen(&fa, STDOUT_FILENO, "/dev/null", O_WRONLY, 0);
    if (stderr_pipe) posix_spawn_file_actions_adddup2(&fa, stderr_pipe->m_write_fd, STDERR_FILENO);
    else if (stderr_mode == stdio::NUL) posix_spawn_file_actions_addopen(&fa, STDERR_FILENO, "/dev/null", O_WRONLY, 0);
    // the pipe descriptors themselves are O_CLOEXEC (or FD_CLOEXEC): closed in the child by the exec
    if (cwd) get_posix_spawn_addchdir()(&fa, cwd.get()->data());

    posix_spawnattr_t attr;
    posix_spawnattr_init(&attr);
    if (do_setsid) posix_spawnattr_setflags(&attr, POSIX_SPAWN_SETSID);

    pid_t pid = 0;
    int rc = posix_spawnp(&pid, pargs[0], &fa, &attr, pargs.data(), penv.data());
    posix_spawn_file_actions_destroy(&fa);
    posix_spawnattr_destroy(&attr);
    free_strv(penv);
    if (rc != 0) {
        // the command could not be executed: an `IO.Error` (the `fork` path printed to stderr and exited 255)
        if (stdin_pipe)  { close(stdin_pipe->m_read_fd);  close(stdin_pipe->m_write_fd); }
        if (stdout_pipe) { close(stdout_pipe->m_read_fd); close(stdout_pipe->m_write_fd); }
        if (stderr_pipe) { close(stderr_pipe->m_read_fd); close(stderr_pipe->m_write_fd); }
        throw rc;
    }
    result = mk_child(stdin_pipe, stdout_pipe, stderr_pipe, pid, do_setsid);
    return true;
}

static obj_res spawn(string_ref const & proc_name, array_ref<string_ref> const & args, stdio stdin_mode, stdio stdout_mode,
  stdio stderr_mode, option_ref<string_ref> const & cwd, array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & env,
  bool inherit_env, bool do_setsid) {
    // It is crucial to not allocate between `fork` and `execvp` for ASAN to work.
    buffer<char *> pargs;
    pargs.push_back(strdup(proc_name.data()));
    for (auto & arg : args)
        pargs.push_back(strdup(arg.data()));
    pargs.push_back(NULL);

    {
        obj_res result = nullptr;
        bool spawned;
        try {
            spawned = spawn_posix(pargs, stdin_mode, stdout_mode, stderr_mode, cwd, env, inherit_env, do_setsid, result);
        } catch (...) {
            free_strv(pargs);
            throw;
        }
        if (spawned) {
            free_strv(pargs);
            return result;
        }
    }

    /* Setup stdio based on process configuration (the `fork` fallback). */
    auto stdin_pipe  = setup_stdio(stdin_mode);
    auto stdout_pipe = setup_stdio(stdout_mode);
    auto stderr_pipe = setup_stdio(stderr_mode);

    int pid = fork();

    if (pid == 0) {
        if (!inherit_env) {
#ifdef __APPLE__
            environ = NULL;
#else
            clearenv();
#endif
        }
        for (auto & entry : env) {
            if (entry.snd()) {
                setenv(entry.fst().data(), entry.snd().get()->data(), true);
            } else {
                unsetenv(entry.fst().data());
            }
        }

        if (stdin_pipe) {
            dup2(stdin_pipe->m_read_fd, STDIN_FILENO);
            close(stdin_pipe->m_write_fd);
        } else if (stdin_mode == stdio::NUL) {
            int fd = open("/dev/null", O_RDONLY);
            dup2(fd, STDIN_FILENO);
        }

        if (stdout_pipe) {
            dup2(stdout_pipe->m_write_fd, STDOUT_FILENO);
            close(stdout_pipe->m_read_fd);
        } else if (stdout_mode == stdio::NUL) {
            int fd = open("/dev/null", O_WRONLY);
            dup2(fd, STDOUT_FILENO);
        }

        if (stderr_pipe) {
            dup2(stderr_pipe->m_write_fd, STDERR_FILENO);
            close(stderr_pipe->m_read_fd);
        } else if (stderr_mode == stdio::NUL) {
            int fd = open("/dev/null", O_WRONLY);
            dup2(fd, STDERR_FILENO);
        }

        if (cwd) {
            if (chdir(cwd.get()->data()) < 0) {
                std::cerr << "could not change directory to " << cwd.get()->data() << std::endl;
                // Use `_exit` rather than `exit` to avoid flushing stdio buffers that were
                // inherited from the parent via `fork`. Those buffers share the underlying
                // file descriptors with the parent, so flushing them here would duplicate
                // the parent's buffered writes in any file it had open for writing.
                _exit(-1);
            }
        }

        if (do_setsid) {
            lean_always_assert(setsid() >= 0);
        }

        if (execvp(pargs[0], pargs.data()) < 0) {
            std::cerr << "could not execute external process '" << pargs[0] << "'" << std::endl;
            // See the comment above about `_exit` vs `exit`.
            _exit(-1);
        }
    } else if (pid == -1) {
        throw errno;
    }

    for (char* parg : pargs) {
        if (parg != NULL) {
            free(parg);
        }
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

    object_ref r = mk_cnstr(0, parent_stdin, parent_stdout, parent_stderr, sizeof(pid_t) + sizeof(uint8_t));
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    cnstr_set_uint32(r.raw(), 3 * sizeof(object *), pid);
    cnstr_set_uint8(r.raw(), 3 * sizeof(object *) + sizeof(pid_t), do_setsid);
    return lean_io_result_mk_ok(r.steal());
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_take_stdin(b_obj_arg, obj_arg lchild) {
    object_ref child(lchild);
    object_ref child2 = mk_cnstr(0, object_ref(box(0)), cnstr_get_ref(child, 1), cnstr_get_ref(child, 2), sizeof(pid_t));
    cnstr_set_uint32(child2.raw(), 3 * sizeof(object *), cnstr_get_uint32(child.raw(), 3 * sizeof(object *)));
    object_ref r = mk_cnstr(0, cnstr_get_ref(child, 0), child2);
    return lean_io_result_mk_ok(r.steal());
}

void initialize_process() {}
void finalize_process() {}

#endif

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
