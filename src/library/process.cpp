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

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
#include <windows.h>
#include <Fcntl.h>
#include <io.h>
#include <tchar.h>
#include <stdio.h>
#include <strsafe.h>
#else
#include <unistd.h>
#include <sys/wait.h>
#endif

#include "library/process.h"
#include "util/buffer.h"
#include "library/pipe.h"

namespace lean {

process::process(std::string n, stdio io_stdin, stdio io_stdout, stdio io_stderr):
    m_proc_name(n), m_stdout(io_stdout), m_stdin(io_stdin), m_stderr(io_stderr) {
    m_args.push_back(m_proc_name);
}

process & process::arg(std::string a) {
    m_args.push_back(a);
    return *this;
}

process & process::set_cwd(std::string const &cwd) {
    m_cwd = cwd;
    return *this;
}

process & process::set_env(std::string const & var, optional<std::string> const & val) {
    m_env[var] = val;
    return *this;
}

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)

struct windows_child : public child {
    handle_ref m_stdin;
    handle_ref m_stdout;
    handle_ref m_stderr;
    HANDLE m_process;

    windows_child(HANDLE p, handle_ref hstdin, handle_ref hstdout, handle_ref hstderr) :
            m_stdin(hstdin), m_stdout(hstdout), m_stderr(hstderr), m_process(p) {}

    ~windows_child() {
        CloseHandle(m_process);
    }

    handle_ref get_stdin() override { return m_stdin; }
    handle_ref get_stdout() override { return m_stdout; }
    handle_ref get_stderr() override { return m_stderr; }

    unsigned wait() override {
        DWORD exit_code;
        WaitForSingleObject(m_process, INFINITE);
        GetExitCodeProcess(m_process, &exit_code);
        return static_cast<unsigned>(exit_code);
    }
};

// static HANDLE to_win_handle(FILE * file) {
//     intptr_t handle = _get_osfhandle(fileno(file));
//     return reinterpret_cast<HANDLE>(handle);
// }

static FILE * from_win_handle(HANDLE handle, char const * mode) {
    int fd = _open_osfhandle(reinterpret_cast<intptr_t>(handle), _O_APPEND);
    return fdopen(fd, mode);
}

static HANDLE create_child_process(std::string cmd_name, optional<std::string> const & cwd,
    std::unordered_map<std::string, optional<std::string>> const & env,
    HANDLE hstdin, HANDLE hstdout, HANDLE hstderr);

// TODO(@jroesch): unify this code between platforms better.
static optional<pipe> setup_stdio(SECURITY_ATTRIBUTES * saAttr, HANDLE * handle, bool in, stdio cfg) {
    /* Setup stdio based on process configuration. */
    switch (cfg) {
    case stdio::INHERIT:
        lean_always_assert(DuplicateHandle(GetCurrentProcess(), *handle,
                                           GetCurrentProcess(), handle,
                                           0, TRUE, DUPLICATE_SAME_ACCESS));
        return optional<pipe>();
    case stdio::PIPED: {
        HANDLE readh;
        HANDLE writeh;
        if (!CreatePipe(&readh, &writeh, saAttr, 0))
            throw new exception("unable to create pipe");
        auto pipe = lean::pipe(readh, writeh);
        auto ours = in ? pipe.m_write_fd : pipe.m_read_fd;
        auto theirs = in ? pipe.m_read_fd : pipe.m_write_fd;
        lean_always_assert(SetHandleInformation(ours, HANDLE_FLAG_INHERIT, 0));
        *handle = theirs;
        return optional<lean::pipe>(pipe);
    }
    case stdio::NUL:
        /* We should map /dev/null. */
        return optional<pipe>();
    }
    lean_unreachable();
}

// This code is adapted from: https://msdn.microsoft.com/en-us/library/windows/desktop/ms682499(v=vs.85).aspx
std::shared_ptr<child> process::spawn_core() {
    HANDLE child_stdin = GetStdHandle(STD_INPUT_HANDLE);
    HANDLE child_stdout = GetStdHandle(STD_OUTPUT_HANDLE);
    HANDLE child_stderr = GetStdHandle(STD_ERROR_HANDLE);

    SECURITY_ATTRIBUTES saAttr;

    // Set the bInheritHandle flag so pipe handles are inherited.
    saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
    saAttr.bInheritHandle = TRUE;
    saAttr.lpSecurityDescriptor = NULL;

    auto stdin_pipe = setup_stdio(&saAttr, &child_stdin, true, m_stdin);
    auto stdout_pipe = setup_stdio(&saAttr, &child_stdout, false, m_stdout);
    auto stderr_pipe = setup_stdio(&saAttr, &child_stderr, false, m_stderr);

    std::string command;

    // This needs some thought, on Windows we must pass a command string
    // which is a valid command, that is a fully assembled command to be executed.
    //
    // We must escape the arguments to preseving spacing and other characters,
    // we might need to revisit escaping here.
    bool once_through = false;
    for (auto arg : m_args) {
        if (once_through) {
            command += " \"";
        }
        command += arg;
        if (once_through) {
            command += "\"";
        }
        once_through = true;
    }

    // Create the child process.
    auto proc_handle =
        create_child_process(command, m_cwd, m_env, child_stdin, child_stdout, child_stderr);

    FILE * parent_stdin = nullptr, *parent_stdout = nullptr, *parent_stderr = nullptr;

    if (stdin_pipe) {
        CloseHandle(stdin_pipe->m_read_fd);
        parent_stdin = from_win_handle(stdin_pipe->m_write_fd, "w");
    }

    if (stdout_pipe) {
        CloseHandle(stdout_pipe->m_write_fd);
        parent_stdout = from_win_handle(stdout_pipe->m_read_fd, "r");
    }

    if (stderr_pipe) {
        CloseHandle(stderr_pipe->m_write_fd);
        parent_stderr = from_win_handle(stderr_pipe->m_read_fd, "r");
    }

    return std::make_shared<windows_child>(proc_handle,
        std::make_shared<handle>(parent_stdin),
        std::make_shared<handle>(parent_stdout),
        std::make_shared<handle>(parent_stderr));
}

static void set_env(std::string const & var, optional<std::string> const & val) {
    SetEnvironmentVariable(var.c_str(), val ? val->c_str() : NULL);
}

// Create a child process that uses the previously created pipes for STDIN and STDOUT.
static HANDLE create_child_process(std::string command, optional<std::string> const & cwd,
        std::unordered_map<std::string, optional<std::string>> const & env,
        HANDLE hstdin, HANDLE hstdout, HANDLE hstderr) {
    PROCESS_INFORMATION piProcInfo;
    STARTUPINFO siStartInfo;
    BOOL bSuccess = FALSE;

    // Set up members of the PROCESS_INFORMATION structure.
    ZeroMemory(&piProcInfo, sizeof(PROCESS_INFORMATION));

    // Set up members of the STARTUPINFO structure.
    // This structure specifies the STDIN and STDOUT handles for redirection.

    ZeroMemory(&siStartInfo, sizeof(STARTUPINFO));
    siStartInfo.cb = sizeof(STARTUPINFO);
    siStartInfo.hStdError = hstderr;
    siStartInfo.hStdOutput = hstdout;
    siStartInfo.hStdInput = hstdin;
    siStartInfo.dwFlags |= STARTF_USESTDHANDLES;

    // TODO(gabriel): this is thread-unsafe
    std::unordered_map<std::string, optional<std::string>> old_env_vars;
    for (auto & entry : env) {
        optional<std::string> old;
        if (auto old_val = getenv(entry.first.c_str()))
            old = std::string(old_val);
        old_env_vars[entry.first] = old;

        set_env(entry.first, entry.second);
    }

    // Create the child process.
    // std::cout << command << std::endl;
    bSuccess = CreateProcess(
        NULL,
        const_cast<char *>(command.c_str()), // command line
        NULL,                                // process security attributes
        NULL,                                // primary thread security attributes
        TRUE,                                // handles are inherited
        0,                                   // creation flags
        NULL,                                // use parent's environment
        cwd ? cwd->c_str() : NULL,           // current directory
        &siStartInfo,                        // STARTUPINFO pointer
        &piProcInfo);                        // receives PROCESS_INFORMATION

    for (auto & entry : old_env_vars) {
        set_env(entry.first, entry.second);
    }

    // If an error occurs, exit the application.
    if (!bSuccess) {
        throw exception("failed to start child process");
    } else {
        // Close handles to the child process and its primary thread.
        // Some applications might keep these handles to monitor the status
        // of the child process, for example.

        CloseHandle(piProcInfo.hThread);

        return piProcInfo.hProcess;
    }
}

#else

static optional<pipe> setup_stdio(stdio cfg) {
    /* Setup stdio based on process configuration. */
    switch (cfg) {
    case stdio::INHERIT:
        /* We should need to do nothing in this case */
        return optional<pipe>();
    case stdio::PIPED:
        return optional<pipe>(lean::pipe());
    case stdio::NUL:
        /* We should map /dev/null. */
        return optional<pipe>();
    }
    lean_unreachable();
}

struct unix_child : public child {
    handle_ref m_stdin;
    handle_ref m_stdout;
    handle_ref m_stderr;
    int m_pid;

    unix_child(int pid, handle_ref hstdin, handle_ref hstdout, handle_ref hstderr) :
            m_stdin(hstdin), m_stdout(hstdout), m_stderr(hstderr), m_pid(pid) {}

    handle_ref get_stdin() override { return m_stdin; }
    handle_ref get_stdout() override { return m_stdout; }
    handle_ref get_stderr() override { return m_stderr; }

    unsigned wait() override {
        int status;
        waitpid(m_pid, &status, 0);
        if (WIFEXITED(status)) {
            return static_cast<unsigned>(WEXITSTATUS(status));
        } else {
            lean_assert(WIFSIGNALED(status));
            // use bash's convention
            return 128 + static_cast<unsigned>(WTERMSIG(status));
        }
    }
};

std::shared_ptr<child> process::spawn_core() {
    /* Setup stdio based on process configuration. */
    auto stdin_pipe = setup_stdio(m_stdin);
    auto stdout_pipe = setup_stdio(m_stdout);
    auto stderr_pipe = setup_stdio(m_stderr);

    int pid = fork();

    if (pid == 0) {
        for (auto & entry : m_env) {
            if (auto val = entry.second) {
                setenv(entry.first.c_str(), val->c_str(), true);
            } else {
                unsetenv(entry.first.c_str());
            }
        }

        if (stdin_pipe) {
            dup2(stdin_pipe->m_read_fd, STDIN_FILENO);
            close(stdin_pipe->m_write_fd);
        }

        if (stdout_pipe) {
            dup2(stdout_pipe->m_write_fd, STDOUT_FILENO);
            close(stdout_pipe->m_read_fd);
        }

        if (stderr_pipe) {
            dup2(stderr_pipe->m_write_fd, STDERR_FILENO);
            close(stderr_pipe->m_read_fd);
        }

        if (m_cwd) {
            if (chdir(m_cwd->c_str()) < 0) {
                std::cerr << "could not change directory to " << *m_cwd << std::endl;
                exit(-1);
            }
        }

        buffer<char *> pargs;
        for (auto & arg : m_args)
            pargs.push_back(strdup(arg.c_str()));
        pargs.push_back(NULL);

        if (execvp(pargs[0], pargs.data()) < 0) {
            std::cerr << "could not execute external process" << std::endl;
            exit(-1);
        }
    } else if (pid == -1) {
        throw std::runtime_error("forking process failed: ...");
    }

    /* We want to setup the parent's view of the file descriptors. */
    FILE * parent_stdin = nullptr, * parent_stdout = nullptr, * parent_stderr = nullptr;

    if (stdin_pipe) {
        close(stdin_pipe->m_read_fd);
        parent_stdin = fdopen(stdin_pipe->m_write_fd, "w");
    }

    if (stdout_pipe) {
        close(stdout_pipe->m_write_fd);
        parent_stdout = fdopen(stdout_pipe->m_read_fd, "r");
    }

    if (stderr_pipe) {
        close(stderr_pipe->m_write_fd);
        parent_stderr = fdopen(stderr_pipe->m_read_fd, "r");
    }

    return std::make_shared<unix_child>(pid,
         std::make_shared<handle>(parent_stdin),
         std::make_shared<handle>(parent_stdout),
         std::make_shared<handle>(parent_stderr));
}

#endif

std::shared_ptr<child> process::spawn() {
    if (m_stdout == stdio::INHERIT) {
        std::cout.flush();
    }
    return spawn_core();
}

}
