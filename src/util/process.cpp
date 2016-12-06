/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include <unistd.h>
#include <sys/wait.h>
#include "util/process.h"
#include "util/buffer.h"

namespace lean {

// TODO(jroesch): make this cross platform

process::process(std::string n): m_proc_name(n), m_args() {
    m_args.push_back(m_proc_name);
}

process & process::arg(std::string a) {
    m_args.push_back(a);
    return *this;
}

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
void process::run() {
    throw std::runtime_error("process::run not supported on Windows")
}
#else

void process::run() {
    int pid = fork();
    if (pid == 0) {
        buffer<char*> pargs;

        for (auto arg : m_args) {
            auto str = new char[arg.size() + 1];
            arg.copy(str, arg.size());
            str[arg.size()] = '\0';
            pargs.push_back(str);
        }

        pargs.data()[pargs.size()] = NULL;

        auto err = execvp(pargs.data()[0], pargs.data());
        if (err < 0) {
            throw std::runtime_error("executing process failed: ...");
        }
    } else if (pid == -1) {
        throw std::runtime_error("forking process failed: ...");
    } else {
        int status;
        waitpid(pid, &status, 0);
    }
}
#endif

}
