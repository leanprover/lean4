/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/exception.h"
#include "util/sstream.h"
#include "util/file_lock.h"
#ifdef _WINDOWS
namespace lean {
file_lock::file_lock(char const *, bool) {
    // TODO(Leo):
}
file_lock::~file_lock() {
}
}
#else
#include <unistd.h>
#include <sys/file.h>
namespace lean {
file_lock::file_lock(char const * fname, bool exclusive):
    m_fname(fname), m_fd(-1) {
    m_fname += ".lock";
    m_fd = open(m_fname.c_str(), O_CREAT, 0xFFFF);
    if (m_fd == -1)
        throw exception(sstream() << "failed to lock file '" << fname << "'");
    int status = flock(m_fd, exclusive ? LOCK_EX : LOCK_SH);
    // TODO(Leo): should we use a loop and keep checking, and fail after k seconds?
    if (status == -1)
        throw exception(sstream() << "failed to lock file '" << fname << "'");
}
file_lock::~file_lock() {
    if (m_fd != -1) {
        std::remove(m_fname.c_str());
        flock(m_fd, LOCK_UN);
        close(m_fd);
    }
}
}
#endif
