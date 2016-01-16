/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <sys/file.h>
#include <errno.h>
#include "util/exception.h"
#include "util/sstream.h"
#include "util/file_lock.h"

#ifdef LEAN_WINDOWS
#include <windows.h>
#include <io.h>
#define   LOCK_SH   1    /* shared lock */
#define   LOCK_EX   2    /* exclusive lock */
#define   LOCK_NB   4    /* don't block when locking */
#define   LOCK_UN   8    /* unlock */

static BOOL lock(HANDLE h, int non_blocking, int exclusive) {
    DWORD lower, upper;
    OVERLAPPED ovlp;
    int flags = 0;

    lower = GetFileSize(h, &upper);
    memset (&ovlp, 0, sizeof(ovlp));

    if (non_blocking)
        flags |= LOCKFILE_FAIL_IMMEDIATELY;
    if (exclusive)
        flags |= LOCKFILE_EXCLUSIVE_LOCK;

    return LockFileEx(h, flags, 0, lower, upper, &ovlp);
}

static BOOL unlock(HANDLE h) {
    DWORD lower, upper;
    lower = GetFileSize(h, &upper);
    return UnlockFile(h, 0, 0, lower, upper);
}

int flock(int fd, int op) {
    HANDLE h = (HANDLE)_get_osfhandle(fd);
    DWORD res;
    int non_blocking;

    if (h == INVALID_HANDLE_VALUE)
        return -1;

    non_blocking = op & LOCK_NB;
    op          &= ~LOCK_NB;

    switch (op) {
    case LOCK_SH:
        res = lock(h, non_blocking, 0);
        break;
    case LOCK_EX:
        res = lock(h, non_blocking, 1);
        break;
    case LOCK_UN:
        res = unlock(h);
        break;
    default:
        return -1;
    }
    return !res ? -1 : 0;
}
#else
#include <unistd.h>
#include <fcntl.h>
#endif

namespace lean {
file_lock::file_lock(char const * fname, bool exclusive):
    m_fname(fname), m_fd(-1) {
    m_fname += ".lock";
    m_fd = open(m_fname.c_str(), O_CREAT, 0xFFFF);
    if (m_fd == -1) {
        if (errno == EACCES || errno == EROFS) {
            // We don't have permission to create the file, the folder containing fname is probably readonly.
            // fname is probably part of the Lean installation in a system directory.
            // So, we ignore the file_lock in this case.
        } else {
            throw exception(sstream() << "failed to lock file '" << fname << "'");
        }
    } else {
        int status = flock(m_fd, exclusive ? LOCK_EX : LOCK_SH);
        if (status == -1)
            throw exception(sstream() << "failed to lock file '" << fname << "'");
    }
}
file_lock::~file_lock() {
    if (m_fd != -1) {
        std::remove(m_fname.c_str());
        flock(m_fd, LOCK_UN);
        close(m_fd);
    }
}
}
