/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include <string>

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
typedef void* HANDLE;
#else
#endif

namespace lean  {

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)

struct pipe {
    HANDLE m_read_fd;
    HANDLE m_write_fd;
    pipe();
    pipe(HANDLE read_fd, HANDLE write_fd) :
        m_read_fd(read_fd), m_write_fd(write_fd) {}
    pipe(pipe const & p) :
        m_read_fd(p.m_read_fd), m_write_fd(p.m_write_fd) {}
};
#else
struct pipe {
    int m_read_fd;
    int m_write_fd;
    pipe();
    pipe(int read_fd, int write_fd) :
        m_read_fd(read_fd), m_write_fd(write_fd) {}
    pipe(pipe const & p) :
        m_read_fd(p.m_read_fd), m_write_fd(p.m_write_fd) {}
};

#endif

}
