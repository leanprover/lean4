/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#if defined(LEAN_CYGWIN)
#if defined(__STRICT_ANSI__)
// hack for using realpath on cygwin
#undef __STRICT_ANSI__
#endif
#endif

#include <string>
#include <cstdlib>
#include "util/realpath.h"

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
#include <windows.h>
#endif

namespace lean {
std::string lrealpath(char const * fname) {
#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
    constexpr unsigned BufferSize = 8192;
    char buffer[BufferSize];
    DWORD retval = GetFullPathName(fname, BufferSize, buffer, nullptr);
    if (retval == 0 || retval > BufferSize) {
        return std::string(fname);
    } else {
        return std::string(buffer);
    }
#else
    char * tmp = realpath(fname, nullptr);
    std::string r(tmp);
    free(tmp);
    return r;
#endif
}
}
