/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <cstdlib>
#include "util/realpath.h"

#ifdef LEAN_WINDOWS
#include <windows.h>
#endif

namespace lean {
std::string lrealpath(char const * fname) {
#ifdef LEAN_WINDOWS
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
