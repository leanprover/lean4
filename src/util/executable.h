/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jay Freeman (Saurik), Jared Roesch
*/

#include <mach-o/dyld.h>

// TODO: this must be platform specific code
std::string executable() {
    uint32_t size(0);
    lean_assert(_NSGetExecutablePath(NULL, &size) == -1);
    std::string path;
    path.resize(size);
    lean_assert(_NSGetExecutablePath(&path[0], &size) != -1);
    lean_assert(path.back() == '\0');
    path.resize(strlen(path.c_str()));
    return path;
}
