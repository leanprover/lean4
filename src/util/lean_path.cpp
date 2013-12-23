/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <cstdlib>
#include "util/exception.h"

namespace lean {
#if defined(LEAN_WINDOWS)
// Windows version
#include <windows.h>
static std::string get_exe_location() {
    HMODULE hModule = GetModuleHandleW(NULL);
    WCHAR path[MAX_PATH];
    GetModuleFileNameW(hModule, path, MAX_PATH);
    return std::string(path);
}
#elif defined(__APPLE__)
// OSX version
#include <mach-o/dyld.h>
#include <limits.h>
static std::string get_exe_location() {
    char buf[PATH_MAX];
    uint32_t bufsize = PATH_MAX;
    if (_NSGetExecutablePath(buf, &bufsize) != 0)
        throw exception("failed to locate Lean executable location");
    return std::string(buf);
}
#else
// Linux version
#include <sys/types.h>
#include <unistd.h>
#include <sys/stat.h>
#include <limits.h> // NOLINT
#include <stdio.h>
static std::string get_exe_location() {
    char path[PATH_MAX];
    char dest[PATH_MAX];
    pid_t pid = getpid();
    snprintf(path, PATH_MAX, "/proc/%d/exe", pid);
    if (readlink(path, dest, PATH_MAX) == -1) {
        throw exception("failed to locate Lean executable location");
    } else {
        return std::string(dest);
    }
}
#endif
static std::string g_lean_path;
struct init_lean_path {
    init_lean_path() {
        char * r = getenv("LEAN_PATH");
        if (r == nullptr)
            g_lean_path = get_exe_location();
        else
            g_lean_path = r;
    }
};
static init_lean_path g_init_lean_path;
char const * get_lean_path() {
    return g_lean_path.c_str();
}
}
