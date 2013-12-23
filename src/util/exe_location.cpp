/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/exception.h"

namespace lean {
static std::string g_exe_location;
#if defined(LEAN_WINDOWS)
// Windows version
#include <windows.h>
static void init_exe_location() {
    HMODULE hModule = GetModuleHandleW(NULL);
    WCHAR path[MAX_PATH];
    GetModuleFileNameW(hModule, path, MAX_PATH);
    g_exe_location = path;
}
#elif defined(__APPLE__)
// OSX version
#include <mach-o/dyld.h>
#include <limits.h>
static void init_exe_location() {
    char buf[PATH_MAX];
    uint32_t bufsize = PATH_MAX;
    if (_NSGetExecutablePath(buf, &bufsize) != 0)
        throw exception("failed to locate Lean executable location");
    g_exe_location = buf;
}
#else
// Linux version
#include <sys/types.h>
#include <unistd.h>
#include <sys/stat.h>
#include <limits.h> // NOLINT
#include <stdio.h>
static void init_exe_location() {
    char path[PATH_MAX];
    char dest[PATH_MAX];
    pid_t pid = getpid();
    snprintf(path, PATH_MAX, "/proc/%d/exe", pid);
    if (readlink(path, dest, PATH_MAX) == -1) {
        throw exception("failed to locate Lean executable location");
    } else {
        g_exe_location = dest;
    }
}
#endif
struct init_exe_location_proc {
    init_exe_location_proc() { init_exe_location(); }
};
static init_exe_location_proc g_init_exe_location_proc;
char const * get_exe_location() {
    return g_exe_location.c_str();
}
}
