/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <cstdlib>
#include <fstream>
#include <vector>
#include "util/exception.h"
#include "util/sstream.h"

namespace lean {
#if defined(LEAN_WINDOWS)
// Windows version
#include <windows.h>
static char g_path_sep = ';';
static char g_sep      = '\\';
static char g_bad_sep  = '/';
static std::string get_exe_location() {
    HMODULE hModule = GetModuleHandleW(NULL);
    WCHAR path[MAX_PATH];
    GetModuleFileNameW(hModule, path, MAX_PATH);
    std::wstring pathstr(path);
    std::string r(pathstr.begin(), pathstr.end());
    while (true) {
        if (r.empty())
            throw exception("failed to locate Lean executable location");
        if (r.back() == g_sep) {
            r.pop_back();
            return r;
        }
        r.pop_back();
    }
}
#elif defined(__APPLE__)
// OSX version
#include <mach-o/dyld.h>
#include <limits.h>
static char g_path_sep = ':';
static char g_sep      = '/';
static char g_bad_sep  = '\\';
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
static char g_path_sep = ':';
static char g_sep      = '/';
static char g_bad_sep  = '\\';
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

std::string normalize_path(std::string f) {
    for (auto & c : f) {
        if (c == g_bad_sep)
            c = g_sep;
    }
    return f;
}

static std::string              g_lean_path;
static std::vector<std::string> g_lean_path_vector;
struct init_lean_path {
    init_lean_path() {
        char * r = getenv("LEAN_PATH");
        if (r == nullptr) {
            g_lean_path  = ".";
            g_lean_path += g_path_sep;
            g_lean_path += get_exe_location();
        } else {
            g_lean_path = r;
        }
        g_lean_path = normalize_path(g_lean_path);
        unsigned i  = 0;
        unsigned j  = 0;
        unsigned sz = g_lean_path.size();
        for (; j < sz; j++) {
            if (g_lean_path[j] == g_path_sep) {
                if (j > i)
                    g_lean_path_vector.push_back(g_lean_path.substr(i, j - i));
                i = j + 1;
            }
        }
        if (j > i)
            g_lean_path_vector.push_back(g_lean_path.substr(i, j - i));
    }
};
static init_lean_path g_init_lean_path;

std::string find_file(char const * fname) {
    std::string nfname = normalize_path(std::string(fname));
    for (auto path : g_lean_path_vector) {
        std::string file = path + g_sep + nfname;
        std::ifstream ifile(file);
        if (ifile)
            return file;
    }
    throw exception(sstream() << "file '" << fname << "' not found in the LEAN_PATH");
}

char const * get_lean_path() {
    return g_lean_path.c_str();
}
}
