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
#include "util/name.h"
#include "util/optional.h"

namespace lean {
#if defined(LEAN_WINDOWS)
// Windows version
#include <windows.h>
static char g_path_sep     = ';';
static char g_sep          = '\\';
static char g_bad_sep      = '/';
static std::string get_exe_location() {
    HMODULE hModule = GetModuleHandleW(NULL);
    WCHAR path[MAX_PATH];
    GetModuleFileNameW(hModule, path, MAX_PATH);
    std::wstring pathstr(path);
    return std::string(pathstr.begin(), pathstr.end());
}
#elif defined(__APPLE__)
// OSX version
#include <mach-o/dyld.h>
#include <limits.h>
static char g_path_sep     = ':';
static char g_sep          = '/';
static char g_bad_sep      = '\\';
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
#include <string.h>
#include <sys/stat.h>
#include <limits.h> // NOLINT
#include <stdio.h>
static char g_path_sep     = ':';
static char g_sep          = '/';
static char g_bad_sep      = '\\';
static std::string get_exe_location() {
    char path[PATH_MAX];
    char dest[PATH_MAX];
    memset(dest, 0, PATH_MAX);
    pid_t pid = getpid();
    snprintf(path, PATH_MAX, "/proc/%d/exe", pid);
    if (readlink(path, dest, PATH_MAX) == -1) {
        throw exception("failed to locate Lean executable location");
    } else {
        return std::string(dest);
    }
}
#endif

#if defined(LEAN_CYGWIN)
/**
   \brief Cleanup path when using cygwin.
   This procedure performs two fixes, if the string contains '/'.

   1- It replaces '/' with '\\' and ':' with ';'

   2- Then, it replaces "\cygdrive\c\" with "c:"
*/
static std::string fix_cygwin_path(std::string f) {
    if (f.find('/') != std::string::npos) {
        // Step 1.
        for (auto & c : f) {
            if (c == g_bad_sep)
                c = g_sep;
            else if (c == ':')
                c = g_path_sep;
        }
        // Step 2.
        size_t pos = 0;
        size_t matchpos;
        std::string cygdrive("\\cygdrive\\");
        while ((matchpos = f.find(cygdrive, pos)) != std::string::npos) {
            // erase "\cygdrive\"
            f = f.replace(matchpos, cygdrive.size(), "");
            // replace the next "\" with ":\"
            if ((matchpos = f.find("\\", matchpos)) != std::string::npos) {
                f.replace(matchpos, 1, ":\\");
            }
            pos = matchpos;
        }
    }
    return f;
}
#endif

std::string normalize_path(std::string f) {
#if defined(LEAN_CYGWIN)
    f = fix_cygwin_path(f);
#else
    for (auto & c : f) {
        if (c == g_bad_sep)
            c = g_sep;
    }
#endif
    return f;
}

std::string get_path(std::string f) {
    while (true) {
        if (f.empty())
            throw exception("failed to locate Lean executable location");
        if (f.back() == g_sep) {
            f.pop_back();
            return f;
        }
        f.pop_back();
    }
}

static std::string              g_lean_path;
static std::vector<std::string> g_lean_path_vector;
void init_lean_path(char const * kernel_instance_name) {
    char * r = getenv("LEAN_PATH");
    if (r == nullptr) {
        g_lean_path  = ".";
        std::string exe_path = get_path(get_exe_location());
        g_lean_path += g_path_sep;
        g_lean_path += exe_path + g_sep + ".." + g_sep + "library" + g_sep + kernel_instance_name;
        g_lean_path += g_path_sep;
        g_lean_path += exe_path;
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

struct init_lean_path_fn {
    init_lean_path_fn() { init_lean_path("standard"); }
};
static init_lean_path_fn g_init_lean_path_fn;
static std::string       g_sep_str(1, g_sep);

bool has_file_ext(std::string const & fname, char const * ext) {
    unsigned ext_len = strlen(ext);
    return fname.size() > ext_len && fname.substr(fname.size() - ext_len, ext_len) == ext;
}

bool is_lean_file(std::string const & fname) {
    return has_file_ext(fname, ".lean");
}

bool is_olean_file(std::string const & fname) {
    return has_file_ext(fname, ".olean");
}

bool is_lua_file(std::string const & fname) {
    return has_file_ext(fname, ".lua");
}

bool is_known_file_ext(std::string const & fname) {
    return is_lean_file(fname) || is_olean_file(fname) || is_lua_file(fname);
}

optional<std::string> check_file(std::string const & path, std::string const & fname, char const * ext = nullptr) {
    std::string file = path + g_sep + fname;
    if (ext)
        file += ext;
    std::ifstream ifile(file);
    if (ifile)
        return optional<std::string>(file);
    else
        return optional<std::string>();
}

std::string name_to_file(name const & fname) {
    return fname.to_string(g_sep_str.c_str());
}

std::string find_file(std::string fname, std::initializer_list<char const *> const & extensions) {
    bool is_known = is_known_file_ext(fname);
    fname = normalize_path(fname);
    for (auto path : g_lean_path_vector) {
        if (is_known) {
            if (auto r = check_file(path, fname))
                return *r;
        } else {
            for (auto ext : extensions) {
                if (auto r = check_file(path, fname, ext))
                    return *r;
            }
        }
    }
    throw exception(sstream() << "file '" << fname << "' not found in the LEAN_PATH");
}

std::string find_file(std::string fname) {
    return find_file(fname, {".olean", ".lean", ".lua"});
}

std::string find_file(name const & fname) {
    return find_file(fname.to_string(g_sep_str.c_str()));
}

std::string find_file(name const & fname, std::initializer_list<char const *> const & exts) {
    return find_file(fname.to_string(g_sep_str.c_str()), exts);
}

char const * get_lean_path() {
    return g_lean_path.c_str();
}
}
