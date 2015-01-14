/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
#include <windows.h>
#endif
#include <string>
#include <cstdlib>
#include <fstream>
#include <vector>
#include <sys/types.h>
#include <sys/stat.h>
#include "util/exception.h"
#include "util/sstream.h"
#include "util/name.h"
#include "util/optional.h"
#include "util/realpath.h"
#include "util/lean_path.h"

#ifndef LEAN_DEFAULT_MODULE_FILE_NAME
#define LEAN_DEFAULT_MODULE_FILE_NAME "default"
#endif

namespace lean {
file_not_found_exception::file_not_found_exception(std::string const & fname):
    exception(sstream() << "file '" << fname << "' not found in the LEAN_PATH"),
    m_fname(fname) {}

static std::string * g_default_file_name             = nullptr;
static std::string *              g_lean_path        = nullptr;
static std::vector<std::string> * g_lean_path_vector = nullptr;

bool is_directory(char const * pathname) {
    struct stat info;
    if (stat(pathname, &info) != 0 )
        return false; // failed to access pathname
    return info.st_mode & S_IFDIR;
}

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
// Windows version
static char g_path_sep     = ';';
static char g_path_alt_sep = ':';
static char g_sep          = '\\';
static char g_bad_sep      = '/';
static std::string get_exe_location() {
    HMODULE hModule = GetModuleHandleW(NULL);
    WCHAR path[MAX_PATH];
    GetModuleFileNameW(hModule, path, MAX_PATH);
    std::wstring pathstr(path);
    return std::string(pathstr.begin(), pathstr.end());
}
bool is_path_sep(char c) { return c == g_path_sep || c == g_path_alt_sep; }
#elif defined(__APPLE__)
// OSX version
#include <mach-o/dyld.h>
#include <limits.h>
#include <stdlib.h>
static char g_path_sep     = ':';
static char g_sep          = '/';
static char g_bad_sep      = '\\';
static std::string get_exe_location() {
    char buf1[PATH_MAX];
    char buf2[PATH_MAX];
    uint32_t bufsize = PATH_MAX;
    if (_NSGetExecutablePath(buf1, &bufsize) != 0)
        throw exception("failed to locate Lean executable location");
    if (!realpath(buf1, buf2))
        throw exception("failed to resolve symbolic links in " + std::string(buf1));
    return std::string(buf2);
}
bool is_path_sep(char c) { return c == g_path_sep; }
#else
// Linux version
#include <unistd.h>
#include <string.h>
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
bool is_path_sep(char c) { return c == g_path_sep; }
#endif

std::string normalize_path(std::string f) {
    for (auto & c : f) {
        if (c == g_bad_sep)
            c = g_sep;
    }
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

void init_lean_path(bool use_hott) {
#if defined(LEAN_EMSCRIPTEN)
    *g_lean_path = "/library";
    g_lean_path_vector->push_back(*g_lean_path);
#else
    char * r = nullptr;
    if (use_hott)
        r = getenv("HLEAN_PATH");
    else
        r = getenv("LEAN_PATH");
    if (r == nullptr) {
        std::string exe_path = get_path(get_exe_location());
        if (use_hott)
            *g_lean_path  = exe_path + g_sep + ".." + g_sep + "hott";
        else
            *g_lean_path  = exe_path + g_sep + ".." + g_sep + "library";
        *g_lean_path += g_path_sep;
        if (use_hott)
            *g_lean_path += exe_path + g_sep + ".." + g_sep + "lib" + g_sep + "lean" + g_sep + "hott";
        else
            *g_lean_path += exe_path + g_sep + ".." + g_sep + "lib" + g_sep + "lean" + g_sep + "library";
        *g_lean_path += g_path_sep;
        *g_lean_path += ".";
    } else {
        *g_lean_path = r;
    }
    g_lean_path_vector->clear();
    *g_lean_path = normalize_path(*g_lean_path);
    unsigned i  = 0;
    unsigned j  = 0;
    unsigned sz = g_lean_path->size();
    for (; j < sz; j++) {
        if (is_path_sep((*g_lean_path)[j])) {
            if (j > i)
                g_lean_path_vector->push_back(g_lean_path->substr(i, j - i));
            i = j + 1;
        }
    }
    if (j > i)
        g_lean_path_vector->push_back(g_lean_path->substr(i, j - i));
#endif
}

static char g_sep_str[2];

void initialize_lean_path(bool use_hott) {
    if (g_default_file_name != nullptr)
        finalize_lean_path();
    g_default_file_name = new std::string(LEAN_DEFAULT_MODULE_FILE_NAME);
    g_lean_path         = new std::string();
    g_lean_path_vector  = new std::vector<std::string>();
    g_sep_str[0]        = g_sep;
    g_sep_str[1]        = 0;
    init_lean_path(use_hott);
}

void finalize_lean_path() {
    delete g_lean_path_vector;
    delete g_lean_path;
    delete g_default_file_name;
}

bool has_file_ext(std::string const & fname, char const * ext) {
    unsigned ext_len = strlen(ext);
    return fname.size() > ext_len && fname.substr(fname.size() - ext_len, ext_len) == ext;
}

bool is_hlean_file(std::string const & fname) {
    return has_file_ext(fname, ".hlean");
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
    return is_lean_file(fname) || is_hlean_file(fname) || is_olean_file(fname) || is_lua_file(fname);
}

optional<std::string> check_file_core(std::string file, char const * ext) {
    if (ext)
        file += ext;
    std::ifstream ifile(file);
    if (ifile)
        return optional<std::string>(lrealpath(file.c_str()));
    else
        return optional<std::string>();
}

optional<std::string> check_file(std::string const & path, std::string const & fname, char const * ext = nullptr) {
    std::string file = path + g_sep + fname;
    if (is_directory(file.c_str())) {
        std::string default_file = file + g_sep + *g_default_file_name;
        if (auto r1 = check_file_core(default_file, ext)) {
            if (auto r2 = check_file_core(file, ext))
                throw exception(sstream() << "ambiguous import, it can be '" << *r1 << "' or '" << *r2 << "'");
            return r1;
        }
    }
    return check_file_core(file, ext);
}

std::string name_to_file(name const & fname) {
    return fname.to_string(g_sep_str);
}

std::string find_file(std::string fname, std::initializer_list<char const *> const & extensions) {
    bool is_known = is_known_file_ext(fname);
    fname = normalize_path(fname);
    for (auto path : *g_lean_path_vector) {
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
    throw file_not_found_exception(fname);
}

std::string find_file(std::string const & base, optional<unsigned> const & rel, name const & fname,
                      std::initializer_list<char const *> const & extensions) {
    if (!rel) {
        return find_file(fname.to_string(g_sep_str), extensions);
    } else {
        auto path = base;
        for (unsigned i = 0; i < *rel; i++) {
            path += g_sep;
            path += "..";
        }
        for (auto ext : extensions) {
            if (auto r = check_file(path, fname.to_string(g_sep_str), ext))
                return *r;
        }
        throw file_not_found_exception(fname.to_string());
    }
}

std::string find_file(std::string const & base, optional<unsigned> const & k, name const & fname, char const * ext) {
    return find_file(base, k, fname, {ext});
}

std::string find_file(std::string fname) {
    return find_file(fname, {".olean", ".lean", ".lua"});
}

std::string find_file(name const & fname) {
    return find_file(fname.to_string(g_sep_str));
}

std::string find_file(name const & fname, std::initializer_list<char const *> const & exts) {
    return find_file(fname.to_string(g_sep_str), exts);
}

char const * get_lean_path() {
    return g_lean_path->c_str();
}

void display_path(std::ostream & out, std::string const & fname) {
    out << fname;
}

std::string dirname(char const * fname) {
    if (fname == nullptr)
        return ".";
    std::string nfname = normalize_path(std::string(fname));
    fname = nfname.c_str();
    unsigned i        = 0;
    unsigned last_sep = 0;
    bool found_sep    = false;
    char const * it   = fname;
    while (*it) {
        if (*it == g_sep) {
            found_sep = true;
            last_sep  = i;
        }
        ++i;
        ++it;
    }
    if (!found_sep) {
        return ".";
    } else {
        std::string r;
        for (unsigned i = 0; i < last_sep; i++)
            r.push_back(fname[i]);
        return r;
    }
}

std::string path_append(char const * p1, char const * p2) {
    std::string r(p1);
    r += g_sep;
    r += p2;
    return r;
}
}
