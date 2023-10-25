/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Gabriel Ebner
*/
#include "util/path.h"
#if defined(LEAN_WINDOWS)
#include <windows.h>
#endif
#include <string>
#include <cstring>
#include <cstdlib>
#include <fstream>
#include <vector>
#include <sys/types.h>
#include <sys/stat.h>
#include "runtime/exception.h"
#include "runtime/sstream.h"
#include "runtime/optional.h"

#ifdef _MSC_VER
#define S_ISDIR(mode) ((mode & _S_IFDIR) != 0)
#else
#include <dirent.h>
#endif

namespace lean {
file_not_found_exception::file_not_found_exception(std::string const & fname):
        exception(sstream() << "file '" << fname << "' not found"),
        m_fname(fname) {}

#if defined(LEAN_EMSCRIPTEN)
// emscripten version
static char g_path_sep     = ':';
static constexpr char g_sep          = '/';
static char g_bad_sep      = '\\';
bool is_path_sep(char c) { return c == g_path_sep; }
#elif defined(LEAN_WINDOWS)
// Windows version
static char g_path_sep     = ';';
static constexpr char g_sep          = '\\';
static char g_bad_sep      = '/';
std::string get_exe_location() {
    HMODULE hModule = GetModuleHandle(NULL);
    char path[MAX_PATH];
    GetModuleFileName(hModule, path, MAX_PATH);
    return std::string(path);
}
bool is_path_sep(char c) { return c == g_path_sep; }
#elif defined(__APPLE__)
// OSX version
#include <mach-o/dyld.h>
#include <limits.h>
#include <stdlib.h>
static char g_path_sep     = ':';
static constexpr char g_sep          = '/';
static char g_bad_sep      = '\\';
std::string get_exe_location() {
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
static constexpr char g_sep          = '/';
static char g_bad_sep      = '\\';
std::string get_exe_location() {
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

#if defined(LEAN_WINDOWS)
std::string resolve(std::string const & rel_or_abs, std::string const & base) {
    // TODO(gabriel): detect absolute pathnames
    return base + g_sep + rel_or_abs;
}
#else
std::string resolve(std::string const & rel_or_abs, std::string const & base) {
    if (!rel_or_abs.empty() && rel_or_abs[0] == g_sep) {
        // absolute
        return rel_or_abs;
    } else {
        // relative
        return base + g_sep + rel_or_abs;
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

static char g_sep_str[2] = { g_sep, 0 };

char const * get_dir_sep() { return g_sep_str; }
char get_dir_sep_ch() { return g_sep; }

bool has_file_ext(std::string const & fname, char const * ext) {
    unsigned ext_len = strlen(ext);
    return fname.size() > ext_len && fname.substr(fname.size() - ext_len, ext_len) == ext;
}

void find_files(std::string const & base, char const * ext, std::vector<std::string> & files) {
    for (auto & fn : read_dir(base)) {
        if (auto i_d = is_dir(fn)) {
            if (*i_d) {
                find_files(fn, ext, files);
            } else if (has_file_ext(fn, ext)) {
                files.push_back(fn);
            }
        }
    }
}

std::string dirname(std::string const & fname) {
    auto nfname = normalize_path(fname);
    auto i = nfname.rfind(g_sep);
    if (i == std::string::npos) {
        return ".";
    } else {
        return nfname.substr(0, i);
    }
}

std::string stem(std::string const & fname) {
    auto nfname = normalize_path(fname);
    auto i = nfname.rfind(g_sep);
    if (i == std::string::npos) {
        i = 0;
    } else {
        i++;
    }
    auto j = nfname.rfind(".");
    if (j == std::string::npos) {
        j = nfname.size();
    }
    return nfname.substr(i, j - i);
}

std::string read_file(std::string const & fname, std::ios_base::openmode mode) {
    std::ifstream in(fname, mode);
    if (!in.good()) throw file_not_found_exception(fname);
    std::stringstream buf;
    buf << in.rdbuf();
    return buf.str();
}

time_t get_mtime(std::string const &fname) {
    struct stat st;
    if (stat(fname.c_str(), &st) != 0)
        return -1;
    return st.st_mtime;
}

optional<bool> is_dir(std::string const & fn) {
    struct stat st;
    if (stat(fn.c_str(), &st) == 0)
        return optional<bool>(S_ISDIR(st.st_mode));
    return optional<bool>();
}

bool is_directory(std::string const & fn) {
    if (auto res = is_dir(fn)) {
        return *res;
    } else {
        return false;
    }
}

std::vector<std::string> read_dir(std::string const &dirname) {
    std::vector<std::string> files;
#ifdef _MSC_VER
    WIN32_FIND_DATA data;
    std::string dir = dirname + "\\*";
    HANDLE hFind = FindFirstFile(dir.c_str(), &data);
    if (hFind != INVALID_HANDLE_VALUE) {
        do {
            if (strcmp(data.cFileName, ".") != 0 && strcmp(data.cFileName, "..") != 0)
                files.push_back(dirname + '\\' + data.cFileName);
        } while (FindNextFile(hFind, &data));
        FindClose(hFind);
    }
#else
    auto dir = opendir(dirname.c_str());
    if (!dir) throw exception(sstream() << "could not open directory " << dirname << ": " << std::strerror(errno));

    while (auto ep = readdir(dir)) { // NOLINT
        // ^^ disabling readdir_r lint because glibc recommends using readdir now.

        std::string fn = ep->d_name;
        if (fn == "." || fn == "..") continue;
        files.push_back(dirname + get_dir_sep() + fn);
    }
    closedir(dir);
#endif
    return files;
}

std::string lrealpath(std::string const & fname) {
#if defined(LEAN_EMSCRIPTEN)
    return fname;
#elif defined(LEAN_WINDOWS)
    constexpr unsigned BufferSize = 8192;
    char buffer[BufferSize];
    DWORD retval = GetFullPathName(fname.c_str(), BufferSize, buffer, nullptr);
    if (retval == 0 || retval > BufferSize) {
        return fname;
    } else {
        return std::string(buffer);
    }
#else
    constexpr unsigned BufferSize = 8192;
    char buffer[BufferSize];
    char * tmp = realpath(fname.c_str(), buffer);
    if (tmp) {
        std::string r(tmp);
        return r;
    } else {
        throw file_not_found_exception(fname);
    }
#endif
}
}
