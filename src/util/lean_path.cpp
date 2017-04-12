/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/lean_path.h"
#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
#include <windows.h>
#endif
#include <string>
#include <cstdlib>
#include <fstream>
#include <vector>
#include <sys/types.h>
#include <sys/stat.h>
#include <dirent.h>
#include "util/exception.h"
#include "util/sstream.h"
#include "util/name.h"
#include "util/optional.h"
#include "util/realpath.h"

#ifndef LEAN_DEFAULT_MODULE_FILE_NAME
#define LEAN_DEFAULT_MODULE_FILE_NAME "default"
#endif

namespace lean {
file_not_found_exception::file_not_found_exception(std::string const & fname):
    exception(sstream() << "file '" << fname << "' not found in the LEAN_PATH"),
    m_fname(fname) {}

static std::string * g_default_file_name             = nullptr;

bool is_directory(char const * pathname) {
    struct stat info;
    if (stat(pathname, &info) != 0 )
        return false; // failed to access pathname
    return info.st_mode & S_IFDIR;
}

#if defined(LEAN_EMSCRIPTEN)
// emscripten version
static char g_path_sep     = ':';
static char g_sep          = '/';
static char g_bad_sep      = '\\';
bool is_path_sep(char c) { return c == g_path_sep; }
#elif defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
// Windows version
static char g_path_sep     = ';';
static char g_sep          = '\\';
static char g_bad_sep      = '/';
std::string get_exe_location() {
    HMODULE hModule = GetModuleHandleW(NULL);
    WCHAR path[MAX_PATH];
    GetModuleFileNameW(hModule, path, MAX_PATH);
    std::wstring pathstr(path);
    return std::string(pathstr.begin(), pathstr.end());
}
bool is_path_sep(char c) { return c == g_path_sep; }
#elif defined(__APPLE__)
// OSX version
#include <mach-o/dyld.h>
#include <limits.h>
#include <stdlib.h>
static char g_path_sep     = ':';
static char g_sep          = '/';
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
static char g_sep          = '/';
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

static char g_sep_str[2];

void initialize_lean_path() {
    if (g_default_file_name != nullptr)
        finalize_lean_path();
    g_default_file_name = new std::string(LEAN_DEFAULT_MODULE_FILE_NAME);
    g_sep_str[0]        = g_sep;
    g_sep_str[1]        = 0;
}

void finalize_lean_path() {
    delete g_default_file_name;
}

static bool exists(std::string const & fn) {
    return !!std::ifstream(fn);
}

optional<std::string> get_leanpkg_path_file() {
    auto dir = lrealpath(".");
    while (true) {
        auto fn = dir + g_sep_str + "leanpkg.path";
        if (exists(fn)) return optional<std::string>(fn);

        auto i = dir.rfind(g_sep);
        if (i == std::string::npos) {
            return optional<std::string>();
        } else {
            dir = dir.substr(0, i);
        }
    }
}

std::string get_user_leanpkg_path() {
    // TODO(gabriel): check if this works on windows
    return std::string(getenv("HOME")) + g_sep + ".lean" + g_sep + "leanpkg.path";
}

static optional<std::string> begins_with(std::string const & s, std::string const & prefix) {
    if (prefix.size() <= s.size() && s.substr(0, prefix.size()) == prefix) {
        return optional<std::string>(s.substr(prefix.size(), s.size()));
    } else {
        return optional<std::string>();
    }
}

search_path parse_leanpkg_path(std::string const & fn) {
    std::ifstream in(fn);
    if (!in) throw exception(sstream() << "cannot open " << fn);
    auto fn_dir = dirname(fn);
    search_path path;
    while (!in.eof()) {
        std::string line;
        std::getline(in, line);

        if (auto rest = begins_with(line, "path "))
            path.push_back(resolve(*rest, fn_dir));

        if (line == "builtin_path") {
            auto builtin = get_builtin_search_path();
            path.insert(path.end(), builtin.begin(), builtin.end());
        }
    }
    return path;
}

optional<search_path> get_lean_path_from_env() {
    if (auto r = getenv("LEAN_PATH")) {
        auto lean_path = normalize_path(r);
        unsigned i  = 0;
        unsigned j  = 0;
        unsigned sz = static_cast<unsigned>(lean_path.size());
        search_path path;
        for (; j < sz; j++) {
            if (is_path_sep(lean_path[j])) {
                if (j > i)
                    path.push_back(lean_path.substr(i, j - i));
                i = j + 1;
            }
        }
        if (j > i)
            path.push_back(lean_path.substr(i, j - i));
        return optional<search_path>(path);
    } else {
        return optional<search_path>();
    }
}

search_path get_builtin_search_path() {
    search_path path;
    std::string exe_path = get_path(get_exe_location());
    path.push_back(exe_path + g_sep + ".." + g_sep + "library");
    path.push_back(exe_path + g_sep + ".." + g_sep + "lib" + g_sep + "lean" + g_sep + "library");
    return path;
}

standard_search_path::standard_search_path() {
    m_builtin = get_builtin_search_path();

    m_from_env = get_lean_path_from_env();
    m_leanpkg_path_fn = get_leanpkg_path_file();
    m_user_leanpkg_path_fn = get_user_leanpkg_path();

    if (m_leanpkg_path_fn) {
        m_from_leanpkg_path = parse_leanpkg_path(*m_leanpkg_path_fn);
    } else if (exists(m_user_leanpkg_path_fn)) {
        m_from_leanpkg_path = parse_leanpkg_path(m_user_leanpkg_path_fn);
    }
}

search_path standard_search_path::get_path() const {
    if (m_from_env) return *m_from_env;
    if (m_from_leanpkg_path) return *m_from_leanpkg_path;
    return m_builtin;
}

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

bool is_known_file_ext(std::string const & fname) {
    return is_lean_file(fname) || is_olean_file(fname);
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

std::string find_file(search_path const & paths, std::string fname, std::initializer_list<char const *> const & extensions) {
    bool is_known = is_known_file_ext(fname);
    fname = normalize_path(fname);
    for (auto & path : paths) {
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

std::string find_file(search_path const & paths, std::string const & base, optional<unsigned> const & rel, name const & fname,
                      std::initializer_list<char const *> const & extensions) {
    if (!rel) {
        return find_file(paths, fname.to_string(g_sep_str), extensions);
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

std::string find_file(search_path const & paths,
                      std::string const & base, optional<unsigned> const & k, name const & fname, char const * ext) {
    return find_file(paths, base, k, fname, {ext});
}

std::string find_file(search_path const & paths, std::string fname) {
    return find_file(paths, fname, {".olean", ".lean"});
}

std::string find_file(search_path const & paths, name const & fname) {
    return find_file(paths, fname.to_string(g_sep_str));
}

std::string find_file(search_path const & paths, name const & fname, std::initializer_list<char const *> const & exts) {
    return find_file(paths, fname.to_string(g_sep_str), exts);
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

void find_imports_core(std::string const & base, optional<unsigned> const & k,
                       std::vector<pair<std::string, std::string>> & imports) {
    std::vector<std::string> files;
    find_files(base, ".lean", files);
    find_files(base, ".olean", files);

    for (auto const & file : files) {
        auto import = file.substr(base.size() + 1, file.rfind('.') - (base.size() + 1));
        std::replace(import.begin(), import.end(), g_sep, '.');
        if (k)
            import = std::string(*k + 1, '.') + import;
        auto n = import.rfind(".default");
        if (n != static_cast<unsigned>(-1) && n == import.size() - std::string(".default").size())
            import = import.substr(0, n);
        imports.push_back({import, file});
    }
}

void find_imports(search_path const & paths, std::string const & base, optional<unsigned> const & k,
                  std::vector<pair<std::string, std::string>> & imports) {
    if (!k) {
        for (auto & base : paths)
            if (is_dir(base))
                find_imports_core(base, k, imports);
    } else {
        auto path = base;
        for (unsigned i = 0; i < *k; i++) {
            path += g_sep;
            path += "..";
        }
        find_imports_core(path, k, imports);
    }
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

std::string olean_of_lean(std::string const & lean_fn) {
    if (lean_fn.size() > 5 && lean_fn.substr(lean_fn.size() - 5) == ".lean") {
        return lean_fn.substr(0, lean_fn.size() - 5) + ".olean";
    } else {
        throw exception(sstream() << "not a .lean file: " << lean_fn);
    }
}

std::string olean_file_to_lean_file(std::string const &olean) {
    lean_assert(is_olean_file(olean));
    std::string lean = olean;
    lean.erase(lean.size() - std::string("olean").size(), 1);
    return lean;
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

std::vector<std::string> read_dir(std::string const &dirname) {
    auto dir = opendir(dirname.c_str());
    if (!dir) throw exception(sstream() << "could not open directory " << dirname << ": " << std::strerror(errno));

    std::vector<std::string> files;
    while (auto ep = readdir(dir)) { // NOLINT
        // ^^ disabling readdir_r lint because glibc recommends using readdir now.

        std::string fn = ep->d_name;
        if (fn == "." || fn == "..") continue;
        files.push_back(path_append(dirname.c_str(), fn.c_str()));
    }
    closedir(dir);
    return files;
}

}
