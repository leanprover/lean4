/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Gabriel Ebner
*/
#include "util/lean_path.h"
#include <string>
#include <cstdlib>
#include <fstream>
#include <vector>
#include "util/sstream.h"

#ifndef LEAN_DEFAULT_MODULE_FILE_NAME
#define LEAN_DEFAULT_MODULE_FILE_NAME "default"
#endif

namespace lean {
lean_file_not_found_exception::lean_file_not_found_exception(std::string const & fname):
    exception(sstream() << "file '" << fname << "' not found in the LEAN_PATH"),
    m_fname(fname) {}

static char const * g_default_file_name = LEAN_DEFAULT_MODULE_FILE_NAME;

static bool exists(std::string const & fn) {
    return !!std::ifstream(fn);
}

optional<std::string> get_leanpkg_path_file() {
    auto dir = lrealpath(".");
    while (true) {
        auto fn = dir + get_dir_sep() + "leanpkg.path";
        if (exists(fn)) return optional<std::string>(fn);

        auto i = dir.rfind(get_dir_sep());
        if (i == std::string::npos) {
            return optional<std::string>();
        } else {
            dir = dir.substr(0, i);
        }
    }
}

std::string get_user_leanpkg_path() {
    // TODO(gabriel): check if this works on windows
    if (auto home = getenv("HOME")) {
        return std::string(home) + get_dir_sep() + ".lean" + get_dir_sep() + "leanpkg.path";
    } else {
        return "/could-not-find-home";
    }
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
#if !defined(LEAN_EMSCRIPTEN)
    std::string exe_path = dirname(get_exe_location());
    path.push_back(exe_path + get_dir_sep() + ".." + get_dir_sep() + "library");
    path.push_back(exe_path + get_dir_sep() + ".." + get_dir_sep() + "lib" + get_dir_sep() + "lean" + get_dir_sep() + "library");
#endif
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
        return optional<std::string>(lrealpath(file));
    else
        return optional<std::string>();
}

optional<std::string> check_file(std::string const & path, std::string const & fname, char const * ext = nullptr) {
    std::string file = path + get_dir_sep() + fname;
    if (is_directory(file.c_str())) {
        std::string default_file = file + get_dir_sep() + g_default_file_name;
        if (auto r1 = check_file_core(default_file, ext)) {
            if (auto r2 = check_file_core(file, ext))
                throw exception(sstream() << "ambiguous import, it can be '" << *r1 << "' or '" << *r2 << "'");
            return r1;
        }
    }
    return check_file_core(file, ext);
}

std::string name_to_file(name const & fname) {
    return fname.to_string(get_dir_sep());
}

static std::string find_file(search_path const & paths, std::string fname, std::initializer_list<char const *> const & extensions) {
    bool is_known = is_known_file_ext(fname);
    fname = normalize_path(fname);
    buffer<std::string> results;
    for (auto & path : paths) {
        if (is_known) {
            if (auto r = check_file(path, fname))
                results.push_back(*r);
        } else {
            for (auto ext : extensions) {
                if (auto r = check_file(path, fname, ext))
                    results.push_back(*r);
            }
        }
    }
    if (results.size() == 0)
        throw lean_file_not_found_exception(fname);
    else if (results.size() > 1)
        throw exception(sstream() << "ambiguous import, it can be '" << results[0] << "' or '" << results[1] << "'");
    else
        return results[0];
}

std::string find_file(search_path const & paths, std::string const & base, optional<unsigned> const & rel, name const & fname,
                      std::initializer_list<char const *> const & extensions) {
    if (!rel) {
        return find_file(paths, fname.to_string(get_dir_sep()), extensions);
    } else {
        auto path = base;
        for (unsigned i = 0; i < *rel; i++) {
            path += get_dir_sep();
            path += "..";
        }
        for (auto ext : extensions) {
            if (auto r = check_file(path, fname.to_string(get_dir_sep()), ext))
                return *r;
        }
        throw lean_file_not_found_exception(fname.to_string());
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
    return find_file(paths, fname.to_string(get_dir_sep()));
}

std::string find_file(search_path const & paths, name const & fname, std::initializer_list<char const *> const & exts) {
    return find_file(paths, fname.to_string(get_dir_sep()), exts);
}

void find_imports_core(std::string const & base, optional<unsigned> const & k,
                       std::vector<pair<std::string, std::string>> & imports) {
    std::vector<std::string> files;
    find_files(base, ".lean", files);
    find_files(base, ".olean", files);

    for (auto const & file : files) {
        auto import = file.substr(base.size() + 1, file.rfind('.') - (base.size() + 1));
        std::replace(import.begin(), import.end(), get_dir_sep_ch(), '.');
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
            path += get_dir_sep();
            path += "..";
        }
        find_imports_core(path, k, imports);
    }
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

}
