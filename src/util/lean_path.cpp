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
#include "runtime/sstream.h"

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
                    path.push_back(lrealpath(lean_path.substr(i, j - i)));
                i = j + 1;
            }
        }
        if (j > i)
            path.push_back(lrealpath(lean_path.substr(i, j - i)));
        return optional<search_path>(path);
    } else {
        return optional<search_path>();
    }
}

search_path get_builtin_search_path() {
    search_path path;
#if !defined(LEAN_EMSCRIPTEN)
    std::string exe_path = dirname(get_exe_location());
    auto lib_path = exe_path + get_dir_sep() + ".." + get_dir_sep() + "library";
    if (exists(lib_path))
        path.push_back(lrealpath(lib_path));
    auto installed_lib_path = exe_path + get_dir_sep() + ".." + get_dir_sep() + "lib" + get_dir_sep() + "lean" + get_dir_sep() + "library";
    if (exists(installed_lib_path))
        path.push_back(lrealpath(installed_lib_path));
#endif
    return path;
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

name module_name_of_file(search_path const & paths, std::string const & fname0) {
    auto fname = normalize_path(fname0);
    lean_assert(is_lean_file(fname));
    fname = fname.substr(0, fname.size() - std::string(".lean").size());
    for (auto & path : paths) {
        if (path.size() < fname.size() && fname.substr(0, path.size()) == path) {
            size_t pos = path.size();
            if (fname[pos] == get_dir_sep_ch())
                pos++;
            name n;
            while (pos < fname.size()) {
                auto sep_pos = fname.find(get_dir_sep_ch(), pos);
                n = name(n, fname.substr(pos, sep_pos - pos).c_str());
                pos = sep_pos;
                if (pos != std::string::npos)
                    pos++;
            }
            return n;
        }
    }
    throw exception(sstream() << "file '" << fname0 << "' is not part of any known Lean packages");
}

module_name absolutize_module_name(search_path const & path, std::string const & base, rel_module_name const & rel) {
    // TODO(Sebastian): Should make sure that the result of `find_file` is still in the same package as `base`
    return module_name_of_file(path, find_file(path, base, rel.m_updirs, rel.m_name, ".lean"));
}

std::string olean_of_lean(std::string const & lean_fn) {
    if (lean_fn.size() > 5 && lean_fn.substr(lean_fn.size() - 5) == ".lean") {
        return lean_fn.substr(0, lean_fn.size() - 5) + ".olean";
    } else {
        throw exception(sstream() << "not a .lean file: " << lean_fn);
    }
}
}
