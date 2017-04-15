/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Gabriel Ebner
*/
#pragma once
#include <string>
#include <vector>
#include "util/name.h"
#include "util/exception.h"
#include "util/path.h"

namespace lean {
class lean_file_not_found_exception : public exception {
    std::string m_fname;
public:
    lean_file_not_found_exception(std::string const & fname);
};

using search_path = std::vector<std::string>;

optional<std::string> get_leanpkg_path_file();
search_path parse_leanpkg_path(std::string const & fn);
optional<search_path> get_lean_path_from_env();
search_path get_builtin_search_path();

struct standard_search_path {
    search_path m_builtin;
    optional<search_path> m_from_env;
    optional<std::string> m_leanpkg_path_fn;
    std::string m_user_leanpkg_path_fn;
    optional<search_path> m_from_leanpkg_path;

    standard_search_path();
    search_path get_path() const;
};

#if !defined(LEAN_EMSCRIPTEN)
std::string get_exe_location();
#endif

/** \brief Hierarchical names are converted into paths using the path separator. Example: foo.bar is converted into foo/bar */
std::string find_file(search_path const &, name const & fname);
std::string find_file(search_path const &, name const & fname, std::initializer_list<char const *> const & exts);

/** \brief \brief Similar to previous find_file, but if k is not none then search at the k-th parent of base. */
std::string find_file(search_path const &, std::string const & base, optional<unsigned> const & rel, name const & fname,
                      std::initializer_list<char const *> const & extensions);
std::string find_file(search_path const &, std::string const & base, optional<unsigned> const & k, name const & fname, char const * ext);

void find_imports(search_path const &, std::string const & base, optional<unsigned> const & k,
                  std::vector<pair<std::string, std::string>> & imports_and_files);
/** \brief Return true iff fname ends with ".lean" */
bool is_lean_file(std::string const & fname);
/** \brief Return true iff fname ends with ".olean" */
bool is_olean_file(std::string const & fname);

/** \brief Return a string that replaces hierachical name separator '::' with a path separator. */
std::string name_to_file(name const & fname);

std::string olean_of_lean(std::string const & lean_fn);
std::string olean_file_to_lean_file(std::string const & olean);
}
