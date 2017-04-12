/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <vector>
#include "util/name.h"
#include "util/exception.h"

namespace lean {
class file_not_found_exception : public exception {
    std::string m_fname;
public:
    file_not_found_exception(std::string const & fname);
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

/** \brief Find all files with the given extension recursively. */
void find_files(std::string const & base, char const * ext, std::vector<std::string> & files);
void find_imports(search_path const &, std::string const & base, optional<unsigned> const & k,
                  std::vector<pair<std::string, std::string>> & imports_and_files);
/** \brief Return true iff fname ends with ".lean" */
bool is_lean_file(std::string const & fname);
/** \brief Return true iff fname ends with ".olean" */
bool is_olean_file(std::string const & fname);

/** \brief Return a string that replaces hierachical name separator '::' with a path separator. */
std::string name_to_file(name const & fname);

/**
    \brief Auxiliary function for displaying a path.
    In some platforms it will fix the notation used to display the path.
*/
void display_path(std::ostream & out, std::string const & fname);

std::string resolve(std::string const & rel_or_abs, std::string const & base);
std::string dirname(char const * fname);
inline std::string dirname(std::string const & fn) { return dirname(fn.c_str()); }
std::string path_append(char const * path1, char const * path2);

std::string olean_of_lean(std::string const & lean_fn);
std::string olean_file_to_lean_file(std::string const & olean);

std::string read_file(std::string const & fname, std::ios_base::openmode mode = std::ios_base::in);

optional<bool> is_dir(std::string const & fn);
std::vector<std::string> read_dir(std::string const & dirname);

time_t get_mtime(std::string const & fname);

void initialize_lean_path();
void finalize_lean_path();
}
