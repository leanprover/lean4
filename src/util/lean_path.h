/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/name.h"
#include "util/exception.h"

namespace lean {
class file_not_found_exception : public exception {
    std::string m_fname;
public:
    file_not_found_exception(std::string const & fname);
};

/** \brief Initialize the lean_path */
void init_lean_path();
/** \brief Return the LEAN_PATH string */
char const * get_lean_path();
/**
   \brief Search the file \c fname in the LEAN_PATH. Throw an
   exception if the file was not found.
*/
std::string find_file(std::string fname);
std::string find_file(std::string fname, std::initializer_list<char const *> const & exts);

/** \brief Hierarchical names are converted into paths using the path separator. Example: foo.bar is converted into foo/bar */
std::string find_file(name const & fname);
std::string find_file(name const & fname, std::initializer_list<char const *> const & exts);

/** \brief \brief Similar to previous find_file, but if k is not none then search at the k-th parent of base. */
std::string find_file(std::string const & base, optional<unsigned> const & rel, name const & fname,
                      std::initializer_list<char const *> const & extensions);
std::string find_file(std::string const & base, optional<unsigned> const & k, name const & fname, char const * ext);

/** \brief Return true iff fname ends with ".lean" */
bool is_lean_file(std::string const & fname);
/** \brief Return true iff fname ends with ".olean" */
bool is_olean_file(std::string const & fname);
/** \brief Return true iff fname ends with ".lua" */
bool is_lua_file(std::string const & fname);

/** \brief Return a string that replaces hierachical name separator '::' with a path separator. */
std::string name_to_file(name const & fname);

/**
    \brief Auxiliary function for displaying a path.
    In some platforms it will fix the notation used to display the path.
*/
void display_path(std::ostream & out, std::string const & fname);

std::string dirname(char const * fname);
std::string path_append(char const * path1, char const * path2);

void initialize_lean_path(bool use_hott = false);
void finalize_lean_path();
}
