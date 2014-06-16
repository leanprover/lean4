/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/name.h"
namespace lean {
/** \brief Initialize the lean_path for the given kernel instance */
void init_lean_path(char const * kernel_instance_name);
/** \brief Return the LEAN_PATH string */
char const * get_lean_path();
/**
   \brief Search the file \c fname in the LEAN_PATH. Throw an
   exception if the file was not found.
*/
std::string find_file(std::string fname);

std::string find_file(std::string fname, std::initializer_list<char const *> const & exts);


/** \brief Return true iff fname ends with ".lean" */
bool is_lean_file(std::string const & fname);
/** \brief Return true iff fname ends with ".olean" */
bool is_olean_file(std::string const & fname);
/** \brief Return true iff fname ends with ".lua" */
bool is_lua_file(std::string const & fname);

/** \brief Return a string that replaces hierachical name separator '::' with a path separator. */
std::string name_to_file(name const & fname);
}
