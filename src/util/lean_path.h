/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
namespace lean {
/**
   \brief Return the LEAN_PATH string
*/
char const * get_lean_path();
/**
   \brief Search the file \c fname in the LEAN_PATH. Throw an
   exception if the file was not found.
*/
std::string find_file(char const * fname);
}
