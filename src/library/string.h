/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/environment.h"

namespace lean {
/**
    \brief Return an expression that encodes the given string using the declarations
    ascii, empty and str.

    \see has_string_decls

    \post *to_string(from_string(s)) == s
*/
expr from_string(std::string const & s);

/**
   \brief If the given expression encodes a string, then convert it back to a string.

   \see from_string
*/
optional<std::string> to_string(expr const & e);

format pp_string_literal(std::string const & s);

void initialize_string();
void finalize_string();
}
