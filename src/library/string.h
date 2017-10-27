/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/environment.h"

namespace lean {
/**
    \brief Return an expression that encodes the given string in as a Lean expression.
    \post *to_string(from_string(s)) == s */
expr from_string(std::string const & s);

/** \brief If the given expression encodes a string, then convert it back to a string.
    \see from_string */
optional<std::string> to_string(expr const & e);
bool is_string_value(expr const & e);

bool is_string_macro(expr const & e);
/** \brief Expand string macro if 'e' is a string macro */
optional<expr> expand_string_macro(expr const & e);

optional<unsigned> to_char_core(expr const & e);
bool is_char_value_core(expr const & e);

optional<unsigned> to_char(abstract_type_context & ctx, expr const & e);
bool is_char_value(abstract_type_context & ctx, expr const & e);

format pp_string_literal(std::string const & s);
format pp_char_literal(unsigned c);

void initialize_string();
void finalize_string();
}
