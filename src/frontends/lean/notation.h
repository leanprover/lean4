/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
namespace lean {
constexpr unsigned g_eq_precedence    = 50;
constexpr unsigned g_arrow_precedence = 25;
class environment;
class io_state;
void init_builtin_notation(environment const & env, io_state & st);
}
