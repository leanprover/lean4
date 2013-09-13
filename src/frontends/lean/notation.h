/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
namespace lean {
constexpr unsigned g_eq_precedence    = 50;
constexpr unsigned g_arrow_precedence = 70;
class frontend;
void init_builtin_notation(frontend & fe);
}
