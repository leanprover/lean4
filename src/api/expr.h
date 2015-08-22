/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "api/univ.h"
#include "api/lean_expr.h"
namespace lean {
inline expr * to_expr(lean_expr n) { return reinterpret_cast<expr *>(n); }
inline expr const & to_expr_ref(lean_expr n) { return *reinterpret_cast<expr *>(n); }
inline lean_expr of_expr(expr * n) { return reinterpret_cast<lean_expr>(n); }
void to_buffer(unsigned sz, lean_expr const * ns, buffer<expr> & r);

inline list<expr> * to_list_expr(lean_list_expr n) { return reinterpret_cast<list<expr> *>(n); }
inline list<expr> const & to_list_expr_ref(lean_list_expr n) { return *reinterpret_cast<list<expr> *>(n); }
inline lean_list_expr of_list_expr(list<expr> * n) { return reinterpret_cast<lean_list_expr>(n); }

inline macro_definition * to_macro_definition(lean_macro_def n) { return reinterpret_cast<macro_definition *>(n); }
inline macro_definition const & to_macro_definition_ref(lean_macro_def n) { return *reinterpret_cast<macro_definition *>(n); }
inline lean_macro_def of_macro_definition(macro_definition * n) { return reinterpret_cast<lean_macro_def>(n); }
}
