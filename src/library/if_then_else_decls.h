/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
// Automatically generated file, DO NOT EDIT
#include "kernel/expr.h"
namespace lean {
expr mk_if_true_fn();
bool is_if_true_fn(expr const & e);
inline expr mk_if_true_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_if_true_fn(), e1, e2, e3}); }
expr mk_if_false_fn();
bool is_if_false_fn(expr const & e);
inline expr mk_if_false_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_if_false_fn(), e1, e2, e3}); }
expr mk_if_a_a_fn();
bool is_if_a_a_fn(expr const & e);
inline expr mk_if_a_a_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_if_a_a_fn(), e1, e2, e3}); }
expr mk_if_congr_fn();
bool is_if_congr_fn(expr const & e);
inline expr mk_if_congr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8, expr const & e9, expr const & e10) { return mk_app({mk_if_congr_fn(), e1, e2, e3, e4, e5, e6, e7, e8, e9, e10}); }
expr mk_if_imp_then_fn();
bool is_if_imp_then_fn(expr const & e);
inline expr mk_if_imp_then_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_if_imp_then_fn(), e1, e2, e3, e4, e5}); }
expr mk_if_imp_else_fn();
bool is_if_imp_else_fn(expr const & e);
inline expr mk_if_imp_else_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_if_imp_else_fn(), e1, e2, e3, e4, e5}); }
}
