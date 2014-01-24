/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
// Automatically generated file, DO NOT EDIT
#include "kernel/expr.h"
namespace lean {
expr mk_cast_fn();
bool is_cast_fn(expr const & e);
inline bool is_cast(expr const & e) { return is_app(e) && is_cast_fn(arg(e, 0)) && num_args(e) == 5; }
inline expr mk_cast(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_cast_fn(), e1, e2, e3, e4}); }
expr mk_cast_heq_fn();
bool is_cast_heq_fn(expr const & e);
inline expr mk_cast_heq_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_cast_heq_fn(), e1, e2, e3, e4}); }
expr mk_cast_app_fn();
bool is_cast_app_fn(expr const & e);
inline expr mk_cast_app_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8) { return mk_app({mk_cast_app_fn(), e1, e2, e3, e4, e5, e6, e7, e8}); }
expr mk_cast_eq_fn();
bool is_cast_eq_fn(expr const & e);
inline expr mk_cast_eq_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_cast_eq_fn(), e1, e2, e3}); }
expr mk_cast_trans_fn();
bool is_cast_trans_fn(expr const & e);
inline expr mk_cast_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_cast_trans_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_cast_pull_fn();
bool is_cast_pull_fn(expr const & e);
inline expr mk_cast_pull_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7) { return mk_app({mk_cast_pull_fn(), e1, e2, e3, e4, e5, e6, e7}); }
}
