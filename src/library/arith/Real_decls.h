/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
// Automatically generated file, DO NOT EDIT
#include "kernel/expr.h"
namespace lean {
expr mk_Real();
bool is_Real(expr const & e);
expr mk_nat_to_real_fn();
bool is_nat_to_real_fn(expr const & e);
inline bool is_nat_to_real(expr const & e) { return is_app(e) && is_nat_to_real_fn(arg(e, 0)) && num_args(e) == 2; }
inline expr mk_nat_to_real(expr const & e1) { return mk_app({mk_nat_to_real_fn(), e1}); }
expr mk_Real_ge_fn();
bool is_Real_ge_fn(expr const & e);
inline bool is_Real_ge(expr const & e) { return is_app(e) && is_Real_ge_fn(arg(e, 0)) && num_args(e) == 3; }
inline expr mk_Real_ge(expr const & e1, expr const & e2) { return mk_app({mk_Real_ge_fn(), e1, e2}); }
expr mk_Real_lt_fn();
bool is_Real_lt_fn(expr const & e);
inline bool is_Real_lt(expr const & e) { return is_app(e) && is_Real_lt_fn(arg(e, 0)) && num_args(e) == 3; }
inline expr mk_Real_lt(expr const & e1, expr const & e2) { return mk_app({mk_Real_lt_fn(), e1, e2}); }
expr mk_Real_gt_fn();
bool is_Real_gt_fn(expr const & e);
inline bool is_Real_gt(expr const & e) { return is_app(e) && is_Real_gt_fn(arg(e, 0)) && num_args(e) == 3; }
inline expr mk_Real_gt(expr const & e1, expr const & e2) { return mk_app({mk_Real_gt_fn(), e1, e2}); }
expr mk_Real_sub_fn();
bool is_Real_sub_fn(expr const & e);
inline bool is_Real_sub(expr const & e) { return is_app(e) && is_Real_sub_fn(arg(e, 0)) && num_args(e) == 3; }
inline expr mk_Real_sub(expr const & e1, expr const & e2) { return mk_app({mk_Real_sub_fn(), e1, e2}); }
expr mk_Real_neg_fn();
bool is_Real_neg_fn(expr const & e);
inline bool is_Real_neg(expr const & e) { return is_app(e) && is_Real_neg_fn(arg(e, 0)) && num_args(e) == 2; }
inline expr mk_Real_neg(expr const & e1) { return mk_app({mk_Real_neg_fn(), e1}); }
expr mk_Real_abs_fn();
bool is_Real_abs_fn(expr const & e);
inline bool is_Real_abs(expr const & e) { return is_app(e) && is_Real_abs_fn(arg(e, 0)) && num_args(e) == 2; }
inline expr mk_Real_abs(expr const & e1) { return mk_app({mk_Real_abs_fn(), e1}); }
}
