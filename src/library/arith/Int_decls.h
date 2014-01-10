/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
// Automatically generated file, DO NOT EDIT
#include "kernel/expr.h"
namespace lean {
expr mk_Int();
bool is_Int(expr const & e);
expr mk_Int_ge_fn();
bool is_Int_ge_fn(expr const & e);
inline bool is_Int_ge(expr const & e) { return is_app(e) && is_Int_ge_fn(arg(e, 0)); }
inline expr mk_Int_ge(expr const & e1, expr const & e2) { return mk_app({mk_Int_ge_fn(), e1, e2}); }
expr mk_Int_lt_fn();
bool is_Int_lt_fn(expr const & e);
inline bool is_Int_lt(expr const & e) { return is_app(e) && is_Int_lt_fn(arg(e, 0)); }
inline expr mk_Int_lt(expr const & e1, expr const & e2) { return mk_app({mk_Int_lt_fn(), e1, e2}); }
expr mk_Int_gt_fn();
bool is_Int_gt_fn(expr const & e);
inline bool is_Int_gt(expr const & e) { return is_app(e) && is_Int_gt_fn(arg(e, 0)); }
inline expr mk_Int_gt(expr const & e1, expr const & e2) { return mk_app({mk_Int_gt_fn(), e1, e2}); }
expr mk_Int_sub_fn();
bool is_Int_sub_fn(expr const & e);
inline bool is_Int_sub(expr const & e) { return is_app(e) && is_Int_sub_fn(arg(e, 0)); }
inline expr mk_Int_sub(expr const & e1, expr const & e2) { return mk_app({mk_Int_sub_fn(), e1, e2}); }
expr mk_Int_neg_fn();
bool is_Int_neg_fn(expr const & e);
inline bool is_Int_neg(expr const & e) { return is_app(e) && is_Int_neg_fn(arg(e, 0)); }
inline expr mk_Int_neg(expr const & e1) { return mk_app({mk_Int_neg_fn(), e1}); }
expr mk_Int_mod_fn();
bool is_Int_mod_fn(expr const & e);
inline bool is_Int_mod(expr const & e) { return is_app(e) && is_Int_mod_fn(arg(e, 0)); }
inline expr mk_Int_mod(expr const & e1, expr const & e2) { return mk_app({mk_Int_mod_fn(), e1, e2}); }
expr mk_Int_divides_fn();
bool is_Int_divides_fn(expr const & e);
inline bool is_Int_divides(expr const & e) { return is_app(e) && is_Int_divides_fn(arg(e, 0)); }
inline expr mk_Int_divides(expr const & e1, expr const & e2) { return mk_app({mk_Int_divides_fn(), e1, e2}); }
expr mk_Int_abs_fn();
bool is_Int_abs_fn(expr const & e);
inline bool is_Int_abs(expr const & e) { return is_app(e) && is_Int_abs_fn(arg(e, 0)); }
inline expr mk_Int_abs(expr const & e1) { return mk_app({mk_Int_abs_fn(), e1}); }
expr mk_Nat_sub_fn();
bool is_Nat_sub_fn(expr const & e);
inline bool is_Nat_sub(expr const & e) { return is_app(e) && is_Nat_sub_fn(arg(e, 0)); }
inline expr mk_Nat_sub(expr const & e1, expr const & e2) { return mk_app({mk_Nat_sub_fn(), e1, e2}); }
expr mk_Nat_neg_fn();
bool is_Nat_neg_fn(expr const & e);
inline bool is_Nat_neg(expr const & e) { return is_app(e) && is_Nat_neg_fn(arg(e, 0)); }
inline expr mk_Nat_neg(expr const & e1) { return mk_app({mk_Nat_neg_fn(), e1}); }
}
