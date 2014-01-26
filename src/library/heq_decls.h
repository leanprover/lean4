/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
// Automatically generated file, DO NOT EDIT
#include "kernel/expr.h"
namespace lean {
expr mk_heq_fn();
bool is_heq_fn(expr const & e);
inline bool is_heq(expr const & e) { return is_app(e) && is_heq_fn(arg(e, 0)) && num_args(e) == 5; }
inline expr mk_heq(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_heq_fn(), e1, e2, e3, e4}); }
expr mk_heq_eq_fn();
bool is_heq_eq_fn(expr const & e);
inline expr mk_heq_eq_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_heq_eq_fn(), e1, e2, e3}); }
expr mk_to_eq_fn();
bool is_to_eq_fn(expr const & e);
inline expr mk_to_eq_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_to_eq_fn(), e1, e2, e3, e4}); }
expr mk_to_heq_fn();
bool is_to_heq_fn(expr const & e);
inline expr mk_to_heq_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_to_heq_fn(), e1, e2, e3, e4}); }
expr mk_hrefl_fn();
bool is_hrefl_fn(expr const & e);
inline expr mk_hrefl_th(expr const & e1, expr const & e2) { return mk_app({mk_hrefl_fn(), e1, e2}); }
expr mk_hsymm_fn();
bool is_hsymm_fn(expr const & e);
inline expr mk_hsymm_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_hsymm_fn(), e1, e2, e3, e4, e5}); }
expr mk_htrans_fn();
bool is_htrans_fn(expr const & e);
inline expr mk_htrans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8) { return mk_app({mk_htrans_fn(), e1, e2, e3, e4, e5, e6, e7, e8}); }
expr mk_hcongr_fn();
bool is_hcongr_fn(expr const & e);
inline expr mk_hcongr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8, expr const & e9, expr const & e10) { return mk_app({mk_hcongr_fn(), e1, e2, e3, e4, e5, e6, e7, e8, e9, e10}); }
expr mk_TypeM();
bool is_TypeM(expr const & e);
expr mk_hfunext_fn();
bool is_hfunext_fn(expr const & e);
inline expr mk_hfunext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8) { return mk_app({mk_hfunext_fn(), e1, e2, e3, e4, e5, e6, e7, e8}); }
expr mk_hsfunext_fn();
bool is_hsfunext_fn(expr const & e);
inline expr mk_hsfunext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_hsfunext_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_hallext_fn();
bool is_hallext_fn(expr const & e);
inline expr mk_hallext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_hallext_fn(), e1, e2, e3, e4, e5, e6}); }
}
