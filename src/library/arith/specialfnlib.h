/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"

namespace lean {
// Special functions library

expr mk_exp_fn();
inline expr Exp(expr const & e) { return mk_app(mk_exp_fn(), e); }

expr mk_log_fn();
inline expr Log(expr const & e) { return mk_app(mk_log_fn(), e); }

expr mk_real_pi();

expr mk_sin_fn();
inline expr Sin(expr const & e) { return mk_app(mk_sin_fn(), e); }

expr mk_cos_fn();
inline expr Cos(expr const & e) { return mk_app(mk_cos_fn(), e); }

expr mk_tan_fn();
inline expr Tan(expr const & e) { return mk_app(mk_tan_fn(), e); }

expr mk_cot_fn();
inline expr Cot(expr const & e) { return mk_app(mk_cot_fn(), e); }

expr mk_sec_fn();
inline expr Sec(expr const & e) { return mk_app(mk_sec_fn(), e); }

expr mk_csc_fn();
inline expr Csc(expr const & e) { return mk_app(mk_csc_fn(), e); }

expr mk_sinh_fn();
inline expr Sinh(expr const & e) { return mk_app(mk_sinh_fn(), e); }

expr mk_cosh_fn();
inline expr Cosh(expr const & e) { return mk_app(mk_cosh_fn(), e); }

expr mk_tanh_fn();
inline expr Tanh(expr const & e) { return mk_app(mk_tanh_fn(), e); }

expr mk_coth_fn();
inline expr Coth(expr const & e) { return mk_app(mk_coth_fn(), e); }

expr mk_sech_fn();
inline expr Sech(expr const & e) { return mk_app(mk_sech_fn(), e); }

expr mk_csch_fn();
inline expr Csch(expr const & e) { return mk_app(mk_csch_fn(), e); }

class environment;
/**
    \brief Import the special function library (if it has not been imported already).
    The (basic) Real Number library is also imported.
*/
void import_specialfnlib(environment & env);
}
