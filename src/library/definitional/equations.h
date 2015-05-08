/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
class type_checker;
class io_state;

bool is_equation(expr const & e);
expr const & equation_lhs(expr const & e);
expr const & equation_rhs(expr const & e);
expr mk_equation(expr const & lhs, expr const & rhs);
/** \brief Return true if e is of the form <tt>fun a_1 ... a_n, equation</tt> */
bool is_lambda_equation(expr const & e);

/** \brief Placeholder to indicate no equations were provided (e.g., to a match-with expression) */
expr mk_no_equation();
bool is_no_equation(expr const & e);

bool is_decreasing(expr const & e);
expr const & decreasing_app(expr const & e);
expr const & decreasing_proof(expr const & e);
expr mk_decreasing(expr const & t, expr const & H);

bool is_equations(expr const & e);
bool is_wf_equations(expr const & e);
unsigned equations_size(expr const & e);
unsigned equations_num_fns(expr const & e);
void to_equations(expr const & e, buffer<expr> & eqns);
expr const & equations_wf_proof(expr const & e);
expr const & equations_wf_rel(expr const & e);
expr mk_equations(unsigned num_fns, unsigned num_eqs, expr const * eqs);
expr mk_equations(unsigned num_fns, unsigned num_eqs, expr const * eqs, expr const & R, expr const & Hwf);
expr update_equations(expr const & eqns, buffer<expr> const & new_eqs);

expr mk_inaccessible(expr const & e);
bool is_inaccessible(expr const & e);

expr compile_equations(type_checker & tc, io_state const & ios, expr const & eqns,
                       expr const & meta, expr const & meta_type);

/** \brief Return true if \c e is an auxiliary macro used to store the result of mutually recursive declarations.
    For example, if a set of recursive equations is defining \c n mutually recursive functions, we wrap
    the \c n resulting functions (and their types) with an \c equations_result macro.
*/
bool is_equations_result(expr const & e);
unsigned get_equations_result_size(expr const & e);
expr const & get_equations_result(expr const & e, unsigned i);

void initialize_equations();
void finalize_equations();
}
