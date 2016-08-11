/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
class old_type_checker;
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
/** \brief Return true if e is of the form <tt>fun a_1 ... a_n, no_equation</tt> */
bool is_lambda_no_equation(expr const & e);

bool is_equations(expr const & e);
bool is_wf_equations(expr const & e);
unsigned equations_size(expr const & e);
unsigned equations_num_fns(expr const & e);
void to_equations(expr const & e, buffer<expr> & eqns);

struct equations_header {
    list<name> m_names;
    bool       m_main;    /* if true, we must add .main suffix to auxiliary declaration */
    bool       m_meta;    /* the auxiliary declarations should be tagged as meta */
    bool       m_lemmas;  /* if true, we must create equation lemmas and induction principle */
};

expr mk_equations(equations_header const & header, unsigned num_eqs, expr const * eqs, expr const & R, expr const & Hwf);
expr mk_equations(equations_header const & header, unsigned num_eqs, expr const * eqs);
expr update_equations(expr const & eqns, buffer<expr> const & new_eqs);

/* TODO(Leo): delete the following versions */
expr mk_equations(unsigned num_fns, unsigned num_eqs, expr const * eqs);
expr mk_equations(unsigned num_fns, unsigned num_eqs, expr const * eqs, expr const & R, expr const & Hwf);
expr const & equations_wf_proof(expr const & e);
expr const & equations_wf_rel(expr const & e);
/* End of delete ------------- */

expr mk_inaccessible(expr const & e);
bool is_inaccessible(expr const & e);

/** \brief Return true if \c e is an auxiliary macro used to store the result of mutually recursive declarations.
    For example, if a set of recursive equations is defining \c n mutually recursive functions, we wrap
    the \c n resulting functions (and their types) with an \c equations_result macro.

    TODO(Leo): delete this after we implement the new equations compiler
*/
bool is_equations_result(expr const & e);
expr mk_equations_result(unsigned n, expr const * rs);
unsigned get_equations_result_size(expr const & e);
expr const & get_equations_result(expr const & e, unsigned i);


void initialize_equations();
void finalize_equations();
}
