/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
class io_state;

bool is_equation(expr const & e);
expr const & equation_lhs(expr const & e);
expr const & equation_rhs(expr const & e);
expr mk_equation(expr const & lhs, expr const & rhs, bool ignore_if_unused = false);
/** \brief Return true if e is of the form <tt>fun a_1 ... a_n, equation</tt> */
bool is_lambda_equation(expr const & e);

/** \brief Return true iff e is an equation created with ignore_if_unused flag set to true.
    \pre is_equation(e) */
bool ignore_equation_if_unused(expr const & e);

/** \brief Placeholder to indicate no equations were provided (e.g., to a match-with expression) */
expr mk_no_equation();
bool is_no_equation(expr const & e);
/** \brief Return true if e is of the form <tt>fun a_1 ... a_n, no_equation</tt> */
bool is_lambda_no_equation(expr const & e);

expr mk_inaccessible(expr const & e);
bool is_inaccessible(expr const & e);

/** \brief Construct the "as pattern" <tt>lhs@rhs</tt> */
expr mk_as_pattern(expr const & lhs, expr const & rhs);
bool is_as_pattern(expr const & e);
expr get_as_pattern_lhs(expr const & e);
expr get_as_pattern_rhs(expr const & e);


struct equations_header {
    unsigned   m_num_fns{0};              /* number of functions being defined */
    list<name> m_fn_names;                /* local names for functions */
    list<name> m_fn_actual_names;         /* Full qualified name and/or private name */
    bool       m_is_private{false};       /* if true, it must be a private definition */
    bool       m_is_lemma{false};         /* if true, equations are defining a lemma */
    bool       m_is_meta{false};          /* the auxiliary declarations should be tagged as meta */
    bool       m_is_noncomputable{false}; /* if true, equation is not computable and code should not be generated */
    bool       m_aux_lemmas{false};       /* if true, we must create equation lemmas and induction principle */
    /* m_prev_errors is true when errors have already being found processing the file,
       and we should minimize error reporting */
    bool       m_prev_errors{false};
    bool       m_gen_code{true};          /* if true, generate byte code for recursive equations */
    equations_header() {}
    equations_header(unsigned num_fns):m_num_fns(num_fns) {}
};

bool operator==(equations_header const & h1, equations_header const & h2);
inline bool operator!=(equations_header const & h1, equations_header const & h2) { return !(h1 == h2); }

expr mk_equations(equations_header const & header, unsigned num_eqs, expr const * eqs, expr const & wf_tacs);
expr mk_equations(equations_header const & header, unsigned num_eqs, expr const * eqs);
expr update_equations(expr const & eqns, buffer<expr> const & new_eqs);
expr update_equations(expr const & eqns, equations_header const & header);
expr remove_wf_annotation_from_equations(expr const & eqns);

bool is_equations(expr const & e);
bool is_wf_equations(expr const & e);
unsigned equations_size(expr const & e);
equations_header const & get_equations_header(expr const & e);
unsigned equations_num_fns(expr const & e);
void to_equations(expr const & e, buffer<expr> & eqns);
expr const & equations_wf_tactics(expr const & e);

/** \brief Return true if \c e is an auxiliary macro used to store the result of mutually recursive declarations.
    For example, if a set of recursive equations is defining \c n mutually recursive functions, we wrap
    the \c n resulting functions (and their types) with an \c equations_result macro. */
bool is_equations_result(expr const & e);
expr mk_equations_result(unsigned n, expr const * rs);
inline expr mk_equations_result(expr const & e) { return mk_equations_result(1, &e); }
unsigned get_equations_result_size(expr const & e);
expr const & get_equations_result(expr const & e, unsigned i);

void initialize_equations();
void finalize_equations();
}
