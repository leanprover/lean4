/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"

namespace lean {
/**
    \brief Create a new metavariable with index \c idx.
*/
expr mk_metavar(unsigned idx);

/**
    \brief Return true iff \c n is a metavariable.
*/
bool is_metavar(expr const & n);

/**
    \brief Return the index of the given metavariable.
    \pre is_metavar(n);
*/
unsigned metavar_idx(expr const & n);

/**
    \brief Return true iff the given expression contains a
    metavariable
*/
bool has_metavar(expr const & e);

/**
    \brief Return true iff \c e contains a metavariable with index
    \c midx
*/
bool has_metavar(expr const & e, unsigned midx);

/**
   \brief Version of lift_free_vars for expressions containing
   metavariables. It will return a new expression such that the
   index idx of free variables is increased by \c n when <tt>idx >=
   s</tt>.

   The suffix mmv stands for "modulo metavariables".
*/
expr lift_free_vars_mmv(expr const & e, unsigned s, unsigned n);

/**
   \brief Version of instantiate for expressions containing
   metavariables. It will return a new expression such that the free
   variables with index \c i are replaced with the expression \c v.
   Moreover, the index \c idx of the free variables with <tt>idx > i</tt> is
   lowered by 1.

   The suffix mmv stands for "modulo metavariables".
*/
expr instantiate_free_var_mmv(expr const & e, unsigned i, expr const & v);

/**
   \brief Version of lower_free_vars for expressions containing
   metavariables. It will return a new expression such that the
   index \c idx of free variables is lowered by \c n when <tt>idx >= s</tt>.

   The suffix mmv stands for "modulo metavariables".
*/
expr lower_free_vars_mmv(expr const & e, unsigned s, unsigned n);

/**
   \brief Instantiate the metavariable with index \c midx in \c e with
   the expression \c v.
*/
expr instantiate_metavar(expr const & e, unsigned midx, expr const & v);

/**
   \brief Return true iff \c e is a delayed substitution expression
   of the form (subst:i c v). The meaning of the expression is
   substitute free variable \c i in \c c with expression \c v.
*/
bool is_subst(expr const & e, unsigned & i, expr & v);

/**
    \brief Return true iff \c e is a delayed substitution expression.
*/
bool is_subst(expr const & e);

/**
    \brief Return true iff \c e is a delayed lift expression of the
    form (lift:s:n c). The meaning of the expression is lift the free
    variables >= \c s by \c n in \c c.
*/
bool is_lift(expr const & e, unsigned & s, unsigned & n);

/**
    \brief Return true iff \c e is a delayed lift expression.
*/
bool is_lift(expr const & e);

/**
    \brief Return true iff \c e is a delayed lower expression of the
    form (lower:s:n c). The meaning of the expression is lower the free
    variables >= \c s by \c n in \c c.
*/
bool is_lower(expr const & e, unsigned & s, unsigned & n);

/**
    \brief Return true iff \c e is a delayed lower expression.
*/
bool is_lower(expr const & e);

/**
    \brief Return true iff \c e is a meta-variable, or a delayed
    instantiation expression, or a delayed lift expression, or a
    delayed lower expression.
*/
bool is_meta(expr const & e);
}

