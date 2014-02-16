/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
/** \brief Return true iff the given expression has free variables. */
bool has_free_vars(expr const & a);
/** \brief Return true iff the given expression does not have free variables. */
inline bool closed(expr const & a) { return !has_free_vars(a); }

/**
   \brief Return \c R s.t. the de Bruijn index of all free variables
   occurring in \c e is in the interval <tt>[0, R)</tt>.
*/
unsigned free_var_range(expr const & e);

/**
    \brief Return true iff \c e constains a free variable <tt>(var i)</tt> s.t. \c i in <tt>[low, high)</tt>.
    \pre low < high
*/
bool has_free_var(expr const & e, unsigned low, unsigned high);
/** \brief Return true iff \c e contains the free variable <tt>(var i)</tt>. */
bool has_free_var(expr const & e, unsigned i);
/** \brief Return true iff \c e contains a free variable >= low. */
bool has_free_var_ge(expr const & e, unsigned low);

/**
   \brief Lower the free variables >= s in \c e by \c d. That is, a free variable <tt>(var i)</tt> s.t.
   <tt>i >= s</tt> is mapped into <tt>(var i-d)</tt>.

   \pre s >= d
   \pre !has_free_var(e, s-d, s, menv)
*/
expr lower_free_vars(expr const & e, unsigned s, unsigned d);
expr lower_free_vars(expr const & e, unsigned d);

/** \brief Lift free variables >= s in \c e by d. */
expr lift_free_vars(expr const & e, unsigned s, unsigned d);
expr lift_free_vars(expr const & e, unsigned d);
}
