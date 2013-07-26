/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"
namespace lean {
/**
   \brief Return true iff the given expression has free variables.
*/
bool has_free_vars(expr const & a);
/**
   \brief Return true iff the given expression does not have free variables.
*/
inline bool closed(expr const & a) { return !has_free_vars(a); }

/**
    \brief Return true iff \c e contains the free variable <tt>(var i)</tt>.
*/
bool has_free_var(expr const & e, unsigned i);

/**
    \brief Return true iff \c e constains a free variable <tt>(var i)</tt> s.t. \c i in <tt>[low, high)</tt>.
    \pre low < high
*/
bool has_free_var(expr const & e, unsigned low, unsigned high);

/**
   \brief Lower the free variables in \c e by d. That is, a free variable <tt>(var i)</tt> is mapped into <tt>(var i-d)</tt>.

   \pre d > 0
   \pre !has_free_var(e, 0, d)
*/
expr lower_free_vars(expr const & e, unsigned d);
}
