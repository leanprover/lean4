/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/metavar.h"
namespace lean {
/**
   \brief Return true iff the given expression has free variables.
*/
bool has_free_vars(expr const & a);
/**
   \brief Return true iff the given expression does not have free variables.
*/
inline bool closed(expr const & a) { return !has_free_vars(a); }

class metavar_env;
/**
   \brief Return \c R s.t. the de Bruijn index of all free variables
   occurring in \c e is in the interval <tt>[0, R)</tt>.

   \pre All metavariables occurring in \c e must have been created
   at \c menv.

   \remark Regarding metavariables, if a metavariable \c m was defined
   in a context \c ctx and <tt>ctx.size() == R</tt>, then \c m can
   only contain free variables in the range <tt>[0, R)</tt>

   So, if \c m does not have an associated local context, the answer is just \c R.
   If \c m has an associated local context, we process it using the following rules

   [inst:s v] R  ===>  if s >= R then R else max(R-1, range_of(v))
   [lift:s:n] R  ===>  if s >= R then R else R + n
*/
unsigned free_var_range(expr const & e, metavar_env const & menv);
unsigned free_var_range(expr const & e);

/**
    \brief Return true iff \c e constains a free variable <tt>(var i)</tt> s.t. \c i in <tt>[low, high)</tt>.
    \pre low < high

    \remark If menv is not none, then we use \c free_var_range to compute the free variables that may
    occur in a metavariable.
*/
bool has_free_var(expr const & e, unsigned low, unsigned high, optional<metavar_env> const & menv);
bool has_free_var(expr const & e, unsigned low, unsigned high, metavar_env const & menv);
bool has_free_var(expr const & e, unsigned low, unsigned high);
/**
    \brief Return true iff \c e contains the free variable <tt>(var i)</tt>.
*/
bool has_free_var(expr const & e, unsigned i, optional<metavar_env> const & menv);
bool has_free_var(expr const & e, unsigned i, metavar_env const & menv);
bool has_free_var(expr const & e, unsigned i);

bool has_free_var(context_entry const & e, unsigned low, unsigned high, metavar_env const & menv);

/**
   \brief Lower the free variables >= s in \c e by \c d. That is, a free variable <tt>(var i)</tt> s.t.
   <tt>i >= s</tt> is mapped into <tt>(var i-d)</tt>.

   \pre s >= d
   \pre !has_free_var(e, s-d, s, menv)

   \remark The parameter menv is only used for debugging purposes
*/
expr lower_free_vars(expr const & e, unsigned s, unsigned d, optional<metavar_env> const & menv);
expr lower_free_vars(expr const & e, unsigned s, unsigned d, metavar_env const & menv);
expr lower_free_vars(expr const & e, unsigned s, unsigned d);
expr lower_free_vars(expr const & e, unsigned d, optional<metavar_env> const & menv);
expr lower_free_vars(expr const & e, unsigned d, metavar_env const & menv);
expr lower_free_vars(expr const & e, unsigned d);

context_entry lower_free_vars(context_entry const & e, unsigned s, unsigned d, metavar_env const & menv);

/**
   \brief Lift free variables >= s in \c e by d.

   \remark When the parameter menv is not none, this function will minimize the use
   of the local entry lift in metavariables occurring in \c e.
*/
expr lift_free_vars(expr const & e, unsigned s, unsigned d, optional<metavar_env> const & menv);
expr lift_free_vars(expr const & e, unsigned s, unsigned d);
expr lift_free_vars(expr const & e, unsigned s, unsigned d, metavar_env const & menv);
expr lift_free_vars(expr const & e, unsigned d, optional<metavar_env> const & menv);
expr lift_free_vars(expr const & e, unsigned d, metavar_env const & menv);
expr lift_free_vars(expr const & e, unsigned d);

context_entry lift_free_vars(context_entry const & e, unsigned s, unsigned d, metavar_env const & menv);
}
