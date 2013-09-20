/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include "util/list.h"
#include "util/sexpr/options.h"
#include "kernel/metavar.h"

namespace lean {
/** \brief Functional object for (incomplete) higher-order unification */
class ho_unifier {
    class imp;
    std::unique_ptr<imp> m_ptr;
public:
    ho_unifier(environment const & env, options const & opts = options());
    ~ho_unifier();

    typedef list<std::tuple<context, expr, expr>> residue;
    typedef std::pair<metavar_env, residue> result;

    /**
        \brief Try to unify \c l and \c r in the context \c ctx using the input substitution \c menv.
        By unification, we mean we have to find an assignment for the unassigned metavariables in
        \c l and \c r s.t. \c l and \c r become definitionally equal.
        The unifier may produce a residue: a set of unification problems
        that could not be solved, and were postponed. The unifier postpones unification problems of the form
        <tt>(?M1 ...) == (?M2 ...)</tt> where \c M1 and \c M2 are unassigned metavariables.
        The result is a list of pairs: substitution (in the form of \c metavar_env) and residue.
        Each pair is a possible solution. The resultant \c metavar_env may contain new metavariables.
        The empty list represents failure.
    */
    list<result> operator()(context const & ctx, expr const & l, expr const & r, metavar_env const & menv);

    void set_interrupt(bool flag);
    void interrupt() { set_interrupt(true); }
    void reset_interrupt() { set_interrupt(false); }
};
}
