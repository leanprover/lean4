/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "kernel/metavar.h"

namespace lean {
/** \brief Functional object for (incomplete) higher-order unification */
class ho_unifier {
    class imp;
    std::unique_ptr<imp> m_ptr;
public:
    ho_unifier(environment const & env);
    ~ho_unifier();

    /**
        \brief Try to unify \c l and \c r in the context \c ctx using the substitution \c menv.
        By unification, we mean we have to find an assignment for the unassigned metavariables in
        \c l and \c r s.t. \c l and \c r become definitionally equal.
        The unifier may produce a residue: a set of unification problems that could not be solved,
        and were postponed. This set of problems is stored in \c up. The caller should try to instantiate
        the metavariables in the residue using other constraints, and then try to continue the unification.
        Return true if the unification succeeded (modulo residue), and false if the terms can't be unified.

        @param[in] ctx The context for \c l and \c r
        @param[in] l   Expression to be unified with \c r
        @param[in] r   Expression to be unified with \c l
        @param[in,out] menv  Metavariable substitution. \c menv may already contain some instantiated variables when this method is invoked.
        @param[out]    up Delayed unification problems (aka residue), that could not be solved by the unifier.
    */
    bool operator()(context const & ctx, expr const & l, expr const & r, metavar_env & menv, unification_problems & up);

    void clear();

    void set_interrupt(bool flag);
    void interrupt() { set_interrupt(true); }
    void reset_interrupt() { set_interrupt(false); }
};
}
