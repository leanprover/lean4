/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "library/ho_unifier.h"

namespace lean {
class ho_unifier::imp {
    environment    m_env;
    volatile bool  m_interrupted;

public:
    imp(environment const & env):m_env(env) {
        m_interrupted = false;
        // TODO(Leo)
    }

    bool unify(context const & ctx, expr const & l, expr const & r, metavar_env & menv, unification_problems & up) {
        // TODO(Leo)
        return false;
    }

    void clear() {
        // TODO(Leo)
    }

    void set_interrupt(bool flag) {
        m_interrupted = flag;
    }
};

ho_unifier::ho_unifier(environment const & env):m_ptr(new imp(env)) {}
ho_unifier::~ho_unifier() {}
void ho_unifier::clear() { m_ptr->clear(); }
void ho_unifier::set_interrupt(bool flag) { m_ptr->set_interrupt(flag); }
bool ho_unifier::operator()(context const & ctx, expr const & l, expr const & r, metavar_env & menv, unification_problems & up) {
    return m_ptr->unify(ctx, l, r, menv, up);
}
}
