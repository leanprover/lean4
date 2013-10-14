/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/pdeque.h"
#include "kernel/formatter.h"
#include "library/elaborator/elaborator.h"

namespace lean {
class elaborator::imp {
    typedef pdeque<unification_constraint> cnstr_queue;

    struct state {
        unsigned    m_id;
        metavar_env m_menv;
        cnstr_queue m_queue;
    };

    environment const &                m_env;
    std::shared_ptr<synthesizer>       m_synthesizer;
    std::shared_ptr<elaborator_plugin> m_plugin;
    bool                               m_interrupted;
public:
    imp(environment const & env, metavar_env const &, unsigned num_cnstrs, unification_constraint const * cnstrs,
        std::shared_ptr<synthesizer> const & s, std::shared_ptr<elaborator_plugin> const & p):
        m_env(env),
        m_synthesizer(s),
        m_plugin(p) {
        m_interrupted = false;

        formatter fmt = mk_simple_formatter();
        for (unsigned i = 0; i < num_cnstrs; i++) {
            std::cout << cnstrs[i].pp(fmt, options(), nullptr, true) << "\n";
        }
    }

    substitution next() {
        // TODO(Leo)
        return substitution();
    }

    void interrupt() {
        m_interrupted = true;
    }
};

elaborator::elaborator(environment const & env,
                       metavar_env const & menv,
                       unsigned num_cnstrs,
                       unification_constraint const * cnstrs,
                       std::shared_ptr<synthesizer> const & s,
                       std::shared_ptr<elaborator_plugin> const & p):
    m_ptr(new imp(env, menv, num_cnstrs, cnstrs, s, p)) {
}

elaborator::elaborator(environment const & env,
                       metavar_env const & menv,
                       context const & ctx, expr const & lhs, expr const & rhs):
    elaborator(env, menv, { mk_eq_constraint(ctx, lhs, rhs, trace()) }) {
}

elaborator::~elaborator() {
}

substitution elaborator::next() {
    return m_ptr->next();
}

void elaborator::interrupt() {
    m_ptr->interrupt();
}
}
