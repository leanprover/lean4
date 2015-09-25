/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/expr.h"
#include "library/blast/state.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {
class context {
    environment m_env;
    io_state    m_ios;
    name_set    m_lemma_hints;
    name_set    m_unfold_hints;
public:
    context(environment const & env, io_state const & ios, list<name> const & ls, list<name> const & ds):
        m_env(env), m_ios(ios), m_lemma_hints(to_name_set(ls)), m_unfold_hints(to_name_set(ds)) {
    }
    optional<expr> operator()(goal const &) {
        return none_expr();
    }
};
}
optional<expr> blast_goal(environment const & env, io_state const & ios, list<name> const & ls, list<name> const & ds,
                          goal const & g) {
    blast::scope_hash_consing scope;
    blast::context c(env, ios, ls, ds);
    return c(g);
}
}
