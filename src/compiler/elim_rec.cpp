/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/declaration.h"
#include "kernel/type_checker.h"
#include "library/aux_recursors.h"
#include "library/user_recursors.h"
#include "library/normalize.h"
#include "library/util.h"
#include "compiler/eta_expansion.h"

void pp(lean::environment const & env, lean::expr const & e);

namespace lean {
static expr expand_aux_recursors(environment const & env, expr const & e) {
    auto tc = mk_type_checker(env, name_generator(), [=](name const & n) {
            return !is_aux_recursor(env, n) && !is_user_defined_recursor(env, n);
        });
    constraint_seq cs;
    return normalize(*tc, e, cs);
}

class elim_rec_fn {
    environment           m_env;
    buffer<declaration> & m_aux_decls;
public:
    elim_rec_fn(environment const & env, buffer<declaration> & aux_decls): m_env(env), m_aux_decls(aux_decls) {}

    declaration operator()(declaration const & d) {
        expr v = d.get_value();
        v = expand_aux_recursors(m_env, v);
        v = eta_expand(m_env, v);
        ::pp(m_env, v);
        // TODO(Leo)
        return d;
    }
};

declaration elim_rec(environment const & env, declaration const & d, buffer<declaration> & aux_decls) {
    return elim_rec_fn(env, aux_decls)(d);
}
}
