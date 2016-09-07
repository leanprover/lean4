/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
struct injectivity_info {
    unsigned m_arity;
    name     m_inv;
    name     m_lemma;
};

optional<injectivity_info> has_inverse(environment const & env, name const & fn);
optional<name> is_inverse(environment const & env, name const & inv);
environment add_injectivity_lemma(environment const & env, name const & lemma, bool persistent);
void initialize_injectivity();
void finalize_injectivity();
}
