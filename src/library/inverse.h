/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
struct inverse_info {
    unsigned m_arity;
    name     m_inv;
    unsigned m_inv_arity;
    name     m_lemma;
};

optional<inverse_info> has_inverse(environment const & env, name const & fn);
optional<name> is_inverse(environment const & env, name const & inv);
environment add_inverse_lemma(environment const & env, name const & lemma, bool persistent);
void initialize_inverse();
void finalize_inverse();
}
