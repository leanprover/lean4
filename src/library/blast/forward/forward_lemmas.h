/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_tree.h"
#include "kernel/expr.h"

namespace lean {
/** \brief The forward lemma set is actually a mapping from lemma name to priority */
typedef rb_map<name, unsigned, name_quick_cmp> forward_lemmas;

environment add_forward_lemma(environment const & env, name const & n, unsigned priority, name const & ns, bool persistent);
bool is_forward_lemma(environment const & env, name const & n);
forward_lemmas get_forward_lemmas(environment const & env);

void initialize_forward_lemmas();
void finalize_forward_lemmas();
}
