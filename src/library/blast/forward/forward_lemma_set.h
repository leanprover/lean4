/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_tree.h"
#include "kernel/expr.h"

#ifndef LEAN_FORWARD_DEFAULT_PRIORITY
#define LEAN_FORWARD_DEFAULT_PRIORITY 1000
#endif

namespace lean {
/** \brief The forward lemma set is actually a mapping from lemma name to priority */
typedef rb_map<name, unsigned, name_quick_cmp> forward_lemma_set;

environment add_forward_lemma(environment const & env, name const & n, unsigned priority, name const & ns, bool persistent);
bool is_forward_lemma(environment const & env, name const & n);
forward_lemma_set get_forward_lemma_set(environment const & env);

void initialize_forward_lemma_set();
void finalize_forward_lemma_set();
}
