/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/attribute_manager.h"
#include "library/io_state.h"
#include "library/head_map.h"
#include "library/blast/gexpr.h"

namespace lean {
environment add_backward_lemma(environment const & env, io_state const & ios, name const & c, unsigned prio, name const & ns, bool persistent);
bool is_backward_lemma(environment const & env, name const & n);
void get_backward_lemmas(environment const & env, buffer<name> & r);
void initialize_backward_lemmas();
void finalize_backward_lemmas();
namespace blast {
typedef gexpr backward_lemma;
struct backward_lemma_prio_fn { unsigned operator()(backward_lemma const & r) const; };
/* The following indices are based on blast current set of opaque/reducible constants. They
   must be rebuilt whenever a key is "unfolded by blast */
class backward_lemma_index {
    head_map_prio<backward_lemma, backward_lemma_prio_fn> m_index;
public:
    void init();
    void insert(expr const & href);
    void erase(expr const & href);
    list<backward_lemma> find(head_index const & h) const;
};
}}
