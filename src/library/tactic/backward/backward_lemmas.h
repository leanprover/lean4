/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/priority_queue.h"
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/head_map.h"
#include "library/type_context.h"
#include "library/vm/vm.h"
#include "library/tactic/gexpr.h"

namespace lean {
environment add_backward_lemma(environment const & env, io_state const & ios, name const & c, unsigned prio, name const & ns, bool persistent);
bool is_backward_lemma(environment const & env, name const & n);
void get_backward_lemmas(environment const & env, buffer<name> & r);
void initialize_backward_lemmas();
void finalize_backward_lemmas();

typedef gexpr backward_lemma;
struct backward_lemma_prio_fn {
    priority_queue<name, name_quick_cmp> m_prios;
    backward_lemma_prio_fn(priority_queue<name, name_quick_cmp> const & prios):m_prios(prios) {}
    unsigned operator()(backward_lemma const & r) const;
};

class backward_lemma_index {
    head_map_prio<backward_lemma, backward_lemma_prio_fn> m_index;
public:
    backward_lemma_index(type_context_old & ctx);
    void insert(type_context_old & ctx, expr const & href);
    void erase(type_context_old & ctx, expr const & href);
    list<backward_lemma> find(head_index const & h) const;
};

backward_lemma_index const & to_backward_lemmas(vm_obj const & o);
vm_obj to_obj(backward_lemma_index const & idx);
}
