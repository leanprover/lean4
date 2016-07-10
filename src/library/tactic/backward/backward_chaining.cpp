/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/backward/backward_lemmas.h"

#ifndef LEAN_DEFAULT_BACKWARD_CHAINING_MAX_DEPTH
#define LEAN_DEFAULT_BACKWARD_CHAINING_MAX_DEPTH 8
#endif

namespace lean {
static name * g_backward_chaining_max_depth = nullptr;

unsigned get_backward_chaining_max_depth(options const & o) {
    return o.get_unsigned(*g_backward_chaining_max_depth, LEAN_DEFAULT_BACKWARD_CHAINING_MAX_DEPTH);
}

struct back_chaining_fn {
    tactic_state         m_initial_state;
    type_context         m_ctx;
    bool                 m_use_instances;
    unsigned             m_max_depth;
    vm_obj               m_leaf_tactic;
    backward_lemma_index m_lemmas;

    back_chaining_fn(tactic_state const & s, transparency_mode md, bool use_instances,
                     unsigned max_depth, vm_obj const & leaf_tactic,
                     list<expr> const & extra_lemmas):
        m_initial_state(s),
        m_ctx(mk_type_context_for(s, md)),
        m_use_instances(use_instances),
        m_max_depth(max_depth),
        m_leaf_tactic(leaf_tactic),
        m_lemmas(backward_lemma_index(m_ctx)) {
        for (expr const & extra : extra_lemmas) {
            m_lemmas.insert(m_ctx, extra);
        }
    }

    vm_obj operator()() {
        // TODO(Leo):
        return mk_tactic_exception("back_chaining entry point", m_initial_state);
    }
};

vm_obj back_chaining(transparency_mode md, bool use_instances, unsigned max_depth,
                     vm_obj const & leaf_tactic, list<expr> const & extra_lemmas, tactic_state const & s) {
    return back_chaining_fn(s, md, use_instances, max_depth, leaf_tactic, extra_lemmas)();
}

vm_obj tactic_backward_chaining(vm_obj const & md, vm_obj const & use_instances, vm_obj const & max_depth,
                                vm_obj const & leaf_tactic, vm_obj const & extra_lemmas, vm_obj const & s) {
    return back_chaining(to_transparency_mode(md), to_bool(use_instances),
                         force_to_unsigned(max_depth, std::numeric_limits<unsigned>::max()),
                         leaf_tactic, to_list_expr(extra_lemmas), to_tactic_state(s));
}

void initialize_backward_chaining() {
    DECLARE_VM_BUILTIN(name({"tactic", "backward_chaining_core"}),   tactic_backward_chaining);
    g_backward_chaining_max_depth = new name{"back_chaining", "max_depth"};
    register_unsigned_option(*g_backward_chaining_max_depth, LEAN_DEFAULT_BACKWARD_CHAINING_MAX_DEPTH,
                             "maximum number of nested backward chaining steps");
}

void finalize_backward_chaining() {
    delete g_backward_chaining_max_depth;
}
}
