/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/app_builder_tactics.h"

namespace lean {
struct app_builder_cache_helper {
    typedef std::unique_ptr<app_builder_cache> cache_ptr;
    cache_ptr m_cache_ptr;

    void ensure_compatible(environment const & env) {
        if (!m_cache_ptr || !is_eqp(env, m_cache_ptr->env())) {
            m_cache_ptr.reset(new app_builder_cache(env));
        }
    }
};

MK_THREAD_LOCAL_GET_DEF(app_builder_cache_helper, get_abch);

app_builder_cache & get_app_builder_cache_for(environment const & env) {
    get_abch().ensure_compatible(env);
    return *get_abch().m_cache_ptr.get();
}

vm_obj tactic_mk_app(vm_obj const & c, vm_obj const & as, vm_obj const & _s) {
    tactic_state const & s = to_tactic_state(_s);
    try {
        metavar_context mctx   = s.mctx();
        type_context ctx       = mk_type_context_for(s, mctx);
        app_builder b          = mk_app_builder_for(ctx);
        buffer<expr> args;
        to_buffer_expr(as, args);
        expr r                 = b.mk_app(to_name(c), args.size(), args.data());
        return mk_tactic_success(to_obj(r), s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

void initialize_app_builder_tactics() {
    DECLARE_VM_BUILTIN(name({"tactic", "mk_app"}),   tactic_mk_app);
}

void finalize_app_builder_tactics() {
}
}
