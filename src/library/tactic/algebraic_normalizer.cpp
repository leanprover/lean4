/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/class.h"
#include "library/trace.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/algebraic_normalizer.h"

namespace lean {
static name * g_algebra = nullptr;

MK_THREAD_LOCAL_GET_DEF(algebraic_info_manager::data_ptr, get_alg_info_data);

algebraic_info_manager::algebraic_info_manager(type_context_old & ctx):
    m_ctx(ctx) {
    data_ptr p = get_alg_info_data();
    if (p &&
        is_eqp(ctx.env(), p->m_env) &&
        is_decl_eqp(ctx.lctx(), p->m_lctx)) {
        m_data = p;
    } else {
        m_data = std::make_shared<data>();
        m_data->m_env     = ctx.env();
        m_data->m_lctx    = ctx.lctx();
        m_data->m_symbols = get_class_attribute_symbols(ctx.env(), *g_algebra);
    }
}

algebraic_info_manager::~algebraic_info_manager() {
    get_alg_info_data() = m_data;
}

algebraic_info_ref algebraic_info_manager::get_info(expr const & op) {
    expr const & fn = get_app_fn(op);
    if (!is_constant(fn))
        return algebraic_info_ref(nullptr);
    if (!m_data->m_symbols.contains(const_name(fn)))
        return algebraic_info_ref(nullptr);
    auto it = m_data->m_op_info.find(op);
    if (it != m_data->m_op_info.end())
        return it->second;
    // TODO(Leo):
    return algebraic_info_ref(nullptr);
}

vm_obj tactic_trace_algebra_info(vm_obj const & op, vm_obj const & _s) {
    tactic_state const & s = tactic::to_state(_s);
    type_context_old ctx = mk_type_context_for(s);
    algebraic_info_manager m(ctx);
    if (m.get_info(to_expr(op))) {
        tout() << "operator has algebraic info\n";
    } else {
        tout() << "operator does not have algebraic info\n";
    }
    return tactic::mk_success(mk_vm_unit(), s);
}

void initialize_algebraic_normalizer() {
    register_trace_class("algebra");

    g_algebra = new name("algebra");
    register_class_symbol_tracking_attribute(*g_algebra, "mark class whose instances are relevant for the algebraic normalizer");

    DECLARE_VM_BUILTIN(name({"tactic", "trace_algebra_info"}), tactic_trace_algebra_info);
}

void finalize_algebraic_normalizer() {
    delete g_algebra;
}
}
