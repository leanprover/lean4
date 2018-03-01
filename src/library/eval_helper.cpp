/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/eval_helper.h"
#include "library/tactic/tactic_state.h"

namespace lean {

eval_helper::eval_helper(environment const & env, options const & opts, name const & fn) :
        m_env(env), m_opts(opts), m_tc(env, opts, transparency_mode::None),
        m_vms(env, opts), m_prof(m_vms, opts), m_fn(fn) {
    auto d = env.get(m_fn);
    m_ty = m_tc.whnf(d.get_type());

    if (auto vm_decl = m_vms.get_decl(m_fn)) {
        m_arity = vm_decl->get_arity();
    } else {
        throw exception(sstream() << "no vm declaration found for " << m_fn);
    }
}

vm_obj eval_helper::invoke_fn() {
    /* We use `scope_vm_state` to set thread local g_vm_state which is used
       to collect performance numbers when profiling. */
    scope_vm_state scope(m_vms);
    unsigned arity = m_vms.get_decl(m_fn)->get_arity();
    if (arity > m_args.size()) {
        throw exception(sstream() << "cannot evaluate function: " << m_args.size()
                                  << " arguments given but expected " << arity);
    }
    std::reverse(m_args.begin(), m_args.end());
    return m_vms.invoke(m_fn, m_args.size(), m_args.data());
}

optional<vm_obj> eval_helper::try_exec_io() {
    if (is_app_of(m_ty, get_io_name(), 1)) {
        m_args.push_back(mk_vm_simple(0)); // "world state"
        auto r = invoke_fn();
        if (auto error = is_io_error(r)) {
            throw exception(io_error_to_string(*error));
        } else if (auto result = is_io_result(r)) {
            return result;
        } else {
            throw exception("unexpected vm result of io expression");
        }
    }
    return optional<vm_obj>();
}

optional<vm_obj> eval_helper::try_exec_tac() {
    if (is_constant(get_app_fn(m_ty), get_tactic_name())) {
        auto tac_st = mk_tactic_state_for(m_env, m_opts, m_fn, m_tc.mctx(), m_tc.lctx(), mk_true());
        m_args.push_back(tactic::to_obj(tac_st));
        auto r = invoke_fn();
        if (tactic::is_result_success(r)) {
            return optional<vm_obj>(tactic::get_success_value(r));
        } else if (auto ex = tactic::is_exception(m_vms, r)) {
            throw formatted_exception(std::get<1>(*ex), std::get<0>(*ex));
        } else {
            throw exception("tactic failed");
        }
    }
    return optional<vm_obj>();
}

optional<vm_obj> eval_helper::try_exec() {
    if (auto res = try_exec_io()) return res;
    if (auto res = try_exec_tac()) return res;
    return optional<vm_obj>();
}

}
