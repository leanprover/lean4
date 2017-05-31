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

    m_io_iface = m_tc.push_local(
            "_vm_io_iface", mk_constant(get_io_interface_name(), {}),
            mk_inst_implicit_binder_info());
}

void eval_helper::dependency_injection() {
    while (is_pi(m_ty)) {
        auto arg_ty = m_tc.whnf(binding_domain(m_ty));
        optional<expr> arg;

        if (is_constant(get_app_fn(arg_ty), get_io_interface_name())) {
            m_args.push_back(mk_io_interface(m_cmdline_args));
            arg = m_io_iface;
        }

        if (arg) {
            m_ty = m_tc.whnf(instantiate(binding_body(m_ty), *arg));
        } else {
            break;
        }
    }
}

vm_obj eval_helper::invoke_fn() {
    unsigned arity = m_vms.get_decl(m_fn)->get_arity();
    if (arity > m_args.size()) {
        throw exception(sstream() << "cannot evaluate function: " << m_args.size()
                                  << " arguments given but expected " << arity);
    }
    std::reverse(m_args.begin(), m_args.end());
    return m_vms.invoke(m_fn, m_args.size(), m_args.data());
}

optional<vm_obj> eval_helper::try_exec_io() {
    if (is_constant(get_app_fn(m_ty), get_io_name()) && app_arg(app_fn(m_ty)) == m_io_iface) {
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
            return optional<vm_obj>(tactic::get_result_value(r));
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
