/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/replace_visitor.h"
#include "library/fun_info_manager.h"

namespace lean {
fun_info_manager::fun_info_manager(type_context & ctx):
    m_ctx(ctx) {
}

list<unsigned> fun_info_manager::collect_deps(expr const & type, buffer<expr> const & locals) {
    buffer<unsigned> deps;
    for_each(type, [&](expr const & e, unsigned) {
            if (m_ctx.is_tmp_local(e)) {
                unsigned idx;
                for (idx = 0; idx < locals.size(); idx++)
                    if (locals[idx] == e)
                        break;
                if (idx < locals.size() && std::find(deps.begin(), deps.end(), idx) == deps.end())
                    deps.push_back(idx);
            }
            return has_local(e); // continue the search only if e has locals
        });
    std::sort(deps.begin(), deps.end());
    return to_list(deps);
}

fun_info fun_info_manager::get(expr const & e) {
    if (auto r = m_fun_info.find(e))
        return *r;
    expr type = m_ctx.relaxed_try_to_pi(m_ctx.infer(e));
    buffer<param_info> info;
    buffer<expr> locals;
    while (is_pi(type)) {
        expr local      = m_ctx.mk_tmp_local_from_binding(type);
        expr local_type = m_ctx.infer(local);
        expr new_type   = m_ctx.relaxed_try_to_pi(instantiate(binding_body(type), local));
        bool spec       = false;
        bool is_prop    = m_ctx.is_prop(local_type);
        bool is_sub     = is_prop;
        bool is_dep     = !closed(binding_body(type));
        if (!is_sub) {
            // TODO(Leo): check if the following line is a performance bottleneck.
            is_sub = static_cast<bool>(m_ctx.mk_subsingleton_instance(local_type));
        }
        info.emplace_back(spec,
                          binding_info(type).is_implicit(),
                          binding_info(type).is_inst_implicit(),
                          is_prop, is_sub, is_dep, collect_deps(local_type, locals));
        locals.push_back(local);
        type = new_type;
    }
    fun_info r(info.size(), to_list(info), collect_deps(type, locals));
    m_fun_info.insert(e, r);
    return r;
}

fun_info fun_info_manager::get(expr const & e, unsigned nargs) {
    auto r = get(e);
    lean_assert(nargs <= r.get_arity());
    if (nargs == r.get_arity()) {
        return r;
    } else {
        buffer<param_info> pinfos;
        to_buffer(r.get_params_info(), pinfos);
        buffer<unsigned> rdeps;
        to_buffer(r.get_result_dependencies(), rdeps);
        for (unsigned i = nargs; i < pinfos.size(); i++) {
            for (auto d : pinfos[i].get_dependencies()) {
                if (std::find(rdeps.begin(), rdeps.end(), d) == rdeps.end())
                    rdeps.push_back(d);
            }
        }
        pinfos.shrink(nargs);
        return fun_info(nargs, to_list(pinfos), to_list(rdeps));
    }
}

fun_info fun_info_manager::get_specialization(expr const &) {
    // TODO(Leo)
    lean_unreachable();
}
}
