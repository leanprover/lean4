/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "library/fun_info_manager.h"

namespace lean {
fun_info_manager::fun_info_manager(type_context & ctx):
    m_ctx(ctx) {
}

auto fun_info_manager::get(expr const & e) -> fun_info {
    if (auto r = m_fun_info.find(e))
        return *r;
    expr type = m_ctx.infer(e);
    buffer<arg_info> info;
    buffer<expr> locals;
    while (is_pi(type)) {
        expr local      = m_ctx.mk_tmp_local_from_binding(type);
        expr local_type = m_ctx.infer(local);
        bool is_prop    = m_ctx.is_prop(local_type);
        // TODO(Leo): check if the following line is a performance bottleneck.
        bool is_sub     = is_prop;
        if (!is_sub)
            is_sub = static_cast<bool>(m_ctx.mk_subsingleton_instance(local_type));
        buffer<unsigned> deps;
        for_each(local_type, [&](expr const & e, unsigned) {
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
        locals.push_back(local);
        info.emplace_back(binding_info(type).is_implicit(),
                          binding_info(type).is_inst_implicit(),
                          is_prop, is_sub, to_list(deps));
        type = m_ctx.whnf(instantiate(binding_body(type), local));
    }
    fun_info r(info.size(), to_list(info));
    m_fun_info.insert(e, r);
    return r;
}
}
