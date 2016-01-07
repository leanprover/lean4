/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
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

/* Store parameter info for fn in \c pinfos and return the dependencies of the resulting type. */
list<unsigned> fun_info_manager::get_core(expr const & fn, buffer<param_info> & pinfos, unsigned max_args) {
    expr type = m_ctx.relaxed_try_to_pi(m_ctx.infer(fn));
    buffer<expr> locals;
    unsigned i = 0;
    while (is_pi(type)) {
        if (i == max_args)
            break;
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
        pinfos.emplace_back(spec,
                            binding_info(type).is_implicit(),
                            binding_info(type).is_inst_implicit(),
                            is_prop, is_sub, is_dep, collect_deps(local_type, locals));
        locals.push_back(local);
        type = new_type;
        i++;
    }
    return collect_deps(type, locals);
}

fun_info fun_info_manager::get(expr const & e) {
    if (auto r = m_cache_get.find(e))
        return *r;
    buffer<param_info> pinfos;
    auto result_deps = get_core(e, pinfos, std::numeric_limits<unsigned>::max());
    fun_info r(pinfos.size(), to_list(pinfos), result_deps);
    m_cache_get.insert(e, r);
    return r;
}

fun_info fun_info_manager::get(expr const & e, unsigned nargs) {
    if (auto r = m_cache_get_nargs.find(mk_pair(nargs, e)))
        return *r;
    buffer<param_info> pinfos;
    auto result_deps = get_core(e, pinfos, nargs);
    fun_info r(pinfos.size(), to_list(pinfos), result_deps);
    m_cache_get_nargs.insert(mk_pair(nargs, e), r);
    return r;
}

/* Return true if there is j s.t. pinfos[j] is not a
   proposition/subsingleton and it dependends of argument i */
static bool has_nonprop_nonsubsingleton_fwd_dep(unsigned i, buffer<param_info> const & pinfos) {
    for (unsigned j = i+1; j < pinfos.size(); j++) {
        param_info const & fwd_pinfo = pinfos[j];
        if (fwd_pinfo.is_prop() || fwd_pinfo.is_subsingleton())
            continue;
        auto const & fwd_deps        = fwd_pinfo.get_dependencies();
        if (std::find(fwd_deps.begin(), fwd_deps.end(), i) == fwd_deps.end()) {
            return true;
        }
    }
    return false;
}

fun_info fun_info_manager::get_specialization(expr const & fn, buffer<expr> const & args, buffer<param_info> const & pinfos, list<unsigned> const & result_deps) {
    buffer<param_info> new_pinfos;
    expr type = m_ctx.relaxed_try_to_pi(m_ctx.infer(fn));
    for (unsigned i = 0; i < args.size(); i++) {
        expr new_type           = m_ctx.relaxed_try_to_pi(instantiate(binding_body(type), args[i]));
        expr arg_type           = binding_domain(type);
        param_info new_pinfo    = pinfos[i];
        new_pinfo.m_specialized = true;
        if (!new_pinfo.m_prop) {
            new_pinfo.m_prop         = m_ctx.is_prop(arg_type);
            new_pinfo.m_subsingleton = new_pinfo.m_prop;
        }
        if (!new_pinfo.m_subsingleton) {
            new_pinfo.m_subsingleton = static_cast<bool>(m_ctx.mk_subsingleton_instance(arg_type));
        }
        new_pinfos.push_back(new_pinfo);
        type = new_type;
    }
    bool spec = true;
    return fun_info(new_pinfos.size(), to_list(new_pinfos), result_deps, spec);
}

/* Copy the first prefix_sz entries from pinfos to new_pinfos and mark them as m_specialized = true */
static void copy_prefix(unsigned prefix_sz, buffer<param_info> const & pinfos, buffer<param_info> & new_pinfos) {
    for (unsigned i = 0; i < prefix_sz; i++) {
        new_pinfos.push_back(pinfos[i].mk_specialized());
    }
}

fun_info fun_info_manager::get_specialization(expr const & a) {
    lean_assert(is_app(a));
    buffer<expr> args;
    expr const & fn = get_app_args(a, args);
    fun_info info = get(fn, args.size());
    /*
      We say info is "cheap" if it is of the form:

      a) 0 or more dependent parameters p s.t. there is at least one forward dependency x : C[p]
         which is not a proposition nor a subsingleton.

      b) followed by 0 or more nondependent parameter and/or a dependent parameter
      s.t. all forward dependencies are propositions and subsingletons.

      We have a caching mechanism for the "cheap" case.
      The cheap case cover many commonly used functions

        eq  : Pi {A : Type} (x y : A), Prop
        add : Pi {A : Type} [s : has_add A] (x y : A), A
        inv : Pi {A : Type} [s : has_inv A] (x : A) (h : invertible x), A

      but it doesn't cover

         p : Pi {A : Type} (x : A) {B : Type} (y : B), Prop

      I don't think this is a big deal since we can write it as:

         p : Pi {A : Type} {B : Type} (x : A) (y : B), Prop
    */
    buffer<param_info> pinfos;
    to_buffer(info.get_params_info(), pinfos);
    /* Compute "prefix": 0 or more parameters s.t.
       at lest one forward dependency is not a proposition or a subsingleton */
    unsigned i = 0;
    for (; i < pinfos.size(); i++) {
        param_info const & pinfo = pinfos[i];
        if (!pinfo.is_dep())
            break;
        /* search for forward dependency that is not a proposition nor a subsingleton */
        if (!has_nonprop_nonsubsingleton_fwd_dep(i, pinfos))
            break;
    }
    unsigned prefix_sz = i;
    /* Check if all remaining arguments are nondependent or
       dependent (but all forward dependencies are propositions or subsingletons) */
    for (; i < pinfos.size(); i++) {
        param_info const & pinfo = pinfos[i];
        if (!pinfo.is_dep())
            continue; /* nondependent argument */
        if (has_nonprop_nonsubsingleton_fwd_dep(i, pinfos))
            break; /* failed i-th argument has a forward dependent that is not a prop nor a subsingleton */
    }
    if (i < pinfos.size()) {
        /* Expensive case */
        return get_specialization(fn, args, pinfos, info.get_result_dependencies());
    } else {
        if (prefix_sz == 0)
            return info;
        /* Get g : fn + prefix */
        unsigned num_rest_args = pinfos.size() - prefix_sz;
        expr g = a;
        for (unsigned i = 0; i < num_rest_args; i++)
            g = app_fn(g);
        if (auto r = m_cache_get_spec.find(mk_pair(num_rest_args, g)))
            return *r;
        buffer<param_info> new_pinfos;
        copy_prefix(prefix_sz, pinfos, new_pinfos);
        auto result_deps = get_core(g, new_pinfos, num_rest_args);
        fun_info r(new_pinfos.size(), to_list(new_pinfos), result_deps);
        m_cache_get_spec.insert(mk_pair(num_rest_args, g), r);
        return r;
    }
}
}
