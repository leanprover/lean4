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
#include "library/trace.h"
#include "library/replace_visitor.h"
#include "library/fun_info_manager.h"

namespace lean {
static name * g_fun_info = nullptr;
void initialize_fun_info_manager() {
    g_fun_info = new name("fun_info");
    register_trace_class(*g_fun_info);
}

void finalize_fun_info_manager() {
    delete g_fun_info;
}

#define lean_trace_fun_info(Code) lean_trace(*g_fun_info, Code)

static bool is_fun_info_trace_enabled() {
    return is_trace_class_enabled(*g_fun_info);
}

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

/* Store parameter info for fn in \c pinfos and return the dependencies of the resulting type
   (if compute_resulting_deps == true). */
list<unsigned> fun_info_manager::get_core(expr const & fn, buffer<param_info> & pinfos,
                                          unsigned max_args, bool compute_resulting_deps) {
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
    if (compute_resulting_deps)
        return collect_deps(type, locals);
    else
        return list<unsigned>();
}

fun_info fun_info_manager::get(expr const & e) {
    auto it = m_cache_get.find(e);
    if (it != m_cache_get.end())
        return it->second;
    buffer<param_info> pinfos;
    auto result_deps = get_core(e, pinfos, std::numeric_limits<unsigned>::max(), true);
    fun_info r(pinfos.size(), to_list(pinfos), result_deps);
    m_cache_get.insert(mk_pair(e, r));
    return r;
}

fun_info fun_info_manager::get(expr const & e, unsigned nargs) {
    expr_unsigned key(e, nargs);
    auto it = m_cache_get_nargs.find(key);
    if (it != m_cache_get_nargs.end())
        return it->second;
    buffer<param_info> pinfos;
    auto result_deps = get_core(e, pinfos, nargs, true);
    fun_info r(pinfos.size(), to_list(pinfos), result_deps);
    m_cache_get_nargs.insert(mk_pair(key, r));
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
        if (std::find(fwd_deps.begin(), fwd_deps.end(), i) != fwd_deps.end()) {
            return true;
        }
    }
    return false;
}

void fun_info_manager::trace_if_unsupported(expr const & fn, buffer<expr> const & args, unsigned prefix_sz, fun_info const & result) {
    if (!is_fun_info_trace_enabled())
        return;
    fun_info info = get(fn, args.size());
    buffer<param_info> pinfos;
    to_buffer(info.get_params_info(), pinfos);
    /* Check if all remaining arguments are nondependent or
       dependent (but all forward dependencies are propositions or subsingletons) */
    unsigned i = prefix_sz;
    for (; i < pinfos.size(); i++) {
        param_info const & pinfo = pinfos[i];
        if (!pinfo.is_dep())
            continue; /* nondependent argument */
        if (has_nonprop_nonsubsingleton_fwd_dep(i, pinfos))
            break; /* failed i-th argument has a forward dependent that is not a prop nor a subsingleton */
    }
    if (i == pinfos.size())
        return; // It is *cheap* case

    /* Expensive case */
    /* We generate a trace message IF it would be possible to compute more precise information.
       That is, there is an argument that is a proposition and/or subsingleton, but
       the corresponding pinfo is not a marked a prop/subsingleton.
    */
    i = 0;
    for (param_info const & pinfo : result.get_params_info()) {
        if (pinfo.is_prop() || pinfo.is_subsingleton())
            continue;
        expr arg_type = m_ctx.infer(args[i]);
        if (m_ctx.is_prop(arg_type) || m_ctx.mk_subsingleton_instance(arg_type)) {
            lean_trace_fun_info(
                tout() << "approximating function information for '" << fn
                << "', this may affect the effectiveness of the simplifier and congruence closure modules, "
                << "more precise information can be efficiently computed if all parameters are moved to the beginning of the function\n";);
            return;
        }
        i++;
    }
}

unsigned fun_info_manager::get_specialization_prefix_size(expr const & fn, unsigned nargs) {
    /*
      We say a function is "cheap" if it is of the form:

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

      Therefore, we ignore the non-cheap cases, and pretend they are "cheap".
      If tracing is enabled, we produce a tracing message whenever we find
      a non-cheap case.

      This procecure returns the size of group a)
    */
    expr_unsigned key(fn, nargs);
    auto it = m_cache_prefix.find(key);
    if (it != m_cache_prefix.end())
        return it->second;
    fun_info info = get(fn, nargs);
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
    m_cache_prefix.insert(mk_pair(key, prefix_sz));
    return prefix_sz;
}

fun_info fun_info_manager::get_specialized(expr const & a) {
    lean_assert(is_app(a));
    buffer<expr> args;
    expr const & fn        = get_app_args(a, args);
    unsigned prefix_sz     = get_specialization_prefix_size(fn, args.size());
    unsigned num_rest_args = args.size() - prefix_sz;
    expr g = a;
    for (unsigned i = 0; i < num_rest_args; i++)
        g = app_fn(g);
    expr_unsigned key(g, num_rest_args);
    auto it = m_cache_get_spec.find(key);
    if (it != m_cache_get_spec.end()) {
        return it->second;
    }
    /* fun_info is not cached */
    buffer<param_info> pinfos;
    get_core(fn, pinfos, prefix_sz, false);
    for (unsigned i = 0; i < prefix_sz; i++) {
        pinfos[i].m_specialized = true;
    }
    auto result_deps = get_core(g, pinfos, num_rest_args, true);
    fun_info r(pinfos.size(), to_list(pinfos), result_deps);
    m_cache_get_spec.insert(mk_pair(key, r));
    trace_if_unsupported(fn, args, prefix_sz, r);
    return r;
}
}
