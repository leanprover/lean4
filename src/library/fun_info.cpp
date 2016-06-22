/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/expr_maps.h"
#include "library/trace.h"
#include "library/expr_unsigned_map.h"
#include "library/fun_info.h"

namespace lean {
static name * g_fun_info = nullptr;
void initialize_fun_info() {
    g_fun_info = new name("fun_info");
    register_trace_class(*g_fun_info);
}

void finalize_fun_info() {
    delete g_fun_info;
}

#define lean_trace_fun_info(Code) lean_trace(*g_fun_info, Code)

static bool is_fun_info_trace_enabled() {
    return is_trace_class_enabled(*g_fun_info);
}

struct fun_info_cache {
    typedef expr_map<fun_info>          cache;
    typedef expr_unsigned_map<fun_info> narg_cache;
    typedef expr_unsigned_map<unsigned> prefix_cache;
    environment  m_env;
    cache        m_cache_get;
    narg_cache   m_cache_get_nargs;
    narg_cache   m_cache_get_spec;
    prefix_cache m_cache_prefix;
    fun_info_cache(environment const & env):m_env(env) {}
};

struct fun_info_cache_helper {
    typedef std::unique_ptr<fun_info_cache> cache_ptr;
    cache_ptr m_cache_ptr;

    void ensure_compatible(environment const & env) {
        if (!m_cache_ptr || !is_eqp(env, m_cache_ptr->m_env)) {
            m_cache_ptr.reset(new fun_info_cache(env));
        }
    }
};

MK_THREAD_LOCAL_GET_DEF(fun_info_cache_helper, get_fich);

fun_info_cache & get_fun_info_cache_for(environment const & env) {
    get_fich().ensure_compatible(env);
    return *get_fich().m_cache_ptr.get();
}

void clear_fun_info_cache() {
    get_fich().m_cache_ptr.reset();
}

static list<unsigned> collect_deps(expr const & type, buffer<expr> const & locals) {
    buffer<unsigned> deps;
    for_each(type, [&](expr const & e, unsigned) {
            if (is_local(e)) {
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
static list<unsigned> get_core(type_context & ctx,
                               expr const & fn, buffer<param_info> & pinfos,
                               unsigned max_args, bool compute_resulting_deps) {
    expr type = ctx.relaxed_try_to_pi(ctx.infer(fn));
    type_context::tmp_locals locals(ctx);
    unsigned i = 0;
    while (is_pi(type)) {
        if (i == max_args)
            break;
        expr local      = locals.push_local_from_binding(type);
        expr local_type = ctx.infer(local);
        expr new_type   = ctx.relaxed_try_to_pi(instantiate(binding_body(type), local));
        bool spec       = false;
        bool is_prop    = ctx.is_prop(local_type);
        bool is_sub     = is_prop;
        bool is_dep     = !closed(binding_body(type));
        if (!is_sub) {
            // TODO(Leo): check if the following line is a performance bottleneck.
            is_sub = static_cast<bool>(ctx.mk_subsingleton_instance(local_type));
        }
        pinfos.emplace_back(spec,
                            binding_info(type).is_implicit(),
                            binding_info(type).is_inst_implicit(),
                            is_prop, is_sub, is_dep, collect_deps(local_type, locals.as_buffer()));
        type = new_type;
        i++;
    }
    if (compute_resulting_deps)
        return collect_deps(type, locals.as_buffer());
    else
        return list<unsigned>();
}

fun_info get_fun_info(type_context & ctx, expr const & e) {
    fun_info_cache & cache = get_fun_info_cache_for(ctx.env());
    auto it = cache.m_cache_get.find(e);
    if (it != cache.m_cache_get.end())
        return it->second;
    buffer<param_info> pinfos;
    auto result_deps = get_core(ctx, e, pinfos, std::numeric_limits<unsigned>::max(), true);
    fun_info r(pinfos.size(), to_list(pinfos), result_deps);
    cache.m_cache_get.insert(mk_pair(e, r));
    return r;
}

fun_info get_fun_info(type_context & ctx, expr const & e, unsigned nargs) {
    fun_info_cache & cache = get_fun_info_cache_for(ctx.env());
    expr_unsigned key(e, nargs);
    auto it = cache.m_cache_get_nargs.find(key);
    if (it != cache.m_cache_get_nargs.end())
        return it->second;
    buffer<param_info> pinfos;
    auto result_deps = get_core(ctx, e, pinfos, nargs, true);
    fun_info r(pinfos.size(), to_list(pinfos), result_deps);
    cache.m_cache_get_nargs.insert(mk_pair(key, r));
    return r;
}

/* Return true if there is j s.t. pinfos[j] is not a
   proposition/subsingleton and it dependends of argument i */
static bool has_nonprop_nonsubsingleton_fwd_dep(unsigned i, buffer<param_info> const & pinfos) {
    for (unsigned j = i+1; j < pinfos.size(); j++) {
        param_info const & fwd_pinfo = pinfos[j];
        if (fwd_pinfo.is_prop() || fwd_pinfo.is_subsingleton())
            continue;
        auto const & back_deps        = fwd_pinfo.get_back_deps();
        if (std::find(back_deps.begin(), back_deps.end(), i) != back_deps.end()) {
            return true;
        }
    }
    return false;
}

static void trace_if_unsupported(type_context & ctx,
                          expr const & fn, buffer<expr> const & args, unsigned prefix_sz, fun_info const & result) {
    if (!is_fun_info_trace_enabled())
        return;
    fun_info info = get_fun_info(ctx, fn, args.size());
    buffer<param_info> pinfos;
    to_buffer(info.get_params_info(), pinfos);
    /* Check if all remaining arguments are nondependent or
       dependent (but all forward dependencies are propositions or subsingletons) */
    unsigned i = prefix_sz;
    for (; i < pinfos.size(); i++) {
        param_info const & pinfo = pinfos[i];
        if (!pinfo.has_fwd_deps())
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
        expr arg_type = ctx.infer(args[i]);
        if (ctx.is_prop(arg_type) || ctx.mk_subsingleton_instance(arg_type)) {
            lean_trace_fun_info(
                tout() << "approximating function information for '" << fn
                << "', this may affect the effectiveness of the simplifier and congruence closure modules, "
                << "more precise information can be efficiently computed if all parameters are moved to the "
                << "beginning of the function\n";);
            return;
        }
        i++;
    }
}

unsigned get_specialization_prefix_size(type_context & ctx, expr const & fn, unsigned nargs) {
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
    fun_info_cache & cache = get_fun_info_cache_for(ctx.env());
    expr_unsigned key(fn, nargs);
    auto it = cache.m_cache_prefix.find(key);
    if (it != cache.m_cache_prefix.end())
        return it->second;
    fun_info info = get_fun_info(ctx, fn, nargs);
    buffer<param_info> pinfos;
    to_buffer(info.get_params_info(), pinfos);
    /* Compute "prefix": 0 or more parameters s.t.
       at lest one forward dependency is not a proposition or a subsingleton */
    unsigned i = 0;
    for (; i < pinfos.size(); i++) {
        param_info const & pinfo = pinfos[i];
        if (!pinfo.has_fwd_deps())
            break;
        /* search for forward dependency that is not a proposition nor a subsingleton */
        if (!has_nonprop_nonsubsingleton_fwd_dep(i, pinfos))
            break;
    }
    unsigned prefix_sz = i;
    cache.m_cache_prefix.insert(mk_pair(key, prefix_sz));
    return prefix_sz;
}

fun_info get_specialized_fun_info(type_context & ctx, expr const & a) {
    lean_assert(is_app(a));
    buffer<expr> args;
    expr const & fn        = get_app_args(a, args);
    unsigned prefix_sz     = get_specialization_prefix_size(ctx, fn, args.size());
    unsigned num_rest_args = args.size() - prefix_sz;
    expr g = a;
    for (unsigned i = 0; i < num_rest_args; i++)
        g = app_fn(g);
    fun_info_cache & cache = get_fun_info_cache_for(ctx.env());
    expr_unsigned key(g, num_rest_args);
    auto it = cache.m_cache_get_spec.find(key);
    if (it != cache.m_cache_get_spec.end()) {
        return it->second;
    }
    /* fun_info is not cached */
    buffer<param_info> pinfos;
    get_core(ctx, fn, pinfos, prefix_sz, false);
    for (unsigned i = 0; i < prefix_sz; i++) {
        pinfos[i].set_specialized();
    }
    auto result_deps = get_core(ctx, g, pinfos, num_rest_args, true);
    fun_info r(pinfos.size(), to_list(pinfos), result_deps);
    cache.m_cache_get_spec.insert(mk_pair(key, r));
    trace_if_unsupported(ctx, fn, args, prefix_sz, r);
    return r;
}
}
