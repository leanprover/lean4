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
#include "library/util.h"
#include "library/constants.h"
#include "library/expr_unsigned_map.h"
#include "library/fun_info.h"
#include "library/cache_helper.h"

namespace lean {
static name * g_fun_info = nullptr;

#define lean_trace_fun_info(Code) lean_trace(*g_fun_info, Code)

static bool is_fun_info_trace_enabled() {
    return is_trace_class_enabled(*g_fun_info);
}

void initialize_fun_info() {
    g_fun_info = new name("fun_info");
    register_trace_class(*g_fun_info);
}

void finalize_fun_info() {
    delete g_fun_info;
}

/* Return the list of dependencies for the given type.
   If it depends on local i, then it also sets pinfos[i].set_has_fwd_deps();
 */
static list<unsigned> collect_deps(expr const & type, buffer<expr> const & locals, buffer<param_info> & pinfos) {
    buffer<unsigned> deps;
    for_each(type, [&](expr const & e, unsigned) {
            if (is_local(e)) {
                unsigned idx;
                for (idx = 0; idx < locals.size(); idx++)
                    if (locals[idx] == e)
                        break;
                if (idx < locals.size() && std::find(deps.begin(), deps.end(), idx) == deps.end()) {
                    deps.push_back(idx);
                    pinfos[idx].set_has_fwd_deps();
                }
            }
            return has_local(e); // continue the search only if e has locals
        });
    std::sort(deps.begin(), deps.end());
    return to_list(deps);
}

/* Store parameter info for fn in \c pinfos and return the dependencies of the resulting type. */
static list<unsigned> get_core(type_context_old & ctx,
                               expr const & fn, buffer<param_info> & pinfos,
                               unsigned max_args) {
    expr type = ctx.relaxed_try_to_pi(ctx.infer(fn));
    type_context_old::tmp_locals locals(ctx);
    unsigned i = 0;
    while (is_pi(type)) {
        if (i == max_args)
            break;
        expr local_type = consume_auto_opt_param(binding_domain(type));
        expr local      = locals.push_local(binding_name(type), local_type, binding_info(type));
        expr new_type   = ctx.relaxed_try_to_pi(instantiate(binding_body(type), local));
        bool is_prop    = ctx.is_prop(local_type);
        bool is_dep     = false; /* it is set by collect_deps */
        pinfos.emplace_back(binding_info(type).is_implicit(),
                            binding_info(type).is_inst_implicit(),
                            is_prop, is_dep, collect_deps(local_type, locals.as_buffer(), pinfos));
        type = new_type;
        i++;
    }
    return collect_deps(type, locals.as_buffer(), pinfos);
}

fun_info get_fun_info(type_context_old & ctx, expr const & e) {
    abstract_context_cache & cache = ctx.get_cache();
    if (auto r = cache.get_fun_info(ctx.mode(), e))
        return *r;
    buffer<param_info> pinfos;
    auto result_deps = get_core(ctx, e, pinfos, std::numeric_limits<unsigned>::max());
    fun_info r(pinfos.size(), to_list(pinfos), result_deps);
    cache.set_fun_info(ctx.mode(), e, r);
    return r;
}

fun_info get_fun_info(type_context_old & ctx, expr const & e, unsigned nargs) {
    abstract_context_cache & cache = ctx.get_cache();
    if (auto r = cache.get_fun_info_nargs(ctx.mode(), e, nargs))
        return *r;
    buffer<param_info> pinfos;
    auto result_deps = get_core(ctx, e, pinfos, nargs);
    fun_info r(pinfos.size(), to_list(pinfos), result_deps);
    cache.set_fun_info_nargs(ctx.mode(), e, nargs, r);
    return r;
}

/* Store subsingleton parameter info for fn in \c ssinfos */
static void get_ss_core(type_context_old & ctx, expr const & fn, buffer<ss_param_info> & ssinfos,
                        unsigned max_args) {
    expr type = ctx.relaxed_try_to_pi(ctx.infer(fn));
    type_context_old::tmp_locals locals(ctx);
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
        if (!is_sub) {
            // TODO(Leo): check if the following line is a performance bottleneck.
            is_sub = static_cast<bool>(ctx.mk_subsingleton_instance(local_type));
        }
        ssinfos.emplace_back(spec, is_sub);
        type = new_type;
        i++;
    }
}

ss_param_infos get_subsingleton_info(type_context_old & ctx, expr const & e) {
    abstract_context_cache & cache = ctx.get_cache();
    if (auto r = cache.get_subsingleton_info(ctx.mode(), e))
        return *r;
    buffer<ss_param_info> ssinfos;
    get_ss_core(ctx, e, ssinfos, std::numeric_limits<unsigned>::max());
    ss_param_infos r = to_list(ssinfos);
    cache.set_subsingleton_info(ctx.mode(), e, r);
    return r;
}

ss_param_infos get_subsingleton_info(type_context_old & ctx, expr const & e, unsigned nargs) {
    abstract_context_cache & cache = ctx.get_cache();
    if (auto r = cache.get_subsingleton_info_nargs(ctx.mode(), e, nargs))
        return *r;
    buffer<ss_param_info> ssinfos;
    get_ss_core(ctx, e, ssinfos, nargs);
    ss_param_infos r = to_list(ssinfos);
    cache.set_subsingleton_info_nargs(ctx.mode(), e, nargs, r);
    return r;
}

/* Return true if there is j s.t. ssinfos[j] is marked as subsingleton,
   and it dependends of argument i */
static bool has_nonsubsingleton_fwd_dep(unsigned i, buffer<param_info> const & pinfos, buffer<ss_param_info> const & ssinfos) {
    lean_assert(pinfos.size() == ssinfos.size());
    for (unsigned j = i+1; j < pinfos.size(); j++) {
        if (ssinfos[j].is_subsingleton())
            continue;
        auto const & back_deps = pinfos[j].get_back_deps();
        if (std::find(back_deps.begin(), back_deps.end(), i) != back_deps.end()) {
            return true;
        }
    }
    return false;
}

static void trace_if_unsupported(type_context_old & ctx, expr const & fn,
                                 buffer<expr> const & args, unsigned prefix_sz, ss_param_infos const & result) {
    lean_assert(args.size() >= length(result));
    if (!is_fun_info_trace_enabled())
        return;
    fun_info info = get_fun_info(ctx, fn, args.size());
    buffer<param_info> pinfos;
    to_buffer(info.get_params_info(), pinfos);
    buffer<ss_param_info> ssinfos;
    to_buffer(get_subsingleton_info(ctx, fn, args.size()), ssinfos);
    lean_assert(pinfos.size() == ssinfos.size());
    /* Check if all remaining arguments are nondependent or
       dependent (but all forward dependencies are subsingletons) */
    unsigned i = prefix_sz;
    for (; i < pinfos.size(); i++) {
        param_info const & pinfo = pinfos[i];
        if (!pinfo.has_fwd_deps())
            continue; /* nondependent argument */
        if (has_nonsubsingleton_fwd_dep(i, pinfos, ssinfos))
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
    for (ss_param_info const & ssinfo : result) {
        if (ssinfo.is_subsingleton())
            continue;
        expr arg_type = ctx.infer(args[i]);
        if (ctx.mk_subsingleton_instance(arg_type)) {
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

unsigned get_specialization_prefix_size(type_context_old & ctx, expr const & fn, unsigned nargs) {
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
    abstract_context_cache & cache = ctx.get_cache();
    if (auto r = cache.get_specialization_prefix_size(ctx.mode(), fn, nargs))
        return *r;
    fun_info info = get_fun_info(ctx, fn, nargs);
    buffer<param_info> pinfos;
    to_buffer(info.get_params_info(), pinfos);
    buffer<ss_param_info> ssinfos;
    to_buffer(get_subsingleton_info(ctx, fn, nargs), ssinfos);
    lean_assert(pinfos.size() == ssinfos.size());
    /* Compute "prefix": 0 or more parameters s.t.
       at lest one forward dependency is not a proposition or a subsingleton */
    unsigned i = 0;
    for (; i < pinfos.size(); i++) {
        param_info const & pinfo = pinfos[i];
        if (!pinfo.has_fwd_deps())
            break;
        /* search for forward dependency that is not a proposition nor a subsingleton */
        if (!has_nonsubsingleton_fwd_dep(i, pinfos, ssinfos))
            break;
    }
    unsigned prefix_sz = i;
    cache.set_specialization_prefix_size(ctx.mode(), fn, nargs, prefix_sz);
    return prefix_sz;
}

ss_param_infos get_specialized_subsingleton_info(type_context_old & ctx, expr const & a) {
    lean_assert(is_app(a));
    buffer<expr> args;
    expr const & fn        = get_app_args(a, args);
    unsigned prefix_sz     = get_specialization_prefix_size(ctx, fn, args.size());
    unsigned num_rest_args = args.size() - prefix_sz;
    expr g = a;
    for (unsigned i = 0; i < num_rest_args; i++)
        g = app_fn(g);
    abstract_context_cache & cache = ctx.get_cache();
    if (auto r = cache.get_specialized_subsingleton_info_nargs(ctx.mode(), g, num_rest_args))
        return *r;
    buffer<ss_param_info> ssinfos;
    get_ss_core(ctx, fn, ssinfos, prefix_sz);
    for (unsigned i = 0; i < prefix_sz; i++) {
        ssinfos[i].set_specialized();
    }
    get_ss_core(ctx, g, ssinfos, num_rest_args);
    ss_param_infos r = to_list(ssinfos);
    cache.set_specialization_subsingleton_info_nargs(ctx.mode(), g, num_rest_args, r);
    trace_if_unsupported(ctx, fn, args, prefix_sz, r);
    return r;
}
}
