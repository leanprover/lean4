/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/option_declarations.h"
#include "util/io.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "kernel/trace.h"
#include "library/max_sharing.h"
#include "library/time_task.h"
#include "library/compiler/util.h"
#include "library/compiler/lcnf.h"
#include "library/compiler/find_jp.h"
#include "library/compiler/cse.h"
#include "library/compiler/csimp.h"
#include "library/compiler/elim_dead_let.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/specialize.h"
#include "library/compiler/eager_lambda_lifting.h"
#include "library/compiler/implemented_by_attribute.h"
#include "library/compiler/lambda_lifting.h"
#include "library/compiler/extract_closed.h"
#include "library/compiler/reduce_arity.h"
#include "library/compiler/ll_infer_type.h"
#include "library/compiler/simp_app_args.h"
#include "library/compiler/llnf.h"
#include "library/compiler/export_attribute.h"
#include "library/compiler/extern_attribute.h"
#include "library/compiler/struct_cases_on.h"
#include "library/compiler/ir.h"

namespace lean {
static name * g_extract_closed = nullptr;

bool is_extract_closed_enabled(options const & opts) { return opts.get_bool(*g_extract_closed, true); }

static name get_real_name(name const & n) {
    if (optional<name> new_n = is_unsafe_rec_name(n))
        return *new_n;
    else
        return n;
}

static comp_decls to_comp_decls(elab_environment const & env, names const & cs) {
    bool allow_opaque = true;
    return map2<comp_decl>(cs, [&](name const & n) {
            return comp_decl(get_real_name(n), env.get(n).get_value(allow_opaque));
        });
}

static expr eta_expand(elab_environment const & env, expr const & e) {
    return type_checker(env.to_kernel_env()).eta_expand(e);
}

template<typename F>
comp_decls apply(F && f, elab_environment const & env, comp_decls const & ds) {
    return map(ds, [&](comp_decl const & d) { return comp_decl(d.fst(), f(env, d.snd())); });
}

template<typename F>
comp_decls apply(F && f, comp_decls const & ds) {
    return map(ds, [&](comp_decl const & d) { return comp_decl(d.fst(), f(d.snd())); });
}

void trace_comp_decl(comp_decl const & d) {
    tout() << ">> " << d.fst() << "\n" << trace_pp_expr(d.snd()) << "\n";
}

void trace_comp_decls(comp_decls const & ds) {
    for (comp_decl const & d : ds) {
        trace_comp_decl(d);
    }
}

static elab_environment cache_stage1(elab_environment env, comp_decls const & ds) {
    for (comp_decl const & d : ds) {
        name n = d.fst();
        expr v = d.snd();
        constant_info info = env.get(n);
        env = register_stage1_decl(env, n, info.get_lparams(), info.get_type(), v);
    }
    return env;
}

static expr ensure_arity(expr const & t, unsigned arity) {
    if (arity == 0) {
        if (is_pi(t)) return mk_enf_object_type(); // closure
        else return t;
    }
    lean_assert(is_pi(t));
    return update_binding(t, binding_domain(t), ensure_arity(binding_body(t), arity-1));
}

static elab_environment cache_stage2(elab_environment env, comp_decls const & ds, bool only_new_ones = false) {
    buffer<expr> ts;
    ll_infer_type(env, ds, ts);
    lean_assert(ts.size() == length(ds));
    unsigned i = 0;
    for (comp_decl const & d : ds) {
        name n = d.fst();
        expr v = d.snd();
        if (!only_new_ones || !is_stage2_decl(env, n)) {
            expr t = ts[i];
            unsigned arity = get_num_nested_lambdas(v);
            t = ensure_arity(t, arity);
            lean_trace(name({"compiler", "stage2"}), tout() << n << " : " << t << "\n";);
            lean_trace(name({"compiler", "ll_infer_type"}), tout() << n << " : " << t << "\n";);
            env = register_stage2_decl(env, n, t, v);
        }
        i++;
    }
    return env;
}

/* Cache the declarations in `ds` that have not already been cached. */
static elab_environment cache_new_stage2(elab_environment env, comp_decls const & ds) {
    return cache_stage2(env, ds, true);
}

bool is_main_fn(elab_environment const & env, name const & n) {
    if (n == "main") return true;
    if (optional<name> c = get_export_name_for(env, n)) {
        return *c == "main";
    }
    return false;
}

bool is_uint32_or_unit(expr const & type) {
    return
        is_constant(type, get_uint32_name()) ||
        is_constant(type, get_unit_name()) ||
        is_constant(type, get_punit_name());
}

/* Return true iff type is `(List String ->) IO (UInt32 | (P)Unit)` */
bool is_main_fn_type(expr const & type) {
    if (is_arrow(type)) {
        expr d = binding_domain(type);
        expr r = binding_body(type);
        return
            is_app(r) &&
            is_constant(app_fn(r), get_io_name()) &&
            is_uint32_or_unit(app_arg(r)) &&
            is_app(d) &&
            is_constant(app_fn(d), get_list_name()) &&
            is_constant(app_arg(d), get_string_name());
    } else if (is_app(type)) {
        return
            is_constant(app_fn(type), get_io_name()) &&
            is_uint32_or_unit(app_arg(type));
    } else {
        return false;
    }
}

#define trace_compiler(k, ds) lean_trace(k, trace_comp_decls(ds););

extern "C" object* lean_csimp_replace_constants(object* env, object* n);

expr csimp_replace_constants(elab_environment const & env, expr const & e) {
    return expr(lean_csimp_replace_constants(env.to_obj_arg(), e.to_obj_arg()));
}

bool is_matcher(elab_environment const & env, comp_decls const & ds) {
    return length(ds) == 1 && is_matcher(env, head(ds).fst());
}

elab_environment compile(elab_environment const & env, options const & opts, names cs) {
    /* Do not generate code for irrelevant decls */
    cs = filter(cs, [&](name const & c) { return !is_irrelevant_type(env, env.get(c).get_type());});
    if (empty(cs)) return env;

    for (name const & c : cs) {
        if (is_main_fn(env, c) && !is_main_fn_type(env.get(c).get_type())) {
            throw exception("invalid `main` function, it must have type `List String -> IO UInt32`");
        }
    }

    if (length(cs) == 1) {
        name c = get_real_name(head(cs));
        if (has_implemented_by_attribute(env, c))
            return env;
        if (is_extern_or_init_constant(env, c)) {
            /* Generate boxed version for extern/native constant if needed. */
            return ir::add_extern(env, c);
        }
    }

    for (name const & c : cs) {
        lean_assert(!is_extern_constant(env, get_real_name(c)));
        constant_info cinfo = env.get(c);
        if (!cinfo.is_definition() && !cinfo.is_opaque()) return env;
    }

    time_task t("compilation", opts, head(cs));
    scope_trace_env scope_trace(env, opts);

    comp_decls ds = to_comp_decls(env, cs);
    csimp_cfg cfg(opts);
    // Use the following line to see compiler intermediate steps
    // scope_traces_as_string trace_scope;
    auto simp  = [&](elab_environment const & env, expr const & e) { return csimp(env, e, cfg); };
    auto esimp = [&](elab_environment const & env, expr const & e) { return cesimp(env, e, cfg); };
    trace_compiler(name({"compiler", "input"}), ds);
    ds = apply(eta_expand, env, ds);
    trace_compiler(name({"compiler", "eta_expand"}), ds);
    ds = apply(to_lcnf, env, ds);
    ds = apply(find_jp, env, ds);
    // trace(ds);
    trace_compiler(name({"compiler", "lcnf"}), ds);
    // trace(ds);
    ds = apply(cce, env, ds);
    trace_compiler(name({"compiler", "cce"}), ds);
    ds = apply(csimp_replace_constants, env, ds);
    ds = apply(simp, env, ds);
    trace_compiler(name({"compiler", "simp"}), ds);
    // trace(ds);
    elab_environment new_env = env;
    std::tie(new_env, ds) = eager_lambda_lifting(new_env, ds, cfg);
    trace_compiler(name({"compiler", "eager_lambda_lifting"}), ds);
    ds = apply(max_sharing, ds);
    trace_compiler(name({"compiler", "stage1"}), ds);
    new_env = cache_stage1(new_env, ds);
    if (is_matcher(new_env, ds)) {
        /* Auxiliary matcher applications are marked as inlined, and are always fully applied
           (if users don't use them manually). So, we skip code generation for them.
           By caching stage1, we make sure we have all information we need to inline them.

           TODO: we should have a "[strong_inline]" annotation that will inline a definition even
           when it is partially applied. Then, we can mark all `match` auxiliary functions as `[strong_inline]` */
        return new_env;
    }
    std::tie(new_env, ds) = specialize(new_env, ds, cfg);
    // The following check is incorrect. It was exposed by issue #1812.
    // We will not fix the check since we will delete the compiler.
    // lean_assert(lcnf_check_let_decls(new_env, ds));
    trace_compiler(name({"compiler", "specialize"}), ds);
    ds = apply(elim_dead_let, ds);
    trace_compiler(name({"compiler", "elim_dead_let"}), ds);
    ds = apply(erase_irrelevant, new_env, ds);
    trace_compiler(name({"compiler", "erase_irrelevant"}), ds);
    ds = apply(struct_cases_on, new_env, ds);
    trace_compiler(name({"compiler", "struct_cases_on"}), ds);
    ds = apply(esimp, new_env, ds);
    trace_compiler(name({"compiler", "simp"}), ds);
    ds = reduce_arity(new_env, ds);
    trace_compiler(name({"compiler", "reduce_arity"}), ds);
    std::tie(new_env, ds) = lambda_lifting(new_env, ds);
    trace_compiler(name({"compiler", "lambda_lifting"}), ds);
    // trace(ds);
    ds = apply(esimp, new_env, ds);
    trace_compiler(name({"compiler", "simp"}), ds);
    new_env = cache_stage2(new_env, ds);
    trace_compiler(name({"compiler", "stage2"}), ds);
    if (is_extract_closed_enabled(opts)) {
        std::tie(new_env, ds) = extract_closed(new_env, ds);
        ds = apply(elim_dead_let, ds);
        ds = apply(esimp, new_env, ds);
        trace_compiler(name({"compiler", "extract_closed"}), ds);
    }
    new_env = cache_new_stage2(new_env, ds);
    ds = apply(esimp, new_env, ds);
    trace_compiler(name({"compiler", "simp"}), ds);
    ds = apply(simp_app_args, new_env, ds);
    ds = apply(ecse, new_env, ds);
    ds = apply(elim_dead_let, ds);
    trace_compiler(name({"compiler", "simp_app_args"}), ds);
    // std::cout << trace_scope.get_string() << "\n";
    /* compile IR. */
    return compile_ir(new_env, opts, ds);
}

extern "C" LEAN_EXPORT object * lean_compile_decls(object * env, object * opts, object * decls) {
    return catch_kernel_exceptions<elab_environment>([&]() {
            return compile(elab_environment(env), options(opts, true), names(decls, true));
        });
}

void initialize_compiler() {
    g_extract_closed = new name{"compiler", "extract_closed"};
    mark_persistent(g_extract_closed->raw());
    register_bool_option(*g_extract_closed, true, "(compiler) enable/disable closed term caching");
    register_trace_class("compiler");
    register_trace_class({"compiler", "input"});
    register_trace_class({"compiler", "inline"});
    register_trace_class({"compiler", "eta_expand"});
    register_trace_class({"compiler", "lcnf"});
    register_trace_class({"compiler", "cce"});
    register_trace_class({"compiler", "simp"});
    register_trace_class({"compiler", "simp_detail"});
    register_trace_class({"compiler", "simp_float_cases"});
    register_trace_class({"compiler", "elim_dead_let"});
    register_trace_class({"compiler", "cse"});
    register_trace_class({"compiler", "specialize"});
    register_trace_class({"compiler", "stage1"});
    register_trace_class({"compiler", "stage2"});
    register_trace_class({"compiler", "erase_irrelevant"});
    register_trace_class({"compiler", "eager_lambda_lifting"});
    register_trace_class({"compiler", "lambda_lifting"});
    register_trace_class({"compiler", "extract_closed"});
    register_trace_class({"compiler", "reduce_arity"});
    register_trace_class({"compiler", "simp_app_args"});
    register_trace_class({"compiler", "struct_cases_on"});
    register_trace_class({"compiler", "llnf"});
    register_trace_class({"compiler", "result"});
    register_trace_class({"compiler", "optimize_bytecode"});
    register_trace_class({"compiler", "code_gen"});
    register_trace_class({"compiler", "ll_infer_type"});
    register_trace_class({"compiler", "ir"});
    register_trace_class({"compiler", "ir", "init"});
    register_trace_class({"compiler", "ir", "push_proj"});
    register_trace_class({"compiler", "ir", "reset_reuse"});
    register_trace_class({"compiler", "ir", "elim_dead_branches"});
    register_trace_class({"compiler", "ir", "elim_dead"});
    register_trace_class({"compiler", "ir", "simp_case"});
    register_trace_class({"compiler", "ir", "borrow"});
    register_trace_class({"compiler", "ir", "boxing"});
    register_trace_class({"compiler", "ir", "rc"});
    register_trace_class({"compiler", "ir", "expand_reset_reuse"});
    register_trace_class({"compiler", "ir", "result"});
}

void finalize_compiler() {
    delete g_extract_closed;
}
}
