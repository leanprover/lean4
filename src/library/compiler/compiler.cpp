/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "kernel/type_checker.h"
#include "library/max_sharing.h"
#include "library/trace.h"
#include "library/sorry.h"
#include "library/compiler/util.h"
#include "library/compiler/lcnf.h"
#include "library/compiler/cse.h"
#include "library/compiler/csimp.h"
#include "library/compiler/elim_dead_let.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/specialize.h"
#include "library/compiler/lambda_lifting.h"
#include "library/compiler/extract_closed.h"
#include "library/compiler/reduce_arity.h"
#include "library/compiler/ll_infer_type.h"
#include "library/compiler/simp_app_args.h"
#include "library/compiler/llnf.h"
#include "library/compiler/emit_bytecode.h"
#include "library/compiler/llnf_code.h"
#include "library/compiler/export_attribute.h"
#include "library/compiler/extern_attribute.h"

namespace lean {
static name * g_codegen = nullptr;

bool is_codegen_enabled(options const & opts) {
    return opts.get_bool(*g_codegen, true);
}

static name get_real_name(name const & n) {
    if (optional<name> new_n = is_unsafe_rec_name(n))
        return *new_n;
    else
        return n;
}

static comp_decls to_comp_decls(environment const & env, names const & cs) {
    return map2<comp_decl>(cs, [&](name const & n) {
            return comp_decl(get_real_name(n), env.get(n).get_value());
        });
}

static expr eta_expand(environment const & env, expr const & e) {
    return type_checker(env).eta_expand(e);
}

template<typename F>
comp_decls apply(F && f, environment const & env, comp_decls const & ds) {
    return map(ds, [&](comp_decl const & d) { return comp_decl(d.fst(), f(env, d.snd())); });
}

template<typename F>
comp_decls apply(F && f, comp_decls const & ds) {
    return map(ds, [&](comp_decl const & d) { return comp_decl(d.fst(), f(d.snd())); });
}

static void trace(comp_decls const & ds) {
    for (comp_decl const & d : ds) {
        tout() << ">> " << d.fst() << "\n" << d.snd() << "\n";
    }
}

static environment cache_stage1(environment env, comp_decls const & ds) {
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

static environment cache_stage2(environment env, comp_decls const & ds) {
    buffer<expr> ts;
    ll_infer_type(env, ds, ts);
    lean_assert(ts.size() == length(ds));
    unsigned i = 0;
    for (comp_decl const & d : ds) {
        name n = d.fst();
        expr v = d.snd();
        expr t = ts[i];
        unsigned arity = get_num_nested_lambdas(v);
        t = ensure_arity(t, arity);
        lean_trace(name({"compiler", "stage2"}), tout() << n << " : " << t << "\n";);
        lean_trace(name({"compiler", "ll_infer_type"}), tout() << n << " : " << t << "\n";);
        env = register_stage2_decl(env, n, t, v);
        i++;
    }
    return env;
}

#define trace_compiler(k, ds) lean_trace(k, trace(ds);)

bool is_main_fn(environment const & env, name const & n) {
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

/* Return true iff type is `list string -> io uint32` or `io uint32` */
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

environment compile(environment const & env, options const & opts, names cs) {
    if (!is_codegen_enabled(opts))
        return env;

    /* Do not generate code for irrelevant decls */
    cs = filter(cs, [&](name const & c) { return !is_irrelevant_type(env, env.get(c).get_type());});
    if (empty(cs)) return env;

    for (name const & c : cs) {
        if (is_main_fn(env, c) && !is_main_fn_type(env.get(c).get_type())) {
            throw exception("invalid `main` function, it must have type `list string -> io uint32`");
        }
    }

    if (length(cs) == 1 && is_extern_constant(env, head(cs))) {
        /* Generate boxed version for extern/native constant if needed. */
        unsigned arity = *get_extern_constant_arity(env, head(cs));
        if (optional<pair<environment, comp_decl>> p = mk_boxed_version(env, head(cs), arity)) {
            /* Remark: we don't need boxed version for the bytecode. */
            return save_llnf_code(p->first, comp_decls(p->second));
        } else {
            /* We always generate boxed versions for extern. */
            lean_unreachable();
        }
    }

    for (name const & c : cs) {
        lean_assert(!is_extern_constant(env, c));
        if ((!env.get(c).is_definition() && !env.get(c).is_opaque()) || has_synthetic_sorry(env.get(c).get_value())) {
            return env;
        }
    }

    comp_decls ds = to_comp_decls(env, cs);
    csimp_cfg cfg(opts);
    auto simp  = [&](environment const & env, expr const & e) { return csimp(env, e, cfg); };
    auto esimp = [&](environment const & env, expr const & e) { return cesimp(env, e, cfg); };
    trace_compiler(name({"compiler", "input"}), ds);
    ds = apply(eta_expand, env, ds);
    trace_compiler(name({"compiler", "eta_expand"}), ds);
    ds = apply(to_lcnf, env, ds);
    trace_compiler(name({"compiler", "lcnf"}), ds);
    ds = apply(cce, env, ds);
    trace_compiler(name({"compiler", "cce"}), ds);
    ds = apply(simp, env, ds);
    trace_compiler(name({"compiler", "simp"}), ds);
    ds = apply(elim_dead_let, ds);
    trace_compiler(name({"compiler", "elim_dead_let"}), ds);
    ds = apply(cse, env, ds);
    trace_compiler(name({"compiler", "cse"}), ds);
    ds = apply(max_sharing, ds);
    trace_compiler(name({"compiler", "stage1"}), ds);
    environment new_env = cache_stage1(env, ds);
    std::tie(new_env, ds) = specialize(new_env, ds, cfg);
    trace_compiler(name({"compiler", "specialize"}), ds);
    ds = apply(elim_dead_let, ds);
    trace_compiler(name({"compiler", "elim_dead_let"}), ds);
    ds = apply(erase_irrelevant, new_env, ds);
    trace_compiler(name({"compiler", "erase_irrelevant"}), ds);
    ds = apply(esimp, new_env, ds);
    trace_compiler(name({"compiler", "simp"}), ds);
    ds = apply(elim_dead_let, ds);
    trace_compiler(name({"compiler", "elim_dead_let"}), ds);
    ds = apply(ecse, new_env, ds);
    trace_compiler(name({"compiler", "cse"}), ds);
    ds = reduce_arity(new_env, ds);
    trace_compiler(name({"compiler", "reduce_arity"}), ds);
    std::tie(new_env, ds) = lambda_lifting(new_env, ds);
    trace_compiler(name({"compiler", "lambda_lifting"}), ds);
    ds = apply(esimp, new_env, ds);
    trace_compiler(name({"compiler", "simp"}), ds);
    std::tie(new_env, ds) = extract_closed(new_env, ds);
    ds = apply(elim_dead_let, ds);
    trace_compiler(name({"compiler", "extract_closed"}), ds);
    new_env = cache_stage2(new_env, ds);
    trace_compiler(name({"compiler", "stage2"}), ds);
    ds = apply(esimp, new_env, ds);
    trace_compiler(name({"compiler", "simp"}), ds);
    ds = apply(simp_app_args, new_env, ds);
    ds = apply(ecse, new_env, ds);
    ds = apply(elim_dead_let, ds);
    trace_compiler(name({"compiler", "simp_app_args"}), ds);
    /* emit C++ code. */
    comp_decls b_ds;
    std::tie(new_env, b_ds) = to_llnf(new_env, ds, true);
    new_env = save_llnf_code(new_env, b_ds);
    trace_compiler(name({"compiler", "boxed"}), b_ds);
    /* emit bytecode. Remark: the current emit_bytecode has no support for unboxed data. */
    std::tie(new_env, ds) = to_llnf(new_env, ds, false);
    trace_compiler(name({"compiler", "llnf"}), ds);
    return emit_bytecode(new_env, ds);
}

void initialize_compiler() {
    g_codegen = new name("codegen");
    register_bool_option(*g_codegen, true, "(compiler) enable/disable code generation");

    register_trace_class("compiler");
    register_trace_class({"compiler", "input"});
    register_trace_class({"compiler", "eta_expand"});
    register_trace_class({"compiler", "lcnf"});
    register_trace_class({"compiler", "cce"});
    register_trace_class({"compiler", "simp"});
    register_trace_class({"compiler", "simp_detail"});
    register_trace_class({"compiler", "elim_dead_let"});
    register_trace_class({"compiler", "cse"});
    register_trace_class({"compiler", "specialize"});
    register_trace_class({"compiler", "stage1"});
    register_trace_class({"compiler", "stage2"});
    register_trace_class({"compiler", "erase_irrelevant"});
    register_trace_class({"compiler", "lambda_lifting"});
    register_trace_class({"compiler", "extract_closed"});
    register_trace_class({"compiler", "reduce_arity"});
    register_trace_class({"compiler", "simp_app_args"});
    register_trace_class({"compiler", "llnf"});
    register_trace_class({"compiler", "boxed"});
    register_trace_class({"compiler", "optimize_bytecode"});
    register_trace_class({"compiler", "code_gen"});
    register_trace_class({"compiler", "ll_infer_type"});
}

void finalize_compiler() {
    delete g_codegen;
}
}
