/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/option_declarations.h"
#include "util/io.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "library/max_sharing.h"
#include "library/trace.h"
#include "library/sorry.h"
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
static name * g_codegen = nullptr;
static name * g_extract_closed = nullptr;

/*
@[export lean_mk_metavar_ctx]
def mkMetavarContext : Unit → MetavarContext := fun _ => {}
*/
extern "C" lean_object* lean_mk_metavar_ctx(lean_object*);

/*
@[export lean_pp_expr]
def ppExprLegacy (env : Environment) (mctx : MetavarContext) (lctx : LocalContext) (opts : Options) (e : Expr) : IO Format :=
*/
extern "C" object * lean_pp_expr(object * env, object * mctx, object * lctx, object * opts, object * e, object * w);

/*
@[export lean_format_pretty]
def pretty (f : Format) (w : Nat := defWidth) : String :=
*/
extern "C" object * lean_format_pretty(object * f, object * w);

std::string pp_expr(environment const & env, options const & opts, expr const & e) {
    local_ctx lctx;
    object_ref fmt = get_io_result<object_ref>(lean_pp_expr(env.to_obj_arg(), lean_mk_metavar_ctx(lean_box(0)), lctx.to_obj_arg(), opts.to_obj_arg(),
                                                            e.to_obj_arg(), io_mk_world()));
    string_ref str(lean_format_pretty(fmt.to_obj_arg(), lean_unsigned_to_nat(80)));
    return str.to_std_string();
}

bool is_codegen_enabled(options const & opts) { return opts.get_bool(*g_codegen, true); }
bool is_extract_closed_enabled(options const & opts) { return opts.get_bool(*g_extract_closed, true); }

static name get_real_name(name const & n) {
    if (optional<name> new_n = is_unsafe_rec_name(n))
        return *new_n;
    else
        return n;
}

static comp_decls to_comp_decls(environment const & env, names const & cs) {
    bool allow_opaque = true;
    return map2<comp_decl>(cs, [&](name const & n) {
            return comp_decl(get_real_name(n), env.get(n).get_value(allow_opaque));
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

static void trace(environment const & env, options const & opts, comp_decls const & ds) {
    for (comp_decl const & d : ds) {
        tout() << ">> " << d.fst() << "\n" << pp_expr(env, opts, d.snd()) << "\n";
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

static environment cache_stage2(environment env, comp_decls const & ds, bool only_new_ones = false) {
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
static environment cache_new_stage2(environment env, comp_decls const & ds) {
    return cache_stage2(env, ds, true);
}

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

/* Return true iff type is `List String -> IO UInt32` or `IO UInt32` */
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

static bool has_synthetic_sorry(constant_info const & cinfo) {
    return cinfo.is_definition() && has_synthetic_sorry(cinfo.get_value());
}

environment compile(environment const & env, options const & opts, names cs) {
#define trace_compiler(k, ds) lean_trace(k, trace(env, opts, ds);)

    if (!is_codegen_enabled(opts))
        return env;

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
        if (is_extern_constant(env, c)) {
            /* Generate boxed version for extern/native constant if needed. */
            return ir::add_extern(env, c);
        }
    }

    for (name const & c : cs) {
        lean_assert(!is_extern_constant(env, get_real_name(c)));
        constant_info cinfo = env.get(c);
        if (!cinfo.is_definition() && !cinfo.is_opaque()) return env;
        if (has_synthetic_sorry(cinfo)) return env;
    }

    time_task t("compilation",
                message_builder(environment(), get_global_ios(), "foo", pos_info(), message_severity::INFORMATION));
    abstract_type_context trace_ctx(opts);
    scope_trace_env scope_trace(env, opts, trace_ctx);

    comp_decls ds = to_comp_decls(env, cs);
    csimp_cfg cfg(opts);
    // Use the following line to see compiler intermediate steps
    // scope_traces_as_string trace_scope;
    auto simp  = [&](environment const & env, expr const & e) { return csimp(env, e, cfg); };
    auto esimp = [&](environment const & env, expr const & e) { return cesimp(env, e, cfg); };
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
    ds = apply(simp, env, ds);
    trace_compiler(name({"compiler", "simp"}), ds);
    // trace(ds);
    environment new_env = env;
    std::tie(new_env, ds) = eager_lambda_lifting(new_env, ds, cfg);
    trace_compiler(name({"compiler", "eager_lambda_lifting"}), ds);
    ds = apply(max_sharing, ds);
    trace_compiler(name({"compiler", "stage1"}), ds);
    new_env = cache_stage1(new_env, ds);
    std::tie(new_env, ds) = specialize(new_env, ds, cfg);
    lean_assert(lcnf_check_let_decls(new_env, ds));
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

extern "C" object* lean_get_decl_names_for_code_gen(object *);
names get_decl_names_for_code_gen(declaration const & decl) {
    return names(lean_get_decl_names_for_code_gen(decl.to_obj_arg()));
}

extern "C" object * lean_compile_decl(object * env, object * opts, object * decl) {
    return catch_kernel_exceptions<environment>([&]() {
            return compile(environment(env), options(opts, true), get_decl_names_for_code_gen(declaration(decl, true)));
        });
}

void initialize_compiler() {
    g_codegen        = new name("codegen");
    mark_persistent(g_codegen->raw());
    g_extract_closed = new name{"compiler", "extract_closed"};
    mark_persistent(g_extract_closed->raw());
    register_bool_option(*g_codegen, true, "(compiler) enable/disable code generation");
    register_bool_option(*g_extract_closed, true, "(compiler) enable/disable closed term caching");
    register_trace_class("compiler");
    register_trace_class({"compiler", "input"});
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
    delete g_codegen;
    delete g_extract_closed;
}
}
