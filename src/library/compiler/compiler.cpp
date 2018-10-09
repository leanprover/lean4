/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "kernel/type_checker.h"
#include "library/noncomputable.h" // TODO(Leo): remove
#include "library/max_sharing.h"
#include "library/trace.h"
#include "library/module.h"
#include "library/compiler/util.h"
#include "library/compiler/lcnf.h"
#include "library/compiler/cse.h"
#include "library/compiler/csimp.h"
#include "library/compiler/elim_dead_let.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/lambda_lifting.h"
#include "library/compiler/simp_inductive.h"

namespace lean {
static name * g_codegen = nullptr;

bool is_codegen_enabled(options const & opts) {
    return opts.get_bool(*g_codegen, true);
}

static comp_decls to_comp_decls(environment const & env, names const & cs) {
    return map2<comp_decl>(cs, [&](name const & n) { return comp_decl(n, env.get(n).get_value()); });
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

static comp_decls lambda_lifting(environment const & env, comp_decls const & ds) {
    comp_decls r;
    for (comp_decl const & d : ds) {
        r = append(r, lambda_lifting(env, d));
    }
    return r;
}

static void trace(comp_decls const & ds) {
    for (comp_decl const & d : ds) {
        tout() << ">> " << d.fst() << "\n" << d.snd() << "\n";
    }
}

static environment cache_stage1(environment env, comp_decls const & ds) {
    type_checker tc(env);
    for (comp_decl const & d : ds) {
        name n = d.fst();
        expr v = d.snd();
        expr t = cheap_beta_reduce(tc.infer(v));
        declaration aux_decl = mk_definition(mk_cstage1_name(n), names(), t, v, reducibility_hints::mk_opaque(), true);
        env = module::add(env, aux_decl, false);
    }
    return env;
}

#define trace_compiler(k, ds) lean_trace(k, trace(ds);)

environment compile(environment const & env, options const & opts, names const & cs) {
    if (!is_codegen_enabled(opts))
        return env;

    for (name const & c : cs) {
        if (!env.get(c).is_definition() || is_noncomputable(env, c))
            return env;
    }

    comp_decls ds = to_comp_decls(env, cs);
    auto simp = [&](environment const & env, expr const & e) { return csimp(env, e, csimp_cfg(opts)); };

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
    ds = apply(erase_irrelevant, new_env, ds);
    trace_compiler(name({"compiler", "erase_irrelevant"}), ds);
    ds = apply(elim_dead_let, ds);
    trace_compiler(name({"compiler", "elim_dead_let"}), ds);
    ds = apply(cse, new_env, ds);
    trace_compiler(name({"compiler", "cse"}), ds);
    ds = lambda_lifting(new_env, ds);
    trace_compiler(name({"compiler", "lambda_lifting"}), ds);
    ds = apply(simp_inductive, new_env, ds);
    trace_compiler(name({"compiler", "simplify_inductive"}), ds);
    // TODO(Leo)
    return new_env;
}

void initialize_compiler() {
    g_codegen = new name("codegen");
    register_bool_option(*g_codegen, true, "(compiler) enable/disable code generation");
}

void finalize_compiler() {
    delete g_codegen;
}
}
