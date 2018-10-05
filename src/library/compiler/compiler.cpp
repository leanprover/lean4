/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "kernel/type_checker.h"
#include "library/noncomputable.h" // TODO(Leo): remove
#include "library/max_sharing.h"
#include "library/compiler/util.h"
#include "library/compiler/lcnf.h"
#include "library/compiler/cse.h"
#include "library/compiler/csimp.h"
#include "library/compiler/elim_dead_let.h"
#include "library/compiler/erase_irrelevant.h"

namespace lean {
static name * g_codegen = nullptr;

bool is_codegen_enabled(options const & opts) {
    return opts.get_bool(*g_codegen, true);
}

static cdecls to_cdecls(environment const & env, names const & cs) {
    return map2<cdecl>(cs, [&](name const & n) { return cdecl(n, env.get(n).get_value()); });
}

static expr eta_expand(environment const & env, expr const & e) {
    return type_checker(env).eta_expand(e);
}

template<typename F>
cdecls apply(F && f, environment const & env, cdecls const & ds) {
    return map(ds, [&](cdecl const & d) { return cdecl(d.fst(), f(env, d.snd())); });
}

template<typename F>
cdecls apply(F && f, cdecls const & ds) {
    return map(ds, [&](cdecl const & d) { return cdecl(d.fst(), f(d.snd())); });
}

environment compile(environment const & env, options const & opts, names const & cs) {
    if (!is_codegen_enabled(opts))
        return env;

    for (name const & c : cs) {
        if (!env.get(c).is_definition() || is_noncomputable(env, c))
            return env;
    }

    cdecls ds = to_cdecls(env, cs);
    auto simp = [&](environment const & env, expr const & e) { return csimp(env, e, csimp_cfg(opts)); };

    ds = apply(eta_expand, env, ds);
    ds = apply(to_lcnf, env, ds);
    ds = apply(cce, env, ds);
    ds = apply(simp, env, ds);
    ds = apply(elim_dead_let, ds);
    ds = apply(cse, env, ds);
    ds = apply(max_sharing, ds);
    ds = apply(erase_irrelevant, env, ds);

    // TODO(Leo)
    return env;
}

void initialize_compiler() {
    g_codegen = new name("codegen");
    register_bool_option(*g_codegen, true, "(compiler) enable/disable code generation");
}

void finalize_compiler() {
    delete g_codegen;
}
}
