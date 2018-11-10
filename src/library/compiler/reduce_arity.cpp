/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/compiler/util.h"

namespace lean {
#define REDUCE_ARITY_SUFFIX "_rarg"

bool arity_was_reduced(comp_decl const & cdecl) {
    expr v = cdecl.snd();
    while (is_lambda(v))
        v = binding_body(v);
    expr const & f = get_app_fn(v);
    if (!is_constant(f)) return false;
    name const & n = const_name(f);
    return n.is_string() && !n.is_atomic() && strcmp(n.get_string().data(), REDUCE_ARITY_SUFFIX) == 0;
}

comp_decls reduce_arity(comp_decl const & cdecl) {
    expr code    = cdecl.snd();
    buffer<expr> fvars;
    name_generator ngen;
    local_ctx lctx;
    while (is_lambda(code)) {
        lean_assert(!has_loose_bvars(code));
        expr fvar = lctx.mk_local_decl(ngen, binding_name(code), binding_domain(code));
        fvars.push_back(fvar);
        code = binding_body(code);
    }
    code = instantiate_rev(code, fvars.size(), fvars.data());
    buffer<expr> new_fvars;
#if 1
    /* For now, we remove just the prefix.
       Removing unused variables that occur in other parts of the declaration seem to create problems.
       Example: we may create more closures if the function is partially applied.
       By eliminating just a prefix, we get the most common case: a function that starts with a sequence of type variables.
       TODO(Leo): improve this. */
    bool found_used = false;
    for (expr & fvar : fvars) {
        if (found_used || has_fvar(code, fvar)) {
            found_used = true;
            new_fvars.push_back(fvar);
        }
    }
#else
    for (expr & fvar : fvars) {
        if (has_fvar(code, fvar)) {
            new_fvars.push_back(fvar);
        }
    }
#endif
    if (fvars.size() == new_fvars.size()) {
        /* Do nothing, all arguments are used. */
        return comp_decls(cdecl);
    }
    name red_fn   = name(cdecl.fst(), REDUCE_ARITY_SUFFIX);
    expr red_code = lctx.mk_lambda(new_fvars, code);
    comp_decl red_decl(red_fn, red_code);
    /* Replace `cdecl` code with a call to `red_fn`.
       We rely on inlining to reduce calls to `cdecl` into calls to `red_decl`. */
    expr new_code = mk_app(mk_constant(red_fn), new_fvars);
    new_code      = try_eta(lctx.mk_lambda(fvars, new_code));
    comp_decl new_decl(cdecl.fst(), new_code);
    return comp_decls(red_decl, comp_decls(new_decl));
}

comp_decls reduce_arity(comp_decls const & ds) {
    comp_decls r;
    for (comp_decl const & d : ds) {
        r = append(r, reduce_arity(d));
    }
    return r;
}
}
