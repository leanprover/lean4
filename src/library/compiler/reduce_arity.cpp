/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/compiler/util.h"

namespace lean {
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
    for (expr & fvar : fvars) {
        if (has_fvar(code, fvar)) {
            new_fvars.push_back(fvar);
        }
    }
    if (fvars.size() == new_fvars.size()) {
        /* Do nothing, all arguments are used. */
        return comp_decls(cdecl);
    }
    name red_fn   = name(cdecl.fst(), "_rarg");
    expr red_code = lctx.mk_lambda(new_fvars, code);
    comp_decl red_decl(red_fn, red_code);
    /* Replace `cdecl` code with a call to `red_fn`.
       We rely on inlining to reduce calls to `cdecl` into calls to `red_decl`. */
    expr new_code = mk_app(mk_constant(red_fn), new_fvars);
    new_code      = lctx.mk_lambda(fvars, new_code);
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
