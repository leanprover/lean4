/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/inductive/inductive.h"
#include "library/util.h"

namespace lean {
static bool is_typeformer_app(buffer<name> const & typeformer_names, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (!is_local(fn))
        return false;
    unsigned r = 0;
    for (name const & n : typeformer_names) {
        if (mlocal_name(fn) == n)
            return true;
        r++;
    }
    return false;
}

void get_rec_args(environment const & env, name const & n, buffer<buffer<bool>> & r) {
    lean_assert(inductive::is_inductive_decl(env, n));
    type_checker tc(env);
    name_generator ngen;
    declaration ind_decl   = env.get(n);
    declaration rec_decl   = env.get(inductive::get_elim_name(n));
    unsigned nparams       = *inductive::get_num_params(env, n);
    unsigned nminors       = *inductive::get_num_minor_premises(env, n);
    unsigned ntypeformers  = *inductive::get_num_type_formers(env, n);
    buffer<expr> rec_args;
    to_telescope(ngen, rec_decl.get_type(), rec_args);
    buffer<name> typeformer_names;
    for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
        typeformer_names.push_back(mlocal_name(rec_args[i]));
    }
    lean_assert(typeformer_names.size() == ntypeformers);
    r.clear();
    // add minor premises
    for (unsigned i = nparams + ntypeformers; i < nparams + ntypeformers + nminors; i++) {
        r.push_back(buffer<bool>());
        buffer<bool> & bv = r.back();
        expr minor_type = mlocal_type(rec_args[i]);
        buffer<expr> minor_args;
        to_telescope(ngen, minor_type, minor_args);
        for (expr & minor_arg : minor_args) {
            buffer<expr> minor_arg_args;
            expr minor_arg_type = to_telescope(tc, mlocal_type(minor_arg), minor_arg_args);
            bv.push_back(is_typeformer_app(typeformer_names, minor_arg_type));
        }
    }
}
}
