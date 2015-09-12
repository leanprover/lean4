/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/find_fn.h"
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

bool is_recursive_rec_app(environment const & env, expr const & e) {
    buffer<expr> args;
    name_generator ngen;
    expr const & f = get_app_args(e, args);
    if (!is_constant(f))
        return false;
    auto I_name = inductive::is_elim_rule(env, const_name(f));
    if (!I_name || !is_recursive_datatype(env, *I_name) || is_inductive_predicate(env, *I_name))
        return false;
    unsigned nparams       = *inductive::get_num_params(env, *I_name);
    unsigned nminors       = *inductive::get_num_minor_premises(env, *I_name);
    unsigned ntypeformers  = *inductive::get_num_type_formers(env, *I_name);
    buffer<buffer<bool>> is_rec_arg;
    get_rec_args(env, *I_name, is_rec_arg);
    for (unsigned i = nparams + ntypeformers, j = 0; i < nparams + ntypeformers + nminors; i++, j++) {
        buffer<bool> const & minor_is_rec_arg = is_rec_arg[j];
        expr minor = args[i];
        buffer<expr> minor_ctx;
        expr minor_body = fun_to_telescope(ngen, minor, minor_ctx, optional<binder_info>());
        unsigned sz = std::min(minor_is_rec_arg.size(), minor_ctx.size());
        if (find(minor_body, [&](expr const & e, unsigned) {
                    if (!is_local(e))
                        return false;
                    for (unsigned k = 0; k < sz; k++) {
                        if (minor_is_rec_arg[k] && mlocal_name(e) == mlocal_name(minor_ctx[k]))
                            return true;
                    }
                    return false;
                }))
            return false;
    }
    return true;
}
}
