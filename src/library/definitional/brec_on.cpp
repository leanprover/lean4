/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/inductive/inductive.h"
#include "library/protected.h"
#include "library/reducible.h"
#include "library/module.h"
#include "library/bin_app.h"
#include "library/definitional/util.h"

namespace lean {
static void throw_corrupted(name const & n) {
    throw exception(sstream() << "error in 'brec_on' generation, '" << n << "' inductive datatype declaration is corrupted");
}

static bool is_typeformer_app(buffer<name> const & typeformer_names, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (!is_local(fn))
        return false;
    for (name const & n : typeformer_names) {
        if (mlocal_name(fn) == n)
            return true;
    }
    return false;
}

static environment mk_below(environment const & env, name const & n, bool ibelow) {
    if (!is_recursive_datatype(env, n))
        return env;
    if (is_inductive_predicate(env, n))
        return env;
    inductive::inductive_decls decls = *inductive::is_inductive_decl(env, n);
    type_checker tc(env);
    name_generator ngen;
    unsigned nparams       = std::get<1>(decls);
    declaration ind_decl   = env.get(n);
    declaration rec_decl   = env.get(inductive::get_elim_name(n));
    unsigned nindices      = *inductive::get_num_indices(env, n);
    unsigned nminors       = *inductive::get_num_minor_premises(env, n);
    unsigned ntypeformers  = length(std::get<2>(decls));
    level_param_names lps  = rec_decl.get_univ_params();
    level  lvl             = mk_param_univ(head(lps)); // universe we are eliminating too
    levels lvls            = param_names_to_levels(tail(lps));
    levels blvls;
    level  rlvl;
    name prod_name;
    expr unit, outer_prod;
    // The arguments of below (ibelow) are the ones in the recursor - minor premises.
    // The universe we map to is also different (l+1 for below) and (0 fo ibelow).
    expr ref_type;
    if (ibelow) {
        // we are eliminating to Prop
        blvls      = lvls;
        rlvl       = mk_level_zero();
        unit       = mk_constant("true");
        prod_name  = name("and");
        outer_prod = mk_constant(prod_name);
        ref_type   = instantiate_univ_param(rec_decl.get_type(), param_id(lvl), mk_level_zero());
    } else {
        blvls = cons(lvl, lvls);
        rlvl  = get_datatype_level(ind_decl.get_type());
        // if rlvl is of the form (max 1 l), then rlvl <- l
        if (is_max(rlvl) && is_one(max_lhs(rlvl)))
            rlvl = max_rhs(rlvl);
        rlvl       = mk_max(mk_succ(lvl), rlvl);
        unit       = mk_constant("unit", rlvl);
        prod_name  = name("prod");
        outer_prod = mk_constant(prod_name, {rlvl, rlvl});
        ref_type   = instantiate_univ_param(rec_decl.get_type(), param_id(lvl), mk_succ(lvl));
    }
    expr Type_result       = mk_sort(rlvl);
    buffer<expr> ref_args;
    to_telescope(ngen, ref_type, ref_args);
    if (ref_args.size() != nparams + ntypeformers + nminors + nindices + 1)
        throw_corrupted(n);

    // args contains the below/ibelow arguments
    buffer<expr> args;
    buffer<name> typeformer_names;
    // add parameters and typeformers
    for (unsigned i = 0; i < nparams; i++)
        args.push_back(ref_args[i]);
    for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
        args.push_back(ref_args[i]);
        typeformer_names.push_back(mlocal_name(ref_args[i]));
    }
    // we ignore minor premises in below/ibelow
    for (unsigned i = nparams + ntypeformers + nminors; i < ref_args.size(); i++)
        args.push_back(ref_args[i]);

    // We define below/ibelow using the recursor for this type
    levels rec_lvls       = cons(mk_succ(rlvl), lvls);
    expr rec              = mk_constant(rec_decl.get_name(), rec_lvls);
    for (unsigned i = 0; i < nparams; i++)
        rec = mk_app(rec, args[i]);
    // add type formers
    for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
        buffer<expr> targs;
        to_telescope(ngen, mlocal_type(args[i]), targs);
        rec = mk_app(rec, Fun(targs, Type_result));
    }
    // add minor premises
    for (unsigned i = nparams + ntypeformers; i < nparams + ntypeformers + nminors; i++) {
        expr minor = ref_args[i];
        expr minor_type = mlocal_type(minor);
        buffer<expr> minor_args;
        minor_type = to_telescope(ngen, minor_type, minor_args);
        buffer<expr> prod_pairs;
        for (expr & minor_arg : minor_args) {
            buffer<expr> minor_arg_args;
            expr minor_arg_type = to_telescope(tc, mlocal_type(minor_arg), minor_arg_args);
            if (is_typeformer_app(typeformer_names, minor_arg_type)) {
                expr r = minor_arg;
                expr fst = mlocal_type(minor_arg);
                expr snd = Pi(minor_arg_args, mk_app(r, minor_arg_args));
                expr inner_prod;
                if (ibelow) {
                    inner_prod = outer_prod; // and
                } else {
                    level fst_lvl   = sort_level(tc.ensure_type(fst).first);
                    inner_prod = mk_constant(prod_name, {fst_lvl, rlvl});
                }
                prod_pairs.push_back(mk_app(inner_prod, fst, snd));
                minor_arg = update_mlocal(minor_arg, Pi(minor_arg_args, Type_result));
            }
        }
        expr new_arg = mk_bin_rop(outer_prod, unit, prod_pairs.size(), prod_pairs.data());
        rec = mk_app(rec, Fun(minor_args, new_arg));
    }

    // add indices and major premise
    for (unsigned i = nparams + ntypeformers; i < args.size(); i++) {
        rec = mk_app(rec, args[i]);
    }

    name below_name  = ibelow ? name{n, "ibelow"} : name{n, "below"};
    expr below_type  = Pi(args, Type_result);
    expr below_value = Fun(args, rec);

    bool opaque       = false;
    bool use_conv_opt = true;
    declaration new_d = mk_definition(env, below_name, rec_decl.get_univ_params(), below_type, below_value,
                                      opaque, rec_decl.get_module_idx(), use_conv_opt);
    environment new_env = module::add(env, check(env, new_d));
    new_env = set_reducible(new_env, below_name, reducible_status::On);
    return add_protected(new_env, below_name);
}

environment mk_below(environment const & env, name const & n) {
    return mk_below(env, n, false);
}

environment mk_ibelow(environment const & env, name const & n) {
    return mk_below(env, n, true);
}
}
