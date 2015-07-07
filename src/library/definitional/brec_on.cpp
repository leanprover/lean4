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
#include "library/util.h"
#include "library/normalize.h"

namespace lean {
static void throw_corrupted(name const & n) {
    throw exception(sstream() << "error in 'brec_on' generation, '" << n << "' inductive datatype declaration is corrupted");
}

static optional<unsigned> is_typeformer_app(buffer<name> const & typeformer_names, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (!is_local(fn))
        return optional<unsigned>();
    unsigned r = 0;
    for (name const & n : typeformer_names) {
        if (mlocal_name(fn) == n)
            return optional<unsigned>(r);
        r++;
    }
    return optional<unsigned>();
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
    bool is_reflexive      = is_reflexive_datatype(tc, n);
    level  lvl             = mk_param_univ(head(lps));
    levels lvls            = param_names_to_levels(tail(lps));
    level_param_names blvls; // universe level parameters of ibelow/below
    level  rlvl;  // universe level of the resultant type
    // The arguments of below (ibelow) are the ones in the recursor - minor premises.
    // The universe we map to is also different (l+1 for below of reflexive types) and (0 fo ibelow).
    expr ref_type;
    expr Type_result;
    if (ibelow) {
        // we are eliminating to Prop
        blvls      = tail(lps);
        rlvl       = mk_level_zero();
        ref_type   = instantiate_univ_param(rec_decl.get_type(), param_id(lvl), mk_level_zero());
    } else if (is_reflexive) {
        blvls = lps;
        rlvl  = get_datatype_level(ind_decl.get_type());
        // if rlvl is of the form (max 1 l), then rlvl <- l
        if (is_max(rlvl) && is_one(max_lhs(rlvl)))
            rlvl = max_rhs(rlvl);
        rlvl       = mk_max(mk_succ(lvl), rlvl);
        ref_type   = instantiate_univ_param(rec_decl.get_type(), param_id(lvl), mk_succ(lvl));
    } else {
        // we can simplify the universe levels for non-reflexive datatypes
        blvls       = lps;
        rlvl        = mk_max(mk_level_one(), lvl);
        ref_type    = rec_decl.get_type();
    }
    Type_result        = mk_sort(rlvl);
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
                expr fst  = mlocal_type(minor_arg);
                minor_arg = update_mlocal(minor_arg, Pi(minor_arg_args, Type_result));
                expr snd = Pi(minor_arg_args, mk_app(minor_arg, minor_arg_args));
                prod_pairs.push_back(mk_prod(tc, fst, snd, ibelow));
            }
        }
        expr new_arg = foldr([&](expr const & a, expr const & b) { return mk_prod(tc, a, b, ibelow); },
                             [&]() { return mk_unit(rlvl, ibelow); },
                             prod_pairs.size(), prod_pairs.data());
        rec = mk_app(rec, Fun(minor_args, new_arg));
    }

    // add indices and major premise
    for (unsigned i = nparams + ntypeformers; i < args.size(); i++) {
        rec = mk_app(rec, args[i]);
    }

    name below_name  = ibelow ? name{n, "ibelow"} : name{n, "below"};
    expr below_type  = Pi(args, Type_result);
    expr below_value = Fun(args, rec);

    bool use_conv_opt = true;
    declaration new_d = mk_definition(env, below_name, blvls, below_type, below_value,
                                      use_conv_opt);
    environment new_env = module::add(env, check(env, new_d));
    new_env = set_reducible(new_env, below_name, reducible_status::Reducible);
    if (!ibelow)
        new_env = add_unfold_hint(new_env, below_name, nparams + nindices + ntypeformers);
    return add_protected(new_env, below_name);
}

environment mk_below(environment const & env, name const & n) {
    return mk_below(env, n, false);
}

environment mk_ibelow(environment const & env, name const & n) {
    return mk_below(env, n, true);
}

static environment mk_brec_on(environment const & env, name const & n, bool ind) {
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
    // declaration below_decl = env.get(name(n, ind ? "ibelow" : "below"));
    unsigned nindices      = *inductive::get_num_indices(env, n);
    unsigned nminors       = *inductive::get_num_minor_premises(env, n);
    unsigned ntypeformers  = length(std::get<2>(decls));
    level_param_names lps  = rec_decl.get_univ_params();
    bool is_reflexive      = is_reflexive_datatype(tc, n);
    level  lvl             = mk_param_univ(head(lps));
    levels lvls            = param_names_to_levels(tail(lps));
    level rlvl;
    level_param_names blps;
    levels blvls; // universe level parameters of brec_on/binduction_on
    // The arguments of brec_on (binduction_on) are the ones in the recursor - minor premises.
    // The universe we map to is also different (l+1 for below of reflexive types) and (0 fo ibelow).
    expr ref_type;
    if (ind) {
        // we are eliminating to Prop
        blps       = tail(lps);
        blvls      = lvls;
        rlvl       = mk_level_zero();
        ref_type   = instantiate_univ_param(rec_decl.get_type(), param_id(lvl), mk_level_zero());
    } else if (is_reflexive) {
        blps    = lps;
        blvls   = cons(lvl, lvls);
        rlvl    = get_datatype_level(ind_decl.get_type());
        // if rlvl is of the form (max 1 l), then rlvl <- l
        if (is_max(rlvl) && is_one(max_lhs(rlvl)))
            rlvl = max_rhs(rlvl);
        rlvl       = mk_max(mk_succ(lvl), rlvl);
        // inner_prod, inner_prod_intro, pr1, pr2 do not use the same universe levels for
        // reflective datatypes.
        ref_type   = instantiate_univ_param(rec_decl.get_type(), param_id(lvl), mk_succ(lvl));
    } else {
        // we can simplify the universe levels for non-reflexive datatypes
        blps        = lps;
        blvls       = cons(lvl, lvls);
        rlvl        = mk_max(mk_level_one(), lvl);
        ref_type    = rec_decl.get_type();
    }
    buffer<expr> ref_args;
    to_telescope(ngen, ref_type, ref_args);
    if (ref_args.size() != nparams + ntypeformers + nminors + nindices + 1)
        throw_corrupted(n);

    // args contains the brec_on/binduction_on arguments
    buffer<expr> args;
    buffer<name> typeformer_names;
    // add parameters and typeformers
    for (unsigned i = 0; i < nparams; i++)
        args.push_back(ref_args[i]);
    for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
        args.push_back(ref_args[i]);
        typeformer_names.push_back(mlocal_name(ref_args[i]));
    }
    // add indices and major premise
    for (unsigned i = nparams + ntypeformers + nminors; i < ref_args.size(); i++)
        args.push_back(ref_args[i]);
    // create below terms (one per datatype)
    //    (below.{lvls} params type-formers)
    // Remark: it also creates the result type
    buffer<expr> belows;
    expr result_type;
    unsigned k = 0;
    for (auto const & decl : std::get<2>(decls)) {
        name const & n1 = inductive::inductive_decl_name(decl);
        if (n1 == n) {
            result_type = ref_args[nparams + k];
            for (unsigned i = nparams + ntypeformers + nminors; i < ref_args.size(); i++)
                result_type = mk_app(result_type, ref_args[i]);
        }
        k++;
        name bname = name(n1, ind ? "ibelow" : "below");
        expr below = mk_constant(bname, blvls);
        for (unsigned i = 0; i < nparams; i++)
            below = mk_app(below, ref_args[i]);
        for (unsigned i = nparams; i < nparams + ntypeformers; i++)
            below = mk_app(below, ref_args[i]);
        belows.push_back(below);
    }
    // create functionals (one for each type former)
    //     Pi idxs t, below idxs t -> C idxs t
    buffer<expr> Fs;
    name F_name("F");
    for (unsigned i = nparams, j = 0; i < nparams + ntypeformers; i++, j++) {
        expr const & C = ref_args[i];
        buffer<expr> F_args;
        to_telescope(ngen, mlocal_type(C), F_args);
        expr F_result = mk_app(C, F_args);
        expr F_below  = mk_app(belows[j], F_args);
        F_args.push_back(mk_local(ngen.next(), "f", F_below, binder_info()));
        expr F_type   = Pi(F_args, F_result);
        expr F        = mk_local(ngen.next(), F_name.append_after(j+1), F_type, binder_info());
        Fs.push_back(F);
        args.push_back(F);
    }

    // We define brec_on/binduction_on using the recursor for this type
    levels rec_lvls       = cons(rlvl, lvls);
    expr rec              = mk_constant(rec_decl.get_name(), rec_lvls);
    // add parameters to rec
    for (unsigned i = 0; i < nparams; i++)
        rec = mk_app(rec, ref_args[i]);
    // add type formers to rec
    //     Pi indices t, prod (C ... t) (below ... t)
    for (unsigned i = nparams, j = 0; i < nparams + ntypeformers; i++, j++) {
        expr const & C = ref_args[i];
        buffer<expr> C_args;
        to_telescope(ngen, mlocal_type(C), C_args);
        expr C_t     = mk_app(C, C_args);
        expr below_t = mk_app(belows[j], C_args);
        expr prod    = mk_prod(tc, C_t, below_t, ind);
        rec = mk_app(rec, Fun(C_args, prod));
    }
    // add minor premises to rec
    for (unsigned i = nparams + ntypeformers, j = 0; i < nparams + ntypeformers + nminors; i++, j++) {
        expr minor = ref_args[i];
        expr minor_type = mlocal_type(minor);
        buffer<expr> minor_args;
        minor_type = to_telescope(ngen, minor_type, minor_args);
        buffer<expr> pairs;
        for (expr & minor_arg : minor_args) {
            buffer<expr> minor_arg_args;
            expr minor_arg_type = to_telescope(tc, mlocal_type(minor_arg), minor_arg_args);
            if (auto k = is_typeformer_app(typeformer_names, minor_arg_type)) {
                buffer<expr> C_args;
                get_app_args(minor_arg_type, C_args);
                expr new_minor_arg_type = mk_prod(tc, minor_arg_type, mk_app(belows[*k], C_args), ind);
                minor_arg = update_mlocal(minor_arg, Pi(minor_arg_args, new_minor_arg_type));
                if (minor_arg_args.empty()) {
                    pairs.push_back(minor_arg);
                } else {
                    expr r = mk_app(minor_arg, minor_arg_args);
                    expr r_1 = Fun(minor_arg_args, mk_pr1(tc, r, ind));
                    expr r_2 = Fun(minor_arg_args, mk_pr2(tc, r, ind));
                    pairs.push_back(mk_pair(tc, r_1, r_2, ind));
                }
            }
        }
        expr b = foldr([&](expr const & a, expr const & b) { return mk_pair(tc, a, b, ind); },
                       [&]() { return mk_unit_mk(rlvl, ind); },
                       pairs.size(), pairs.data());
        unsigned F_idx = *is_typeformer_app(typeformer_names, minor_type);
        expr F = Fs[F_idx];
        buffer<expr> F_args;
        get_app_args(minor_type, F_args);
        F_args.push_back(b);
        expr new_arg = mk_pair(tc, mk_app(F, F_args), b, ind);
        rec = mk_app(rec, Fun(minor_args, new_arg));
    }
    // add indices and major to rec
    for (unsigned i = nparams + ntypeformers + nminors; i < ref_args.size(); i++)
        rec = mk_app(rec, ref_args[i]);


    name brec_on_name  = name(n, ind ? "binduction_on" : "brec_on");
    expr brec_on_type  = Pi(args, result_type);
    expr brec_on_value = Fun(args, mk_pr1(tc, rec, ind));

    bool use_conv_opt = true;
    declaration new_d = mk_definition(env, brec_on_name, blps, brec_on_type, brec_on_value,
                                      use_conv_opt);
    environment new_env = module::add(env, check(env, new_d));
    new_env = set_reducible(new_env, brec_on_name, reducible_status::Reducible);
    if (!ind)
        new_env = add_unfold_hint(new_env, brec_on_name, nparams + nindices + ntypeformers);
    return add_protected(new_env, brec_on_name);
}

environment mk_brec_on(environment const & env, name const & n) {
    return mk_brec_on(env, n, false);
}

environment mk_binduction_on(environment const & env, name const & n) {
    return mk_brec_on(env, n, true);
}
}
