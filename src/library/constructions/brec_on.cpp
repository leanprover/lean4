/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/sstream.h"
#include "kernel/kernel_exception.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/inductive.h"
#include "library/protected.h"
#include "library/reducible.h"
#include "library/bin_app.h"
#include "library/suffixes.h"
#include "library/util.h"
#include "library/aux_recursors.h"
#include "library/constructions/util.h"

namespace lean {
static optional<unsigned> is_typeformer_app(buffer<name> const & typeformer_names, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (!is_fvar(fn))
        return optional<unsigned>();
    unsigned r = 0;
    for (name const & n : typeformer_names) {
        if (fvar_name(fn) == n)
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
    local_ctx lctx;
    constant_info ind_info = env.get(n);
    inductive_val ind_val  = ind_info.to_inductive_val();
    name_generator ngen    = mk_constructions_name_generator();
    unsigned nparams       = ind_val.get_nparams();
    constant_info rec_info = env.get(mk_rec_name(n));
    recursor_val rec_val   = rec_info.to_recursor_val();
    unsigned nminors       = rec_val.get_nminors();
    unsigned ntypeformers  = rec_val.get_nmotives();
    names lps              = rec_info.get_lparams();
    bool is_reflexive      = ind_val.is_reflexive();
    level  lvl             = mk_univ_param(head(lps));
    levels lvls            = lparams_to_levels(tail(lps));
    names blvls;           // universe parameter names of ibelow/below
    level  rlvl;           // universe level of the resultant type
    // The arguments of below (ibelow) are the ones in the recursor - minor premises.
    // The universe we map to is also different (l+1 for below of reflexive types) and (0 fo ibelow).
    expr ref_type;
    expr Type_result;
    if (ibelow) {
        // we are eliminating to Prop
        blvls      = tail(lps);
        rlvl       = mk_level_zero();
        ref_type   = instantiate_lparam(rec_info.get_type(), param_id(lvl), mk_level_zero());
    } else if (is_reflexive) {
        blvls = lps;
        rlvl  = get_datatype_level(env, ind_info.get_type());
        // if rlvl is of the form (max 1 l), then rlvl <- l
        if (is_max(rlvl) && is_one(max_lhs(rlvl)))
            rlvl = max_rhs(rlvl);
        rlvl       = mk_max(mk_succ(lvl), rlvl);
        ref_type   = instantiate_lparam(rec_info.get_type(), param_id(lvl), mk_succ(lvl));
    } else {
        // we can simplify the universe levels for non-reflexive datatypes
        blvls       = lps;
        rlvl        = mk_max(mk_level_one(), lvl);
        ref_type    = rec_info.get_type();
    }
    Type_result        = mk_sort(rlvl);
    buffer<expr> ref_args;
    to_telescope(lctx, ngen, ref_type, ref_args);
    lean_assert(ref_args.size() == nparams + ntypeformers + nminors + ind_val.get_nindices() + 1);

    // args contains the below/ibelow arguments
    buffer<expr> args;
    buffer<name> typeformer_names;
    // add parameters and typeformers
    for (unsigned i = 0; i < nparams; i++)
        args.push_back(ref_args[i]);
    for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
        args.push_back(ref_args[i]);
        typeformer_names.push_back(fvar_name(ref_args[i]));
    }
    // we ignore minor premises in below/ibelow
    for (unsigned i = nparams + ntypeformers + nminors; i < ref_args.size(); i++)
        args.push_back(ref_args[i]);

    // We define below/ibelow using the recursor for this type
    levels rec_lvls       = cons(mk_succ(rlvl), lvls);
    expr rec              = mk_constant(rec_info.get_name(), rec_lvls);
    for (unsigned i = 0; i < nparams; i++)
        rec = mk_app(rec, args[i]);
    // add type formers
    for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
        buffer<expr> targs;
        to_telescope(lctx, ngen, lctx.get_type(args[i]), targs);
        rec = mk_app(rec, lctx.mk_lambda(targs, Type_result));
    }
    // add minor premises
    for (unsigned i = nparams + ntypeformers; i < nparams + ntypeformers + nminors; i++) {
        expr minor = ref_args[i];
        expr minor_type = lctx.get_type(minor);
        buffer<expr> minor_args;
        minor_type = to_telescope(lctx, ngen, minor_type, minor_args);
        buffer<expr> prod_pairs;
        for (expr & minor_arg : minor_args) {
            buffer<expr> minor_arg_args;
            expr minor_arg_type = to_telescope(env, lctx, ngen, lctx.get_type(minor_arg), minor_arg_args);
            if (is_typeformer_app(typeformer_names, minor_arg_type)) {
                expr fst  = lctx.get_type(minor_arg);
                minor_arg = lctx.mk_local_decl(ngen, lctx.get_local_decl(minor_arg).get_user_name(), lctx.mk_pi(minor_arg_args, Type_result));
                expr snd  = lctx.mk_pi(minor_arg_args, mk_app(minor_arg, minor_arg_args));
                type_checker tc(env, lctx);
                prod_pairs.push_back(mk_pprod(tc, fst, snd, ibelow));
            }
        }
        type_checker tc(env, lctx);
        expr new_arg = foldr([&](expr const & a, expr const & b) { return mk_pprod(tc, a, b, ibelow); },
                             [&]() { return mk_unit(rlvl, ibelow); },
                             prod_pairs.size(), prod_pairs.data());
        rec = mk_app(rec, lctx.mk_lambda(minor_args, new_arg));
    }

    // add indices and major premise
    for (unsigned i = nparams + ntypeformers; i < args.size(); i++) {
        rec = mk_app(rec, args[i]);
    }

    name below_name  = ibelow ? name{n, "ibelow"} : name{n, "below"};
    expr below_type  = lctx.mk_pi(args, Type_result);
    expr below_value = lctx.mk_lambda(args, rec);

    declaration new_d = mk_definition_inferring_unsafe(env, below_name, blvls, below_type, below_value,
                                                       reducibility_hints::mk_abbreviation());
    environment new_env = env.add(new_d);
    new_env = set_reducible(new_env, below_name, reducible_status::Reducible, true);
    new_env = completion_add_to_black_list(new_env, below_name);
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
    local_ctx lctx;
    constant_info ind_info = env.get(n);
    inductive_val ind_val  = ind_info.to_inductive_val();
    name_generator ngen    = mk_constructions_name_generator();
    unsigned nparams       = ind_val.get_nparams();
    constant_info rec_info = env.get(mk_rec_name(n));
    recursor_val rec_val   = rec_info.to_recursor_val();
    unsigned nminors       = rec_val.get_nminors();
    unsigned ntypeformers  = rec_val.get_nmotives();
    unsigned nmutual       = length(ind_val.get_all());
    if (ntypeformers != nmutual) {
        /* The mutual declaration containing `n` contains nested inductive datatypes.
           We don't support this kind of declaration here yet. We will probably never will :)
           To support it, we will need to generate an auxiliary `below` for each nested inductive
           type since their default `below` is not good here. For example, at
           ```
           inductive term
           | var : string -> term
           | app : string -> list term -> term
           ```
           The `list.below` is not useful since it will not allow us to recurse over the nested terms.
           We need to generate another one using the auxiliary recursor `term.rec_1` for `list term`.
        */
        return env;
    }
    names lps              = rec_info.get_lparams();
    bool is_reflexive      = ind_val.is_reflexive();
    level  lvl             = mk_univ_param(head(lps));
    levels lvls            = lparams_to_levels(tail(lps));
    level rlvl;
    names blps;
    levels blvls; // universe level parameters of brec_on/binduction_on
    // The arguments of brec_on (binduction_on) are the ones in the recursor - minor premises.
    // The universe we map to is also different (l+1 for below of reflexive types) and (0 fo ibelow).
    expr ref_type;
    if (ind) {
        // we are eliminating to Prop
        blps       = tail(lps);
        blvls      = lvls;
        rlvl       = mk_level_zero();
        ref_type   = instantiate_lparam(rec_info.get_type(), param_id(lvl), mk_level_zero());
    } else if (is_reflexive) {
        blps    = lps;
        blvls   = cons(lvl, lvls);
        rlvl    = get_datatype_level(env, ind_info.get_type());
        // if rlvl is of the form (max 1 l), then rlvl <- l
        if (is_max(rlvl) && is_one(max_lhs(rlvl)))
            rlvl = max_rhs(rlvl);
        rlvl       = mk_max(mk_succ(lvl), rlvl);
        // inner_prod, inner_prod_intro, pr1, pr2 do not use the same universe levels for
        // reflective datatypes.
        ref_type   = instantiate_lparam(rec_info.get_type(), param_id(lvl), mk_succ(lvl));
    } else {
        // we can simplify the universe levels for non-reflexive datatypes
        blps        = lps;
        blvls       = cons(lvl, lvls);
        rlvl        = mk_max(mk_level_one(), lvl);
        ref_type    = rec_info.get_type();
    }
    buffer<expr> ref_args;
    to_telescope(lctx, ngen, ref_type, ref_args);
    lean_assert(ref_args.size() == nparams + ntypeformers + nminors + ind_val.get_nindices() + 1);

    // args contains the brec_on/binduction_on arguments
    buffer<expr> args;
    buffer<name> typeformer_names;
    // add parameters and typeformers
    for (unsigned i = 0; i < nparams; i++)
        args.push_back(ref_args[i]);
    for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
        args.push_back(ref_args[i]);
        typeformer_names.push_back(fvar_name(ref_args[i]));
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
    for (name const & n1 : ind_val.get_all()) {
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
        to_telescope(lctx, ngen, lctx.get_type(C), F_args);
        expr F_result = mk_app(C, F_args);
        expr F_below  = mk_app(belows[j], F_args);
        F_args.push_back(lctx.mk_local_decl(ngen, "f", F_below));
        expr F_type   = lctx.mk_pi(F_args, F_result);
        expr F        = lctx.mk_local_decl(ngen, F_name.append_after(j+1), F_type);
        Fs.push_back(F);
        args.push_back(F);
    }

    // We define brec_on/binduction_on using the recursor for this type
    levels rec_lvls       = cons(rlvl, lvls);
    expr rec              = mk_constant(rec_info.get_name(), rec_lvls);
    // add parameters to rec
    for (unsigned i = 0; i < nparams; i++)
        rec = mk_app(rec, ref_args[i]);
    // add type formers to rec
    //     Pi indices t, prod (C ... t) (below ... t)
    for (unsigned i = nparams, j = 0; i < nparams + ntypeformers; i++, j++) {
        expr const & C = ref_args[i];
        buffer<expr> C_args;
        to_telescope(lctx, ngen, lctx.get_type(C), C_args);
        expr C_t     = mk_app(C, C_args);
        expr below_t = mk_app(belows[j], C_args);
        type_checker tc(env, lctx);
        expr prod    = mk_pprod(tc, C_t, below_t, ind);
        rec = mk_app(rec, lctx.mk_lambda(C_args, prod));
    }
    // add minor premises to rec
    for (unsigned i = nparams + ntypeformers, j = 0; i < nparams + ntypeformers + nminors; i++, j++) {
        expr minor      = ref_args[i];
        expr minor_type = lctx.get_type(minor);
        buffer<expr> minor_args;
        minor_type = to_telescope(lctx, ngen, minor_type, minor_args);
        buffer<expr> pairs;
        for (expr & minor_arg : minor_args) {
            buffer<expr> minor_arg_args;
            expr minor_arg_type = to_telescope(env, lctx, ngen, lctx.get_type(minor_arg), minor_arg_args);
            if (auto k = is_typeformer_app(typeformer_names, minor_arg_type)) {
                buffer<expr> C_args;
                get_app_args(minor_arg_type, C_args);
                type_checker tc(env, lctx);
                expr new_minor_arg_type = mk_pprod(tc, minor_arg_type, mk_app(belows[*k], C_args), ind);
                minor_arg = lctx.mk_local_decl(ngen, lctx.get_local_decl(minor_arg).get_user_name(), lctx.mk_pi(minor_arg_args, new_minor_arg_type));
                if (minor_arg_args.empty()) {
                    pairs.push_back(minor_arg);
                } else {
                    type_checker tc(env, lctx);
                    expr r = mk_app(minor_arg, minor_arg_args);
                    expr r_1 = lctx.mk_lambda(minor_arg_args, mk_pprod_fst(tc, r, ind));
                    expr r_2 = lctx.mk_lambda(minor_arg_args, mk_pprod_snd(tc, r, ind));
                    pairs.push_back(mk_pprod_mk(tc, r_1, r_2, ind));
                }
            }
        }
        type_checker tc(env, lctx);
        expr b = foldr([&](expr const & a, expr const & b) { return mk_pprod_mk(tc, a, b, ind); },
                       [&]() { return mk_unit_mk(rlvl, ind); },
                       pairs.size(), pairs.data());
        unsigned F_idx = *is_typeformer_app(typeformer_names, minor_type);
        expr F = Fs[F_idx];
        buffer<expr> F_args;
        get_app_args(minor_type, F_args);
        F_args.push_back(b);
        expr new_arg = mk_pprod_mk(tc, mk_app(F, F_args), b, ind);
        rec = mk_app(rec, lctx.mk_lambda(minor_args, new_arg));
    }
    // add indices and major to rec
    for (unsigned i = nparams + ntypeformers + nminors; i < ref_args.size(); i++)
        rec = mk_app(rec, ref_args[i]);

    type_checker tc(env, lctx);
    name brec_on_name  = name(n, ind ? g_binduction_on : g_brec_on);
    expr brec_on_type  = lctx.mk_pi(args, result_type);
    expr brec_on_value = lctx.mk_lambda(args, mk_pprod_fst(tc, rec, ind));


    declaration new_d = mk_definition_inferring_unsafe(env, brec_on_name, blps, brec_on_type, brec_on_value,
                                                       reducibility_hints::mk_abbreviation());
    environment new_env = env.add(new_d);
    new_env = set_reducible(new_env, brec_on_name, reducible_status::Reducible, true);
    new_env = add_aux_recursor(new_env, brec_on_name);
    return add_protected(new_env, brec_on_name);
}

environment mk_brec_on(environment const & env, name const & n) {
    return mk_brec_on(env, n, false);
}

environment mk_binduction_on(environment const & env, name const & n) {
    return mk_brec_on(env, n, true);
}

extern "C" LEAN_EXPORT object * lean_mk_below(object * env, object * n) {
    return catch_kernel_exceptions<environment>([&]() { return mk_below(environment(env), name(n, true)); });
}

extern "C" LEAN_EXPORT object * lean_mk_ibelow(object * env, object * n) {
    return catch_kernel_exceptions<environment>([&]() { return mk_ibelow(environment(env), name(n, true)); });
}

extern "C" LEAN_EXPORT object * lean_mk_brec_on(object * env, object * n) {
    return catch_kernel_exceptions<environment>([&]() { return mk_brec_on(environment(env), name(n, true)); });
}

extern "C" LEAN_EXPORT object * lean_mk_binduction_on(object * env, object * n) {
    return catch_kernel_exceptions<environment>([&]() { return mk_binduction_on(environment(env), name(n, true)); });
}
}
