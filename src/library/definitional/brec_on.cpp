/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/definitional/util.h"

namespace lean {
static void throw_corrupted(name const & n) {
    throw exception(sstream() << "error in 'brec_on' generation, '" << n << "' inductive datatype declaration is corrupted");
}

environment mk_below(environment const & env, name const & n) {
    if (!is_recursive_datatype(env, n))
        return env;
    if (is_inductive_predicate(env, n))
        return env;
    inductive::inductive_decls decls = *inductive::is_inductive_decl(env, n);
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
    levels blvls           = cons(lvl, lvls);
    level rlvl             = mk_max(mk_level_one(), lvl); // max 1 lvl: result universe of below
    expr Type_max_1_l      = mk_sort(rlvl);
    buffer<expr> rec_args;
    expr type              = rec_decl.get_type();

    name prod_name("prod");
    name unit_name("unit");
    expr inner_prod        = mk_constant(prod_name, {lvl,  rlvl});
    expr outer_prod        = mk_constant(prod_name, {rlvl, rlvl});
    expr unit              = mk_constant(unit_name, {rlvl});

    to_telescope(ngen, type, rec_args);
    if (rec_args.size() != nparams + ntypeformers + nminors + nindices + 1)
        throw_corrupted(n);
    buffer<expr> args;
    for (unsigned i = 0; i < nparams + ntypeformers; i++)
        args.push_back(rec_args[i]);
    // we ignore minor premises in the below type
    for (unsigned i = nparams + ntypeformers + nminors; i < rec_args.size(); i++)
        args.push_back(rec_args[i]);

    // create recursor application
    levels rec_lvls       = cons(mk_succ(rlvl), lvls);
    expr rec              = mk_constant(rec_decl.get_name(), rec_lvls);
    for (unsigned i = 0; i < nparams; i++)
        rec = mk_app(rec, args[i]);
    // add type formers
    for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
        buffer<expr> targs;
        to_telescope(ngen, mlocal_type(args[i]), targs);
        rec = mk_app(rec, Fun(targs, Type_max_1_l));
    }
    // add minor premises
    for (unsigned i = nparams + ntypeformers; i < nparams + ntypeformers + nminors; i++) {
        // TODO(Leo)
    }
    // add indices and major premise
    for (unsigned i = nparams + ntypeformers; i < args.size(); i++) {
        rec = mk_app(rec, args[i]);
    }


    name below_name  = name{n, "below"};
    expr below_type  = Pi(args, Type_max_1_l);
    expr below_value = Fun(args, rec);

    // TODO(Leo): declare below
    std::cout << " >> " << below_name  << "\n";
    std::cout << "    " << below_type  << "\n";
    std::cout << "    " << below_value << "\n";

    return env;
}
}
