/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "kernel/instantiate.h"
namespace lean {
/** \brief Return recursor name for the given inductive datatype name */
name mk_rec_name(name const & I);

bool is_inductive(environment const & env, name const & n);
bool is_constructor(environment const & env, name const & n);
bool is_recursor(environment const & env, name const & n);

/** \brief If \c e is a constructor application, then return the name of the constructor.
    Otherwise, return none. */
optional<name> is_constructor_app(environment const & env, expr const & e);

/** \brief Return true if the given declaration is a structure */
bool is_structure_like(environment const & env, name const & decl_name);

/* Auxiliary function for to_cnstr_when_K */
optional<expr> mk_nullary_cnstr(environment const & env, expr const & type, unsigned num_params);

/* For datatypes that support K-axiom, given `e` an element of that type, we convert (if possible)
   to the default constructor. For example, if `e : a = a`, then this method returns `eq.refl a` */
template<typename WHNF, typename INFER, typename IS_DEF_EQ>
inline expr to_cnstr_when_K(environment const & env, recursor_val const & rval, expr const & e,
                            WHNF const & whnf, INFER const & infer_type, IS_DEF_EQ const & is_def_eq) {
    lean_assert(rval.is_k());
    expr app_type    = whnf(infer_type(e));
    expr const & app_type_I = get_app_fn(app_type);
    if (!is_constant(app_type_I) || const_name(app_type_I) != rval.get_major_induct()) return e; // type incorrect
    if (has_expr_mvar(app_type)) {
        buffer<expr> app_type_args;
        get_app_args(app_type, app_type_args);
        for (unsigned i = rval.get_nparams(); i < app_type_args.size(); i++) {
            if (has_expr_metavar(app_type_args[i]))
                return e;
        }
    }
    optional<expr> new_cnstr_app = mk_nullary_cnstr(env, app_type, rval.get_nparams());
    if (!new_cnstr_app) return e;
    expr new_type    = infer_type(*new_cnstr_app);
    if (!is_def_eq(app_type, new_type)) return e;
    return *new_cnstr_app;
}

optional<recursor_rule> get_rec_rule_for(recursor_val const & rec_val, expr const & major);

expr nat_lit_to_constructor(expr const & e);
expr string_lit_to_constructor(expr const & e);

/* Auxiliary method for \c to_cnstr_when_structure, convert `e` into `mk e.1 ... e.n` */
expr expand_eta_struct(environment const & env, expr const & e_type, expr const & e);

/* If `e` is not a constructor application and its type `C ...` is a structure, return `C.mk e.1 ... e.n`,
   where `C.mk` is `C`s constructor. */
template<typename WHNF, typename INFER>
inline expr to_cnstr_when_structure(environment const & env, name const & induct_name, expr const & e,
                                    WHNF const & whnf, INFER const & infer_type) {
    if (!is_structure_like(env, induct_name) || is_constructor_app(env, e))
        return e;
    expr e_type = whnf(infer_type(e));
    if (!is_constant(get_app_fn(e_type), induct_name))
        return e;
    if (whnf(infer_type(e_type)) == mk_Prop())
        return e;
    return expand_eta_struct(env, e_type, e);
}

template<typename WHNF, typename INFER, typename IS_DEF_EQ>
inline optional<expr> inductive_reduce_rec(environment const & env, expr const & e,
                                           WHNF const & whnf, INFER const & infer_type, IS_DEF_EQ const & is_def_eq) {
    expr const & rec_fn   = get_app_fn(e);
    if (!is_constant(rec_fn)) return none_expr();
    optional<constant_info> rec_info = env.find(const_name(rec_fn));
    if (!rec_info || !rec_info->is_recursor()) return none_expr();
    buffer<expr> rec_args;
    get_app_args(e, rec_args);
    recursor_val const & rec_val = rec_info->to_recursor_val();
    unsigned major_idx           = rec_val.get_major_idx();
    if (major_idx >= rec_args.size()) return none_expr(); // major premise is missing
    expr major     = rec_args[major_idx];
    if (rec_val.is_k()) {
        major = to_cnstr_when_K(env, rec_val, major, whnf, infer_type, is_def_eq);
    }
    major = whnf(major);
    if (is_nat_lit(major))
        major = nat_lit_to_constructor(major);
    else if (is_string_lit(major))
        major = string_lit_to_constructor(major);
    else
        major = to_cnstr_when_structure(env, rec_val.get_major_induct(), major, whnf, infer_type);
    optional<recursor_rule> rule = get_rec_rule_for(rec_val, major);
    if (!rule) return none_expr();
    buffer<expr> major_args;
    get_app_args(major, major_args);
    if (rule->get_nfields() > major_args.size()) return none_expr();
    if (length(const_levels(rec_fn)) != length(rec_info->get_lparams())) return none_expr();
    expr rhs = instantiate_lparams(rule->get_rhs(), rec_info->get_lparams(), const_levels(rec_fn));
    /* apply parameters, motives and minor premises from recursor application. */
    rhs      = mk_app(rhs, rec_val.get_nparams() + rec_val.get_nmotives() + rec_val.get_nminors(), rec_args.data());
    /* The number of parameters in the constructor is not necessarily
       equal to the number of parameters in the recursor when we have
       nested inductive types. */
    unsigned nparams = major_args.size() - rule->get_nfields();
    /* apply fields from major premise */
    rhs      = mk_app(rhs, rule->get_nfields(), major_args.data() + nparams);
    if (rec_args.size() > major_idx + 1) {
        /* recursor application has more arguments after major premise */
        unsigned nextra = rec_args.size() - major_idx - 1;
        rhs = mk_app(rhs, nextra, rec_args.data() + major_idx + 1);
    }
    return some_expr(rhs);
}

template<typename WHNF, typename IS_STUCK>
optional<expr> inductive_is_stuck(environment const & env, expr const & e, WHNF const & whnf, IS_STUCK const & is_stuck) {
    expr const & rec_fn   = get_app_fn(e);
    if (!is_constant(rec_fn)) return none_expr();
    optional<constant_info> rec_info = env.find(const_name(rec_fn));
    if (!rec_info || !rec_info->is_recursor()) return none_expr();
    buffer<expr> rec_args;
    get_app_args(e, rec_args);
    recursor_val const & rec_val = rec_info->to_recursor_val();
    unsigned major_idx = rec_val.get_major_idx();
    if (rec_args.size() < major_idx + 1) return none_expr();
    expr cnstr_app = whnf(rec_args[major_idx]);
    if (rec_val.is_k()) {
        /* TODO(Leo): make it more precise.  Remark: this piece of
           code does not affect the correctness of the kernel, but the
           effectiveness of the elaborator. */
        return none_expr();
    } else {
        return is_stuck(cnstr_app);
    }
}

void initialize_inductive();
void finalize_inductive();
}
