/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <vector>
#include "runtime/sstream.h"
#include "runtime/utf8.h"
#include "util/name_generator.h"
#include "util/name_map.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/find_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/kernel_exception.h"

namespace lean {
static name * g_ind_fresh = nullptr;

/** \brief Return recursor name for the given inductive datatype name */
name mk_rec_name(name const & I) {
    return I + name("rec");
}

/** \brief Return true if the given declaration is a non-recursive structure (an inductive type with one constructor and no indices). */
bool is_non_rec_structure(environment const & env, name const & decl_name) {
    constant_info I = env.get(decl_name);
    if (!I.is_inductive()) return false;
    inductive_val I_val = I.to_inductive_val();
    return I_val.get_ncnstrs() == 1 && I_val.get_nindices() == 0 && !I_val.is_rec();
}

bool is_inductive(environment const & env, name const & n) {
    if (optional<constant_info> info = env.find(n))
        return info->is_inductive();
    return false;
}

bool is_constructor(environment const & env, name const & n) {
    if (optional<constant_info> info = env.find(n))
        return info->is_constructor();
    return false;
}

bool is_recursor(environment const & env, name const & n) {
    if (optional<constant_info> info = env.find(n))
        return info->is_recursor();
    return false;
}

optional<name> is_constructor_app(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (is_constant(fn)) {
        if (is_constructor(env, const_name(fn)))
            return optional<name>(const_name(fn));
    }
    return optional<name>();
}

/** Return the names of all inductive datatypes */
static names get_all_inductive_names(buffer<inductive_type> const & ind_types) {
    buffer<name> all_names;
    for (inductive_type const & ind_type : ind_types) {
        all_names.push_back(ind_type.get_name());
    }
    return names(all_names);
}

/** Return the names of all inductive datatypes in the given inductive declaration */
static names get_all_inductive_names(inductive_decl const & d) {
    buffer<inductive_type> ind_types;
    to_buffer(d.get_types(), ind_types);
    return get_all_inductive_names(ind_types);
}

/** \brief If \c d_name is the name of a non-empty inductive datatype, then return the
    name of the first constructor. Return none otherwise. */
static optional<name> get_first_cnstr(environment const & env, name const & d_name) {
    constant_info info = env.get(d_name);
    if (!info.is_inductive()) return optional<name>();
    names const & cnstrs = info.to_inductive_val().get_cnstrs();
    if (empty(cnstrs)) return optional<name>();
    return optional<name>(head(cnstrs));
}

optional<expr> mk_nullary_cnstr(environment const & env, expr const & type, unsigned num_params) {
    buffer<expr> args;
    expr const & d = get_app_args(type, args);
    if (!is_constant(d)) return none_expr();
    name const & d_name = const_name(d);
    auto cnstr_name = get_first_cnstr(env, d_name);
    if (!cnstr_name) return none_expr();
    args.shrink(num_params);
    return some(mk_app(mk_constant(*cnstr_name, const_levels(d)), args));
}

expr expand_eta_struct(environment const & env, expr const & e_type, expr const & e) {
    buffer<expr> args;
    expr const & I = get_app_args(e_type, args);
    if (!is_constant(I)) return e;
    auto ctor_name = get_first_cnstr(env, const_name(I));
    if (!ctor_name) return e;
    constructor_val ctor_val = env.get(*ctor_name).to_constructor_val();
    args.shrink(ctor_val.get_nparams());
    expr result = mk_app(mk_constant(*ctor_name, const_levels(I)), args);
    for (unsigned i = 0; i < ctor_val.get_nfields(); i++) {
        result = mk_app(result, mk_proj(const_name(I), nat(i), e));
    }
    return result;
}

optional<recursor_rule> get_rec_rule_for(recursor_val const & rec_val, expr const & major) {
    expr const & fn = get_app_fn(major);
    if (!is_constant(fn)) return optional<recursor_rule>();
    for (recursor_rule const & rule : rec_val.get_rules()) {
        if (rule.get_cnstr() == const_name(fn))
            return optional<recursor_rule>(rule);
    }
    return optional<recursor_rule>();
}

/* Auxiliary class for adding a mutual inductive datatype declaration. */
class add_inductive_fn {
    environment            m_env;
    name_generator         m_ngen;
    diagnostics *          m_diag;
    local_ctx              m_lctx;
    names      m_lparams;
    unsigned               m_nparams;
    bool                   m_is_unsafe;
    buffer<inductive_type> m_ind_types;
    buffer<unsigned>       m_nindices;
    level                  m_result_level;
    /* m_lparams ==> m_levels */
    levels                 m_levels;
    /* We track whether the resultant universe cannot be zero for any
       universe level instantiation */
    bool                   m_is_not_zero;
    /* A free variable for each parameter */
    buffer<expr>           m_params;
    /* A constant for each inductive type */
    buffer<expr>           m_ind_cnsts;

    level                  m_elim_level;
    bool                   m_K_target;

    unsigned               m_nnested;

    struct rec_info {
        expr         m_C;        /* free variable for "main" motive */
        buffer<expr> m_minors;   /* minor premises */
        buffer<expr> m_indices;
        expr         m_major;    /* major premise */
    };

    /* We have an entry for each inductive datatype being declared,
       and for nested inductive datatypes. */
    buffer<rec_info>       m_rec_infos;

public:
    add_inductive_fn(environment const & env, diagnostics * diag, inductive_decl const & decl, unsigned nnested):
        m_env(env), m_ngen(*g_ind_fresh), m_diag(diag), m_lparams(decl.get_lparams()), m_is_unsafe(decl.is_unsafe()),
        m_nnested(nnested) {
        if (!decl.get_nparams().is_small())
            throw kernel_exception(env, "invalid inductive datatype, number of parameters is too big");
        m_nparams = decl.get_nparams().get_small_value();
        to_buffer(decl.get_types(), m_ind_types);
    }

    type_checker tc() { return type_checker(m_env, m_lctx, m_diag, m_is_unsafe ? definition_safety::unsafe : definition_safety::safe); }

    /** Return type of the parameter at position `i` */
    expr get_param_type(unsigned i) const {
        return m_lctx.get_local_decl(m_params[i]).get_type();
    }

    expr mk_local_decl(name const & n, expr const & t, binder_info const & bi = binder_info()) {
        return m_lctx.mk_local_decl(m_ngen, n, consume_type_annotations(t), bi);
    }

    expr mk_local_decl_for(expr const & t) {
        lean_assert(is_pi(t));
        return m_lctx.mk_local_decl(m_ngen, binding_name(t), consume_type_annotations(binding_domain(t)), binding_info(t));
    }

    expr whnf(expr const & t) { return tc().whnf(t); }

    expr infer_type(expr const & t) { return tc().infer(t); }

    bool is_def_eq(expr const & t1, expr const & t2) { return tc().is_def_eq(t1, t2); }

    expr mk_pi(buffer<expr> const & fvars, expr const & e) const { return m_lctx.mk_pi(fvars, e); }
    expr mk_pi(expr const & fvar, expr const & e) const { return m_lctx.mk_pi(1, &fvar, e); }
    expr mk_lambda(buffer<expr> const & fvars, expr const & e) const { return m_lctx.mk_lambda(fvars, e); }
    expr mk_lambda(expr const & fvar, expr const & e) const { return m_lctx.mk_lambda(1, &fvar, e); }

    /**
       \brief Check whether the type of each datatype is well typed, and do not contain free variables or meta variables,
       all inductive datatypes have the same parameters, the number of parameters match the argument m_nparams,
       and the result universes are equivalent.

       This method also initializes the fields:
       - m_levels
       - m_result_level
       - m_nindices
       - m_ind_cnsts
       - m_params

       \remark The local context m_lctx contains the free variables in m_params. */
    void check_inductive_types() {
        m_levels   = lparams_to_levels(m_lparams);
        bool first = true;
        for (inductive_type const & ind_type : m_ind_types) {
            expr type = ind_type.get_type();
            m_env.check_name(ind_type.get_name());
            m_env.check_name(mk_rec_name(ind_type.get_name()));
            check_no_metavar_no_fvar(m_env, ind_type.get_name(), type);
            tc().check(type, m_lparams);
            m_nindices.push_back(0);
            unsigned i = 0;
            type = whnf(type);
            while (is_pi(type)) {
                if (i < m_nparams) {
                    if (first) {
                        expr param = mk_local_decl_for(type);
                        m_params.push_back(param);
                        type = instantiate(binding_body(type), param);
                    } else {
                        if (!is_def_eq(binding_domain(type), get_param_type(i)))
                            throw kernel_exception(m_env, "parameters of all inductive datatypes must match");
                        type = instantiate(binding_body(type), m_params[i]);
                    }
                    i++;
                } else {
                    expr local = mk_local_decl_for(type);
                    type = instantiate(binding_body(type), local);
                    m_nindices.back()++;
                }
                type = whnf(type);
            }
            if (i != m_nparams)
                throw kernel_exception(m_env, "number of parameters mismatch in inductive datatype declaration");

            type = tc().ensure_sort(type);

            if (first) {
                m_result_level = sort_level(type);
                m_is_not_zero  = is_not_zero(m_result_level);
            } else if (!is_equivalent(sort_level(type), m_result_level)) {
                throw kernel_exception(m_env, "mutually inductive types must live in the same universe");
            }

            m_ind_cnsts.push_back(mk_constant(ind_type.get_name(), m_levels));
            first = false;
        }

        lean_assert(length(m_levels) == length(m_lparams));
        lean_assert(m_nindices.size() == m_ind_types.size());
        lean_assert(m_ind_cnsts.size() == m_ind_types.size());
        lean_assert(m_params.size() == m_nparams);
    }

    /** \brief Return true if declaration is recursive */
    bool is_rec() {
        for (unsigned idx = 0; idx < m_ind_types.size(); idx++) {
            inductive_type const & ind_type = m_ind_types[idx];
            for (constructor const & cnstr : ind_type.get_cnstrs()) {
                expr t = constructor_type(cnstr);
                while (is_pi(t)) {
                    if (find(binding_domain(t), [&](expr const & e, unsigned) {
                                if (is_constant(e)) {
                                    for (expr const & I : m_ind_cnsts)
                                        if (const_name(I) == const_name(e))
                                            return true;
                                }
                                return false;
                            })) {
                        return true;
                    }
                    t = binding_body(t);
                }
            }
        }
        return false;
    }

    /* Return true if the given declarataion is reflexive.

       Remark: We say an inductive type `T` is reflexive if it
       contains at least one constructor that takes as an argument a
       function returning `T'` where `T'` is another inductive datatype (possibly equal to `T`)
       in the same mutual declaration. */
    bool is_reflexive() {
        for (unsigned idx = 0; idx < m_ind_types.size(); idx++) {
            inductive_type const & ind_type = m_ind_types[idx];
            for (constructor const & cnstr : ind_type.get_cnstrs()) {
                expr t = constructor_type(cnstr);
                while (is_pi(t)) {
                    expr arg_type = binding_domain(t);
                    if (is_pi(arg_type) && has_ind_occ(arg_type))
                        return true;
                    expr local = mk_local_decl_for(t);
                    t = instantiate(binding_body(t), local);
                }
            }
        }
        return false;
    }

    /** Return list with the names of all inductive datatypes in the mutual declaration. */
    names get_all_inductive_names() const {
        return ::lean::get_all_inductive_names(m_ind_types);
    }

    /** \brief Add all datatype declarations to environment. */
    void declare_inductive_types() {
        bool rec       = is_rec();
        bool reflexive = is_reflexive();
        names all = get_all_inductive_names();
        for (unsigned idx = 0; idx < m_ind_types.size(); idx++) {
            inductive_type const & ind_type = m_ind_types[idx];
            name const & n = ind_type.get_name();
            buffer<name> cnstr_names;
            for (constructor const & cnstr : ind_type.get_cnstrs()) {
                cnstr_names.push_back(constructor_name(cnstr));
            }
            m_env.check_name(n);
            m_env.add_core(constant_info(inductive_val(n, m_lparams, ind_type.get_type(), m_nparams, m_nindices[idx],
                                                       all, names(cnstr_names), m_nnested, rec, m_is_unsafe, reflexive)));
        }
    }

    /** \brief Return true iff `t` is a term of the form `I As t`
        where `I` is the inductive datatype at position `i` being declared,
        `As` are the global parameters of this declaration,
        and `t` does not contain any inductive datatype being declared. */
    bool is_valid_ind_app(expr const & t, unsigned i) {
        buffer<expr> args;
        expr I = get_app_args(t, args);
        if (I != m_ind_cnsts[i] || args.size() != m_nparams + m_nindices[i])
            return false;
        for (unsigned i = 0; i < m_nparams; i++) {
            if (m_params[i] != args[i])
                return false;
        }
        /*
        Ensure that `t` does not contain the inductive datatype that is being declared.
        Such occurrences are unsound in general. https://github.com/leanprover/lean4/issues/2125
        We also used to reject them in Lean 3.
        */
        for (unsigned i = m_nparams; i < args.size(); i++) {
            if (has_ind_occ(args[i]))
                return false;
        }
        return true;
    }

    /** \brief Return some(i) iff `t` is of the form `I As t` where `I` the inductive `i`-th datatype being defined. */
    optional<unsigned> is_valid_ind_app(expr const & t) {
        for (unsigned i = 0; i < m_ind_types.size(); i++) {
            if (is_valid_ind_app(t, i))
                return optional<unsigned>(i);
        }
        return optional<unsigned>();
    }

    /** \brief Return true iff `e` is one of the inductive datatype being declared. */
    bool is_ind_occ(expr const & e) {
        return
            is_constant(e) &&
            std::any_of(m_ind_cnsts.begin(), m_ind_cnsts.end(),
                        [&](expr const & c) { return const_name(e) == const_name(c); });
    }

    /** \brief Return true iff `t` does not contain any occurrence of a datatype being declared. */
    bool has_ind_occ(expr const & t) {
        return static_cast<bool>(find(t, [&](expr const & e, unsigned) { return is_ind_occ(e); }));
    }

    /** \brief Return `some(d_idx)` iff `t` is a recursive argument, `d_idx` is the index of the
        recursive inductive datatype. Otherwise, return `none`. */
    optional<unsigned> is_rec_argument(expr t) {
        t = whnf(t);
        while (is_pi(t)) {
            expr local = mk_local_decl_for(t);
            t = whnf(instantiate(binding_body(t), local));
        }
        return is_valid_ind_app(t);
    }

    /** \brief Check if \c t contains only positive occurrences of the inductive datatypes being declared. */
    void check_positivity(expr t, name const & cnstr_name, int arg_idx) {
        t = whnf(t);
        if (!has_ind_occ(t)) {
            // nonrecursive argument
        } else if (is_pi(t)) {
            if (has_ind_occ(binding_domain(t)))
                throw kernel_exception(m_env, sstream() << "arg #" << (arg_idx + 1) << " of '" << cnstr_name << "' "
                                       "has a non positive occurrence of the datatypes being declared");
            expr local = mk_local_decl_for(t);
            check_positivity(instantiate(binding_body(t), local), cnstr_name, arg_idx);
        } else if (is_valid_ind_app(t)) {
            // recursive argument
        } else {
            throw kernel_exception(m_env, sstream() << "arg #" << (arg_idx + 1) << " of '" << cnstr_name << "' "
                                   "contains a non valid occurrence of the datatypes being declared");
        }
    }

    /** \brief Check whether the constructor declarations are type correct, parameters are in the expected positions,
        constructor fields are in acceptable universe levels, positivity constraints, and returns the expected result. */
    void check_constructors() {
        for (unsigned idx = 0; idx < m_ind_types.size(); idx++) {
            inductive_type const & ind_type = m_ind_types[idx];
            name_set found_cnstrs;
            for (constructor const & cnstr : ind_type.get_cnstrs()) {
                name const & n = constructor_name(cnstr);
                if (found_cnstrs.contains(n)) {
                    throw kernel_exception(m_env, sstream() << "duplicate constructor name '" << n << "'");
                }
                found_cnstrs.insert(n);
                expr t = constructor_type(cnstr);
                m_env.check_name(n);
                check_no_metavar_no_fvar(m_env, n, t);
                tc().check(t, m_lparams);
                unsigned i = 0;
                while (is_pi(t)) {
                    if (i < m_nparams) {
                        if (!is_def_eq(binding_domain(t), get_param_type(i)))
                            throw kernel_exception(m_env, sstream() << "arg #" << (i + 1) << " of '" << n << "' "
                                                   << "does not match inductive datatypes parameters'");
                        t = instantiate(binding_body(t), m_params[i]);
                    } else {
                        expr s = tc().ensure_type(binding_domain(t));
                        // the sort is ok IF
                        //   1- its level is <= inductive datatype level, OR
                        //   2- is an inductive predicate
                        if (!(is_geq(m_result_level, sort_level(s)) || normalizes_to_zero(m_result_level))) {
                            throw kernel_exception(m_env, sstream() << "universe level of type_of(arg #" << (i + 1) << ") "
                                                   << "of '" << n << "' is too big for the corresponding inductive datatype");
                        }
                        if (!m_is_unsafe)
                            check_positivity(binding_domain(t), n, i);
                        expr local = mk_local_decl_for(t);
                        t = instantiate(binding_body(t), local);
                    }
                    i++;
                }
                if (!is_valid_ind_app(t, idx))
                    throw kernel_exception(m_env, sstream() << "invalid return type for '" << n << "'");
            }
        }
    }

    void declare_constructors() {
        for (unsigned idx = 0; idx < m_ind_types.size(); idx++) {
            inductive_type const & ind_type = m_ind_types[idx];
            unsigned cidx = 0;
            for (constructor const & cnstr : ind_type.get_cnstrs()) {
                name const & n = constructor_name(cnstr);
                expr const & t = constructor_type(cnstr);
                unsigned arity = 0;
                expr it = t;
                while (is_pi(it)) {
                    it = binding_body(it);
                    arity++;
                }
                lean_assert(arity >= m_nparams);
                unsigned nfields = arity - m_nparams;
                m_env.check_name(n);
                m_env.add_core(constant_info(constructor_val(n, m_lparams, t, ind_type.get_name(), cidx, m_nparams, nfields, m_is_unsafe)));
                cidx++;
            }
        }
    }

    /** \brief Return true if recursor can only map into Prop */
    bool elim_only_at_universe_zero() {
        if (m_is_not_zero) {
            /* For every universe parameter assignment, the resultant universe is not 0.
               So, it is not an inductive predicate */
            return false;
        }

        if (m_ind_types.size() > 1) {
            /* Mutually recursive inductive predicates only eliminate into Prop. */
            return true;
        }

        unsigned num_intros = length(m_ind_types[0].get_cnstrs());
        if (num_intros > 1) {
            /* We have more than one constructor, then recursor for inductive predicate
               can only eliminate intro Prop. */
            return true;
        }

        if (num_intros == 0) {
            /* empty inductive predicate (e.g., `false`) can eliminate into any universe */
            return false;
        }

        /* We have only one constructor, the final check is, the type of each argument
           that is not a parameter:
            1- It must live in Prop, *OR*
            2- It must occur in the return type. (this is essentially what is called a non-uniform parameter in Coq).
               We can justify 2 by observing that this information is not a *secret* it is part of the type.
               By eliminating to a non-proposition, we would not be revealing anything that is not already known. */
        constructor const & cnstr = head(m_ind_types[0].get_cnstrs());
        expr type  = constructor_type(cnstr);
        unsigned i = 0;
        buffer<expr> to_check; /* Arguments that we must check if occur in the result type */
        while (is_pi(type)) {
            expr fvar = mk_local_decl_for(type);
            if (i >= m_nparams) {
                expr s = tc().ensure_type(binding_domain(type));
                if (!normalizes_to_zero(sort_level(s))) {
                    /* Current argument is not in Prop (i.e., condition 1 failed).
                       We save it in to_check to be able to try condition 2 above. */
                    to_check.push_back(fvar);
                }
            }
            type = instantiate(binding_body(type), fvar);
            i++;
        }
        buffer<expr> result_args;
        get_app_args(type, result_args);
        /* Check condition 2: every argument in to_check must occur in result_args */
        for (expr const & arg : to_check) {
            if (std::find(result_args.begin(), result_args.end(), arg) == result_args.end())
                return true; /* Condition 2 failed */
        }
        return false;
    }

    /** \brief Initialize m_elim_level. */
    void init_elim_level() {
        if (elim_only_at_universe_zero()) {
            m_elim_level = mk_level_zero();
        } else {
            name u("u");
            int i = 1;
            while (std::find(m_lparams.begin(), m_lparams.end(), u) != m_lparams.end()) {
                u = name("u").append_after(i);
                i++;
            }
            m_elim_level = mk_univ_param(u);
        }
    }

    void init_K_target() {
        /* A declaration is target for K-like reduction when
           it has one intro, the intro has 0 arguments, and it is an inductive predicate.
           In the following for-loop we check if the intro rule has 0 fields. */
        m_K_target =
            m_ind_types.size() == 1 &&              /* It is not a mutual declaration (for simplicity, we don't gain anything by supporting K in mutual declarations. */
            normalizes_to_zero(m_result_level) &&   /* It is an inductive predicate. */
            length(m_ind_types[0].get_cnstrs()) == 1; /* Inductive datatype has only one constructor. */
        if (!m_K_target)
            return;
        expr it = constructor_type(head(m_ind_types[0].get_cnstrs()));
        unsigned i = 0;
        while (is_pi(it)) {
            if (i < m_nparams) {
                it = binding_body(it);
            } else {
                /* See comment above */
                m_K_target = false;
                break;
            }
            i++;
        }
    }

    /** \brief Given `t` of the form `I As is` where `I` is one of the inductive datatypes being defined,
        As are the global parameters, and is the actual indices provided to it.
        Return the index of `I`, and store is in the argument `indices`. */
    unsigned get_I_indices(expr const & t, buffer<expr> & indices) {
        optional<unsigned> r = is_valid_ind_app(t);
        lean_assert(r);
        buffer<expr> all_args;
        get_app_args(t, all_args);
        for (unsigned i = m_nparams; i < all_args.size(); i++)
            indices.push_back(all_args[i]);
        return *r;
    }

    /** \brief Populate m_rec_infos. */
    void mk_rec_infos() {
        unsigned d_idx = 0;
        /* First, populate the fields, m_C, m_indices, m_major */
        for (inductive_type const & ind_type : m_ind_types) {
            rec_info info;
            expr t      = ind_type.get_type();
            unsigned i  = 0;
            t = whnf(t);
            while (is_pi(t)) {
                if (i < m_nparams) {
                    t = instantiate(binding_body(t), m_params[i]);
                } else {
                    expr idx = mk_local_decl_for(t);
                    info.m_indices.push_back(idx);
                    t = instantiate(binding_body(t), idx);
                }
                i++;
                t = whnf(t);
            }
            info.m_major = mk_local_decl("t", mk_app(mk_app(m_ind_cnsts[d_idx], m_params), info.m_indices));
            expr C_ty = mk_sort(m_elim_level);
            C_ty      = mk_pi(info.m_major, C_ty);
            C_ty      = mk_pi(info.m_indices, C_ty);
            name C_name("motive");
            if (m_ind_types.size() > 1)
                C_name = name(C_name).append_after(d_idx+1);
            info.m_C = mk_local_decl(C_name, C_ty);
            m_rec_infos.push_back(info);
            d_idx++;
        }
        /* First, populate the field m_minors */
        d_idx = 0;
        for (inductive_type const & ind_type : m_ind_types) {
            name ind_type_name = ind_type.get_name();
            for (constructor const & cnstr : ind_type.get_cnstrs()) {
                buffer<expr> b_u; // nonrec and rec args;
                buffer<expr> u;   // rec args
                buffer<expr> v;   // inductive args
                name cnstr_name = constructor_name(cnstr);
                expr t          = constructor_type(cnstr);
                unsigned i      = 0;
                while (is_pi(t)) {
                    if (i < m_nparams) {
                        t = instantiate(binding_body(t), m_params[i]);
                    } else {
                        expr l = mk_local_decl_for(t);
                        b_u.push_back(l);
                        if (is_rec_argument(binding_domain(t)))
                            u.push_back(l);
                        t = instantiate(binding_body(t), l);
                    }
                    i++;
                }
                buffer<expr> it_indices;
                unsigned it_idx = get_I_indices(t, it_indices);
                expr C_app      = mk_app(m_rec_infos[it_idx].m_C, it_indices);
                expr intro_app  = mk_app(mk_app(mk_constant(cnstr_name, m_levels), m_params), b_u);
                C_app = mk_app(C_app, intro_app);
                /* populate v using u */
                for (unsigned i = 0; i < u.size(); i++) {
                    expr u_i    = u[i];
                    expr u_i_ty = whnf(infer_type(u_i));
                    buffer<expr> xs;
                    while (is_pi(u_i_ty)) {
                        expr x = mk_local_decl_for(u_i_ty);
                        xs.push_back(x);
                        u_i_ty = whnf(instantiate(binding_body(u_i_ty), x));
                    }
                    buffer<expr> it_indices;
                    unsigned it_idx = get_I_indices(u_i_ty, it_indices);
                    expr C_app  = mk_app(m_rec_infos[it_idx].m_C, it_indices);
                    expr u_app  = mk_app(u_i, xs);
                    C_app = mk_app(C_app, u_app);
                    expr v_i_ty = mk_pi(xs, C_app);
                    local_decl u_i_decl = m_lctx.get_local_decl(fvar_name(u_i));
                    expr v_i    = mk_local_decl(u_i_decl.get_user_name().append_after("_ih"), v_i_ty, binder_info());
                    v.push_back(v_i);
                }
                expr minor_ty   = mk_pi(b_u, mk_pi(v, C_app));
                name minor_name = cnstr_name.replace_prefix(ind_type_name, name());
                expr minor      = mk_local_decl(minor_name, minor_ty);
                m_rec_infos[d_idx].m_minors.push_back(minor);
            }
            d_idx++;
        }
    }

    /** \brief Return the levels for the recursor. */
    levels get_rec_levels() {
        if (is_param(m_elim_level))
            return levels(m_elim_level, m_levels);
        else
            return m_levels;
    }

    /** \brief Return the level parameter names for the recursor. */
    names get_rec_lparams() {
        if (is_param(m_elim_level))
            return names(param_id(m_elim_level), m_lparams);
        else
            return m_lparams;
    }


    /** \brief Store all type formers in `Cs` */
    void collect_Cs(buffer<expr> & Cs) {
        for (unsigned i = 0; i < m_ind_types.size(); i++)
            Cs.push_back(m_rec_infos[i].m_C);
    }

    /** \brief Store all minor premises in `ms`. */
    void collect_minor_premises(buffer<expr> & ms) {
        for (unsigned i = 0; i < m_ind_types.size(); i++)
            ms.append(m_rec_infos[i].m_minors);
    }

    recursor_rules mk_rec_rules(unsigned d_idx, buffer<expr> const & Cs, buffer<expr> const & minors, unsigned & minor_idx) {
        inductive_type const & d = m_ind_types[d_idx];
        levels lvls = get_rec_levels();
        buffer<recursor_rule> rules;
        for (constructor const & cnstr : d.get_cnstrs()) {
            buffer<expr> b_u;
            buffer<expr> u;
            expr t = constructor_type(cnstr);
            unsigned i = 0;
            while (is_pi(t)) {
                if (i < m_nparams) {
                    t = instantiate(binding_body(t), m_params[i]);
                } else {
                    expr l = mk_local_decl_for(t);
                    b_u.push_back(l);
                    if (is_rec_argument(binding_domain(t)))
                        u.push_back(l);
                    t = instantiate(binding_body(t), l);
                }
                i++;
            }
            buffer<expr> v;
            for (unsigned i = 0; i < u.size(); i++) {
                expr u_i    = u[i];
                expr u_i_ty = whnf(infer_type(u_i));
                buffer<expr> xs;
                while (is_pi(u_i_ty)) {
                    expr x = mk_local_decl_for(u_i_ty);
                    xs.push_back(x);
                    u_i_ty = whnf(instantiate(binding_body(u_i_ty), x));
                }
                buffer<expr> it_indices;
                unsigned it_idx = get_I_indices(u_i_ty, it_indices);
                name rec_name   = mk_rec_name(m_ind_types[it_idx].get_name());
                expr rec_app    = mk_constant(rec_name, lvls);
                rec_app         = mk_app(mk_app(mk_app(mk_app(mk_app(rec_app, m_params), Cs), minors), it_indices), mk_app(u_i, xs));
                v.push_back(mk_lambda(xs, rec_app));
            }
            expr e_app    = mk_app(mk_app(minors[minor_idx], b_u), v);
            expr comp_rhs = mk_lambda(m_params, mk_lambda(Cs, mk_lambda(minors, mk_lambda(b_u, e_app))));
            rules.push_back(recursor_rule(constructor_name(cnstr), b_u.size(), comp_rhs));
            minor_idx++;
        }
        return recursor_rules(rules);
    }

    /** \brief Declare recursors. */
    void declare_recursors() {
        buffer<expr> Cs; collect_Cs(Cs);
        buffer<expr> minors; collect_minor_premises(minors);
        unsigned nminors   = minors.size();
        unsigned nmotives  = Cs.size();
        names all          = get_all_inductive_names();
        unsigned minor_idx = 0;
        for (unsigned d_idx = 0; d_idx < m_ind_types.size(); d_idx++) {
            rec_info const & info = m_rec_infos[d_idx];
            expr C_app            = mk_app(mk_app(info.m_C, info.m_indices), info.m_major);
            expr rec_ty           = mk_pi(info.m_major, C_app);
            rec_ty                = mk_pi(info.m_indices, rec_ty);
            rec_ty                = mk_pi(minors, rec_ty);
            rec_ty                = mk_pi(Cs, rec_ty);
            rec_ty                = mk_pi(m_params, rec_ty);
            rec_ty                = infer_implicit(rec_ty, true /* strict */);
            recursor_rules rules  = mk_rec_rules(d_idx, Cs, minors, minor_idx);
            name rec_name         = mk_rec_name(m_ind_types[d_idx].get_name());
            names rec_lparams     = get_rec_lparams();
            m_env.check_name(rec_name);
            m_env.add_core(constant_info(recursor_val(rec_name, rec_lparams, rec_ty, all,
                                                      m_nparams, m_nindices[d_idx], nmotives, nminors,
                                                      rules, m_K_target, m_is_unsafe)));
        }
    }

    environment operator()() {
        m_env.check_duplicated_univ_params(m_lparams);
        check_inductive_types();
        declare_inductive_types();
        check_constructors();
        declare_constructors();
        init_elim_level();
        init_K_target();
        mk_rec_infos();
        declare_recursors();
        return m_env;
    }
};




/* Every recursor a nested inductive declaration introduces: one per type of the mutual block it was
   written as, then one per nested occurrence, the latter named after the block's head. Together their
   rules are the whole of what the declaration makes definitional. */

/* The arities a recursor is declared with, derived from its type rather than copied.

   `major_idx` is `nparams + nmotives + nminors + nindices`, and iota takes that argument for the major
   premise, so these have to be right. The kernel copies them off its own auxiliary declaration today;
   were the elimination to move out of it there would be nothing to copy from, and reading them back
   off the type is a check on what it was handed rather than trust in it.

   A motive is a binder whose type ends in a sort. The indices belong to the type being eliminated and
   come from its own arity, and the minors are then whatever is left. */
static bool derive_rec_arities_core(environment const & env, expr const & rec_type, unsigned nparams,
                                    unsigned & nmotives, unsigned & nminors, unsigned & nindices) {
    local_ctx lctx;
    name_generator ngen(*g_ind_fresh);
    buffer<expr> doms;
    expr ty = rec_type;
    while (is_pi(ty)) {
        expr l = lctx.mk_local_decl(ngen, binding_name(ty), binding_domain(ty), binding_info(ty));
        doms.push_back(binding_domain(ty));
        ty = instantiate(binding_body(ty), l);
    }
    unsigned total = doms.size();
    if (total < nparams + 1) return false;
    /* a motive is a binder after the parameters whose type ends in a sort; a minor premise ends in an
       application of one of them, so the run of motives is where they stop */
    nmotives = 0;
    for (unsigned i = nparams; i < total; i++) {
        expr cod = doms[i];
        while (is_pi(cod)) cod = binding_body(cod);
        if (!is_sort(cod)) break;
        nmotives++;
    }
    /* The major premise is last, and its type says how many of the arguments to the type being
       eliminated are indices. Its own parameters are not indices, and for an auxiliary recursor they
       are not parameters of the recursor either: the nesting fixed them. So they cannot be read off
       the recursor's telescope, nor off the eliminated type's arity, only off here. */
    buffer<expr> major_args;
    expr major_fn = get_app_args(doms[total - 1], major_args);
    if (!is_constant(major_fn)) return false;
    optional<constant_info> major_ind = env.find(const_name(major_fn));
    if (!major_ind || !major_ind->is_inductive()) return false;
    unsigned major_nparams = major_ind->to_inductive_val().get_nparams();
    if (major_args.size() < major_nparams) return false;
    nindices = major_args.size() - major_nparams;
    if (total < nparams + nmotives + nindices + 1) return false;
    nminors = total - nparams - nmotives - nindices - 1;
    return true;
}

/* The equations a recursor's rules assert, one per rule, closed under every binder they mention.

   Stating these here rather than accepting them from the certificate is the whole point: the kernel
   says what it is about to make definitional, and a certificate has to prove exactly that. Accepting
   the statement along with its proof would let a certificate prove something else and be believed.

   The equations are stated over the constants of `env`, in which the rules already hold by
   construction, so as they stand they are vacuous. The caller substitutes a model for those constants
   before asking for proofs, and that substitution is what gives them content. */
static void mk_rule_equations(environment const & env, name const & rec_name, buffer<expr> & eqs,
                              buffer<expr> & sides) {
    constant_info rec_info = env.get(rec_name);
    recursor_val rec_val   = rec_info.to_recursor_val();
    unsigned nparams       = rec_val.get_nparams();
    unsigned nmotives      = rec_val.get_nmotives();
    unsigned nminors       = rec_val.get_nminors();
    unsigned nindices      = rec_val.get_nindices();
    local_ctx lctx;
    name_generator ngen(*g_ind_fresh);
    /* the recursor's parameters, motives and minor premises, which every rule is stated under */
    buffer<expr> tele;
    expr ty = rec_info.get_type();
    for (unsigned i = 0; i < nparams + nmotives + nminors + nindices; i++) {
        if (!is_pi(ty)) return;
        expr l = lctx.mk_local_decl(ngen, binding_name(ty), binding_domain(ty), binding_info(ty));
        if (i < nparams + nmotives + nminors)
            tele.push_back(l);
        ty = instantiate(binding_body(ty), l);
    }
    /* The major premise's type says which type this recursor eliminates and at which parameters, and
       that is where a rule's constructor takes its own parameters and levels from. An auxiliary
       recursor's rules name constructors of the declaration that was nested under, whose parameter
       count is its own and whose parameters are the ones the nesting specialised it at, so neither
       can be read off the recursor's telescope. */
    if (!is_pi(ty)) return;
    buffer<expr> major_args;
    expr major_fn = get_app_args(binding_domain(ty), major_args);
    if (!is_constant(major_fn)) return;
    levels c_lvls = const_levels(major_fn);
    type_checker tc(env, lctx);
    for (recursor_rule const & rule : rec_val.get_rules()) {
        constant_info c_info = env.get(rule.get_cnstr());
        unsigned c_nparams   = c_info.to_constructor_val().get_nparams();
        if (major_args.size() < c_nparams) return;
        expr c_ty = instantiate_type_lparams(c_info, c_lvls);
        for (unsigned i = 0; i < c_nparams; i++) {
            if (!is_pi(c_ty)) return;
            c_ty = instantiate(binding_body(c_ty), major_args[i]);
        }
        /* the constructor's own fields, and with them the indices it concludes at */
        buffer<expr> fields;
        while (is_pi(c_ty)) {
            expr l = lctx.mk_local_decl(ngen, binding_name(c_ty), binding_domain(c_ty), binding_info(c_ty));
            fields.push_back(l);
            c_ty = instantiate(binding_body(c_ty), l);
        }
        buffer<expr> c_args;
        get_app_args(c_ty, c_args);
        if (c_args.size() < c_nparams) return;
        expr major = mk_app(mk_app(mk_constant(rule.get_cnstr(), c_lvls), c_nparams, major_args.data()),
                            fields);
        buffer<expr> lhs_args;
        lhs_args.append(tele);
        for (unsigned i = c_nparams; i < c_args.size(); i++)
            lhs_args.push_back(c_args[i]);
        lhs_args.push_back(major);
        expr lhs = mk_app(mk_constant(rec_name, lparams_to_levels(rec_info.get_lparams())), lhs_args);
        expr rhs = mk_app(mk_app(instantiate_lparams(rule.get_rhs(), rec_info.get_lparams(),
                                                     lparams_to_levels(rec_info.get_lparams())),
                                 tele), fields);
        expr A   = tc.infer(lhs);
        level u  = sort_level(tc.ensure_type(A));
        expr eq  = mk_app(mk_constant(name("Eq"), levels(u)), A, lhs, rhs);
        buffer<expr> binders;
        binders.append(tele);
        binders.append(fields);
        eqs.push_back(lctx.mk_pi(binders, eq));
        /* A rule that already holds definitionally has no certificate, and needs none. The two sides
           go out closed under the same binders so the caller can ask that directly, rather than by
           type checking a reflexivity proof of one of them. */
        sides.push_back(lctx.mk_lambda(binders, lhs));
        sides.push_back(lctx.mk_lambda(binders, rhs));
    }
}

extern "C" object * lean_certify_nested_inductive(obj_arg env, obj_arg d);

/* Require a certificate for the computation rules the kernel states about a nested inductive
   declaration.

   `add_inductive_fn` checks the mutual model, but the rewrite of its types and rules back into the
   nested presentation below is `add_core`d unchecked, and those rules are what the declaration makes
   definitional. `Lean.Meta.NestedGen.certify` rebuilds the model and proves them over it; the
   equations themselves are stated here, by `mk_rule_equations`, so that what gets proved is what is
   about to be believed rather than whatever the generator chose to state.
 */
struct derived_rec {
    name           m_name;
    names          m_lparams;
    expr           m_type;
    recursor_rules m_rules;
    /* the theorem discharging each rule, aligned with `m_rules`; empty where it holds definitionally */
    std::vector<name>  m_rule_proofs;
};

/* What the Lean side returns: the environment holding the model and the proofs, the constant of the
   model standing for each constant of this declaration, the theorems, and the recursors it derived. */
struct nested_certificate {
    bool                     m_present = false;
    optional<environment>    m_env;
    std::vector<derived_rec> m_recs;
    std::vector<bool>        m_reflexive;
};

static nested_certificate get_nested_certificate(environment const & env, declaration const & d,
                                                 name const & decl_name) {
    object * r = lean_certify_nested_inductive(env.to_obj_arg(), d.to_obj_arg());
    if (!lean_io_result_is_ok(r)) {
        lean_io_result_show_error(r);
        lean_dec_ref(r);
        throw kernel_exception(env, sstream() << "failed to certify the computation rules of nested "
                                                 "inductive type '" << decl_name << "'");
    }
    /* `Except String (Option Certificate)`: tag 0 carries the message, tag 1 the certificate, and
       within that a scalar means there was nothing to reason with and nothing was checked. */
    object * v = lean_io_result_get_value(r);
    if (lean_obj_tag(v) == 0) {
        std::string msg(lean_string_cstr(lean_ctor_get(v, 0)));
        lean_dec_ref(r);
        throw kernel_exception(env, sstream() << "uncertified computation rule of nested inductive "
                                                 "type '" << decl_name << "': " << msg);
    }
    object * cert_opt = lean_ctor_get(v, 0);
    nested_certificate cert;
    if (lean_is_scalar(cert_opt)) {
        lean_dec_ref(r);
        return cert;
    }
    object * c = lean_ctor_get(cert_opt, 0);
    cert.m_env = optional<environment>(environment(lean_ctor_get(c, 0), true));
    object * crecs = lean_ctor_get(c, 1);
    /* `RestoredRec`: name, level parameters, type, index count, and one rule per constructor. Read
       before the result is released, since these are borrowed pointers into it. */
    for (size_t i = 0; i < lean_array_size(crecs); i++) {
        object * o = lean_array_get_core(crecs, i);
        derived_rec dr;
        dr.m_name     = name(lean_ctor_get(o, 0), true);
        dr.m_lparams  = names(lean_ctor_get(o, 1), true);
        dr.m_type     = expr(lean_ctor_get(o, 2), true);
        object * rules = lean_ctor_get(o, 4);
        buffer<recursor_rule> rs;
        for (size_t j = 0; j < lean_array_size(rules); j++) {
            object * rl  = lean_array_get_core(rules, j);
            object * snd = lean_ctor_get(rl, 1);
            rs.push_back(recursor_rule(name(lean_ctor_get(rl, 0), true),
                                       static_cast<unsigned>(lean_unbox(lean_ctor_get(snd, 0))),
                                       expr(lean_ctor_get(snd, 1), true)));
        }
        dr.m_rules = recursor_rules(rs);
        object * prfs = lean_ctor_get(o, 5);
        for (size_t j = 0; j < lean_array_size(prfs); j++) {
            object * p = lean_array_get_core(prfs, j);
            dr.m_rule_proofs.push_back(lean_is_scalar(p) ? name() : name(lean_ctor_get(p, 0), true));
        }
        cert.m_recs.push_back(dr);
    }
    object * refl = lean_ctor_get(c, 2);
    for (size_t i = 0; i < lean_array_size(refl); i++)
        cert.m_reflexive.push_back(lean_unbox(lean_array_get_core(refl, i)) != 0);
    lean_dec_ref(r);
    cert.m_present = true;
    return cert;
}

/* Every rule the declaration states, restated over the model and matched against the certificate. */
static void check_nested_rules(environment const & env, name const & decl_name,
                               nested_certificate const & cert) {
    environment const & cert_env = *cert.m_env;
    /* The rules exactly as the kernel is about to make them definitional. They are stated about the
       constants this declaration introduces, where they hold by fiat; what gives them content is
       that the certificate has to satisfy them for definitions realising those same constants.

       Following the certificate's recursors is following exactly what was declared: the loop above
       declared one for each, and `check_name` refused any that already existed. */
    type_checker tc(cert_env);
    for (derived_rec const & dr : cert.m_recs) {
        buffer<expr> eqs, sides;
        mk_rule_equations(env, dr.m_name, eqs, sides);
        if (dr.m_rule_proofs.size() != eqs.size())
            throw kernel_exception(env, sstream() << "the certificate does not answer for every rule of '"
                                                  << dr.m_name << "'");
        for (unsigned i = 0; i < eqs.size(); i++) {
            /* either it holds definitionally over the model, or the named theorem proves it */
            if (tc.is_def_eq(sides[2*i], sides[2*i + 1]))
                continue;
            bool proved = false;
            name const & pn = dr.m_rule_proofs[i];
            if (!pn.is_anonymous()) {
                optional<constant_info> pi = cert_env.find(pn);
                if (pi && length(pi->get_lparams()) == length(dr.m_lparams))
                    proved = tc.is_def_eq(instantiate_type_lparams(*pi, lparams_to_levels(dr.m_lparams)),
                                          eqs[i]);
            }
            /* the theorem names the recursor and the constructor whose rule it is meant to discharge */
            if (!proved)
                throw kernel_exception(env, sstream() << "no certificate for a computation rule of nested "
                                                         "inductive type '" << decl_name << "': "
                                                      << (pn.is_anonymous() ? name("none was named") : pn)
                                                      << " does not prove it");
        }
    }
}

static unsigned count_binders(expr e) {
    unsigned n = 0;
    while (is_pi(e)) { n++; e = binding_body(e); }
    return n;
}

environment environment::add_inductive(declaration const & d) const {
    inductive_decl ind_d(d);
    scoped_diagnostics diag(*this, true);
    names all_ind_names = get_all_inductive_names(ind_d);
    /* Asked of every declaration, since a certified one is declared without being checked here. */
    for (inductive_type const & ind_type : ind_d.get_types()) {
        check_no_metavar_no_fvar(*this, ind_type.get_name(), ind_type.get_type());
        for (constructor const & cnstr : ind_type.get_cnstrs())
            check_no_metavar_no_fvar(*this, constructor_name(cnstr), constructor_type(cnstr));
    }
    /* Whether there is a nested occurrence is decided by the code that would unfold it, so that one
       definition of what counts as an occurrence serves both. Getting it wrong is conservative either
       way: an occurrence reported where there is none leaves the model equal to the declaration, which
       is checked all the same, and one missed sends the declaration to `add_inductive_fn`, whose
       positivity check rejects it. */
    nested_certificate cert = get_nested_certificate(*this, d, head(all_ind_names));
    if (!cert.m_present)
        return diag.update(add_inductive_fn(*this, diag.get(), ind_d, 0)());
    /* A nested declaration is not checked here but declared over a model: the certificate carries the
       recursors, and every constant declared is required to be inhabited in the environment the model
       was checked in, at the type declared for it. */
    unsigned nparams = ind_d.get_nparams().get_small_value();
    unsigned ntypes  = length(ind_d.get_types());
    if (cert.m_recs.size() < ntypes || cert.m_reflexive.size() != ntypes)
        throw kernel_exception(*this, sstream() << "the certificate for '" << head(all_ind_names)
                                                << "' does not cover the declaration's types");
    /* Each constant is declared only once the certificate is shown to define it, at the type being
       declared. A definition is what makes the rules say something -- were the certificate to hold
       the recursor this kernel is about to declare, its rules would hold by the very fiat they are
       meant to justify. Nothing here reads the environment being built, so every check can and does
       come before the `add_core` it licenses. */
    auto realises = [&](name const & n, names const & lps, expr const & ty) {
        /* an unsafe declaration is outside the kernel's guarantees and nothing realises it: a
           definition over the model may not mention an unsafe constant */
        if (ind_d.is_unsafe()) return;
        optional<constant_info> mi = cert.m_env->find(n);
        /* universe parameters are matched by position, not by name: the model was built separately */
        if (!mi || !mi->is_definition()
                || length(lps) != length(mi->get_lparams())
                || instantiate_type_lparams(*mi, lparams_to_levels(lps)) != ty)
            throw kernel_exception(*this, sstream() << "the certificate does not define '" << n
                                                    << "' at its declared type");
    };
    /* Field counts reach iota, so take them from the rules the recursors state rather than from a
       second count of the same binders. */
    name_map<unsigned> rule_nfields;
    for (derived_rec const & dr : cert.m_recs)
        for (recursor_rule const & r : dr.m_rules)
            rule_nfields.insert(r.get_cnstr(), r.get_nfields());
    environment new_env = *this;
    unsigned ind_idx = 0;
    for (inductive_type const & ind_type : ind_d.get_types()) {
        buffer<name> cnstr_names;
        for (constructor const & c : ind_type.get_cnstrs())
            cnstr_names.push_back(constructor_name(c));
        unsigned type_binders = count_binders(ind_type.get_type());
        if (type_binders < nparams)
            throw kernel_exception(*this, sstream() << "'" << ind_type.get_name() << "' takes fewer than "
                                                    << nparams << " parameters");
        realises(ind_type.get_name(), ind_d.get_lparams(), ind_type.get_type());
        new_env.check_name(ind_type.get_name());
        new_env.add_core(constant_info(inductive_val(ind_type.get_name(), ind_d.get_lparams(),
                                                     ind_type.get_type(), nparams, type_binders - nparams,
                                                     all_ind_names, names(cnstr_names),
                                                     cert.m_recs.size() - ntypes, true, ind_d.is_unsafe(),
                                                     cert.m_reflexive[ind_idx])));
        ind_idx++;
        unsigned cidx = 0;
        for (constructor const & c : ind_type.get_cnstrs()) {
            unsigned cnstr_binders = count_binders(constructor_type(c));
            unsigned const * stated = rule_nfields.find(constructor_name(c));
            if (cnstr_binders < nparams || !stated || *stated + nparams != cnstr_binders)
                throw kernel_exception(*this, sstream() << "the certificate does not state a rule for '"
                                                        << constructor_name(c) << "' with its field count");
            unsigned nfields = cnstr_binders - nparams;
            realises(constructor_name(c), ind_d.get_lparams(), constructor_type(c));
            new_env.check_name(constructor_name(c));
            new_env.add_core(constant_info(constructor_val(constructor_name(c), ind_d.get_lparams(),
                                                           constructor_type(c), ind_type.get_name(), cidx,
                                                           nparams, nfields, ind_d.is_unsafe())));
            cidx++;
        }
    }
    for (derived_rec const & dr : cert.m_recs) {
        unsigned nmotives = 0, nminors = 0, nindices = 0;
        if (!derive_rec_arities_core(new_env, dr.m_type, nparams, nmotives, nminors, nindices))
            throw kernel_exception(new_env, sstream() << "the certificate's type for '" << dr.m_name
                                                      << "' does not read as a recursor of this declaration");
        realises(dr.m_name, dr.m_lparams, dr.m_type);
        new_env.check_name(dr.m_name);
        /* Never K-like, and not worth taking anyone's word for: K needs a non-mutual single-constructor
           zero-field `Prop`, a nested occurrence needs a field to sit in, and the model this is derived
           from always has the declaration's types plus at least one copy. Were it wrongly set, `rec`
           would reduce without looking at the major premise. */
        new_env.add_core(constant_info(recursor_val(dr.m_name, dr.m_lparams, dr.m_type, all_ind_names,
                                                    nparams, nindices, nmotives, nminors, dr.m_rules,
                                                    false, ind_d.is_unsafe())));
    }
    /* likewise its rules cannot be proved: a theorem may not mention an unsafe constant */
    if (!ind_d.is_unsafe())
        check_nested_rules(new_env, head(all_ind_names), cert);
    return diag.update(new_env);
}

static expr * g_nat_zero       = nullptr;
static expr * g_nat_succ       = nullptr;
static expr * g_string_mk      = nullptr;
static expr * g_list_cons_char = nullptr;
static expr * g_list_nil_char  = nullptr;
static expr * g_char_of_nat    = nullptr;

expr nat_lit_to_constructor(expr const & e) {
    lean_assert(is_nat_lit(e));
    nat const & v = lit_value(e).get_nat();
    if (v == 0u)
        return *g_nat_zero;
    else
        return mk_app(*g_nat_succ, mk_lit(literal(v - nat(1))));
}

expr string_lit_to_constructor(expr const & e) {
    lean_assert(is_string_lit(e));
    string_ref const & s = lit_value(e).get_string();
    std::vector<unsigned> cs;
    utf8_decode(s.to_std_string(), cs);
    expr r = *g_list_nil_char;
    unsigned i = cs.size();
    while (i > 0) {
        i--;
        r = mk_app(*g_list_cons_char, mk_app(*g_char_of_nat, mk_lit(literal(cs[i]))), r);
    }
    return mk_app(*g_string_mk, r);
}


void initialize_inductive() {
    g_ind_fresh      = new name("_ind_fresh");
    mark_persistent(g_ind_fresh->raw());
    g_nat_zero       = new expr(mk_constant(name{"Nat", "zero"}));
    mark_persistent(g_nat_zero->raw());
    g_nat_succ       = new expr(mk_constant(name{"Nat", "succ"}));
    mark_persistent(g_nat_succ->raw());
    g_string_mk      = new expr(mk_constant(name{"String", "ofList"}));
    mark_persistent(g_string_mk->raw());
    expr char_type   = mk_constant(name{"Char"});
    g_list_cons_char = new expr(mk_app(mk_constant(name{"List", "cons"}, {level()}), char_type));
    mark_persistent(g_list_cons_char->raw());
    g_list_nil_char  = new expr(mk_app(mk_constant(name{"List", "nil"}, {level()}), char_type));
    mark_persistent(g_list_nil_char->raw());
    g_char_of_nat    = new expr(mk_constant(name{"Char", "ofNat"}));
    mark_persistent(g_char_of_nat->raw());
    register_name_generator_prefix(*g_ind_fresh);
}

void finalize_inductive() {
    delete g_ind_fresh;
    delete g_nat_succ;
    delete g_nat_zero;
    delete g_string_mk;
    delete g_list_cons_char;
    delete g_list_nil_char;
}
}
