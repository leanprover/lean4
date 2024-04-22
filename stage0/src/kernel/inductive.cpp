/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/sstream.h"
#include "runtime/utf8.h"
#include "util/name_generator.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/find_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/kernel_exception.h"

namespace lean {
static name * g_ind_fresh = nullptr;

/**\ brief Return recursor name for the given inductive datatype name */
name mk_rec_name(name const & I) {
    return I + name("rec");
}

/** \brief Return true if the given declaration is a structure */
bool is_structure_like(environment const & env, name const & decl_name) {
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

    bool                   m_is_nested;

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
    add_inductive_fn(environment const & env, inductive_decl const & decl, bool is_nested):
        m_env(env), m_ngen(*g_ind_fresh), m_lparams(decl.get_lparams()), m_is_unsafe(decl.is_unsafe()),
        m_is_nested(is_nested) {
        if (!decl.get_nparams().is_small())
            throw kernel_exception(env, "invalid inductive datatype, number of parameters is too big");
        m_nparams = decl.get_nparams().get_small_value();
        to_buffer(decl.get_types(), m_ind_types);
    }

    type_checker tc() { return type_checker(m_env, m_lctx, m_is_unsafe ? definition_safety::unsafe : definition_safety::safe); }

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
            m_env.add_core(constant_info(inductive_val(n, m_lparams, ind_type.get_type(), m_nparams, m_nindices[idx],
                                                       all, names(cnstr_names), rec, m_is_unsafe, reflexive, m_is_nested)));
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
                        if (!(is_geq(m_result_level, sort_level(s)) || is_zero(m_result_level))) {
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
                if (!is_zero(sort_level(s))) {
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
            is_zero(m_result_level) &&              /* It is an inductive predicate. */
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

static name * g_nested = nullptr;
static name * g_nested_fresh = nullptr;

/* Result produced by elim_nested_inductive_fn */
struct elim_nested_inductive_result {
    name_generator           m_ngen;
    buffer<expr>             m_params;
    name_map<expr>           m_aux2nested; /* mapping from auxiliary type to nested inductive type. */
    declaration              m_aux_decl;

    elim_nested_inductive_result(name_generator const & ngen, buffer<expr> const & params, buffer<pair<expr, name>> const & nested_aux, declaration const & d):
        m_ngen(ngen), m_params(params), m_aux_decl(d) {
        for (pair<expr, name> const & p : nested_aux) {
            m_aux2nested.insert(p.second, p.first);
        }
    }

    /* If `c` is an constructor name associated with an auxiliary inductive type, then return the
       nested inductive associated with it and the name of its inductive type. Return none. */
    optional<pair<expr, name>> get_nested_if_aux_constructor(environment const & aux_env, name const & c) const {
        optional<constant_info> info = aux_env.find(c);
        if (!info || !info->is_constructor()) return optional<pair<expr, name>>();
        name auxI_name = info->to_constructor_val().get_induct();
        expr const * nested = m_aux2nested.find(auxI_name);
        if (!nested) return optional<pair<expr, name>>();
        return optional<pair<expr, name>>(*nested, auxI_name);
    }

    name restore_constructor_name(environment const & aux_env, name const & cnstr_name) const {
        optional<pair<expr, name>> p = get_nested_if_aux_constructor(aux_env, cnstr_name);
        lean_assert(p);
        expr const & I = get_app_fn(p->first);
        lean_assert(is_constant(I));
        return cnstr_name.replace_prefix(p->second, const_name(I));
    }

    expr restore_nested(expr e, environment const & aux_env, name_map<name> const & aux_rec_name_map = name_map<name>()) {
        local_ctx lctx;
        buffer<expr> As;
        bool pi = is_pi(e);
        for (unsigned i = 0; i < m_params.size(); i++) {
            lean_assert(is_pi(e) || is_lambda(e));
            As.push_back(lctx.mk_local_decl(m_ngen, binding_name(e), binding_domain(e), binding_info(e)));
            e = instantiate(binding_body(e), As.back());
        }
        e = replace(e, [&](expr const & t, unsigned) {
                if (is_constant(t)) {
                    if (name const * rec_name = aux_rec_name_map.find(const_name(t))) {
                        return some_expr(mk_constant(*rec_name, const_levels(t)));
                    }
                }
                expr const & fn = get_app_fn(t);
                if (is_constant(fn)) {
                    if (expr const * nested = m_aux2nested.find(const_name(fn))) {
                        buffer<expr> args;
                        get_app_args(t, args);
                        lean_assert(args.size() >= m_params.size());
                        expr new_t = instantiate_rev(abstract(*nested, m_params.size(), m_params.data()), As.size(), As.data());
                        return some_expr(mk_app(new_t, args.size() - m_params.size(), args.data() + m_params.size()));
                    }
                    if (optional<pair<expr, name>> r = get_nested_if_aux_constructor(aux_env, const_name(fn))) {
                        expr nested    = r->first;
                        name auxI_name = r->second;
                        /* `t` is a constructor-application of an auxiliary inductive type */
                        buffer<expr> args;
                        get_app_args(t, args);
                        lean_assert(args.size() >= m_params.size());
                        expr new_nested = instantiate_rev(abstract(nested, m_params.size(), m_params.data()), As.size(), As.data());
                        buffer<expr> I_args;
                        expr I = get_app_args(new_nested, I_args);
                        lean_assert(is_constant(I));
                        name new_fn_name = const_name(fn).replace_prefix(auxI_name, const_name(I));
                        expr new_fn = mk_constant(new_fn_name, const_levels(I));
                        expr new_t  = mk_app(mk_app(new_fn, I_args), args.size() - m_params.size(), args.data() + m_params.size());
                        return some_expr(new_t);
                    }
                }
                return none_expr();
            });
        return pi ? lctx.mk_pi(As, e) : lctx.mk_lambda(As, e);
    }
};

/* Eliminate nested inductive datatypes by creating a new (auxiliary) declaration which contains and inductive types in `d`
   and copies of the nested inductive datatypes used in `d`. For each nested occurrence `I Ds is` where `I` is a nested inductive
   datatype and `Ds` are the parametric arguments and `is` the indices, we create an auxiliary type `Iaux` in the (mutual) inductive
   declaration `d`, and replace `I Ds is` with `Iaux As is` where `As` are `d`'s parameters.
   Moreover, we add the pair `(I Ds, Iaux)` to `nested_aux`.

   Note that, `As` and `Ds` may have a different sizes. */
struct elim_nested_inductive_fn {
    environment const &        m_env;
    declaration const &        m_d;
    name_generator             m_ngen;
    local_ctx                  m_params_lctx;
    buffer<expr>               m_params;
    buffer<pair<expr, name>>   m_nested_aux; /* The expressions stored here contains free vars in `m_params` */
    levels                     m_lvls;
    buffer<inductive_type>     m_new_types;
    unsigned                   m_next_idx{1};

    elim_nested_inductive_fn(environment const & env, declaration const & d):
        m_env(env), m_d(d), m_ngen(*g_nested_fresh) {
        m_lvls = lparams_to_levels(inductive_decl(m_d).get_lparams());
    }

    name mk_unique_name(name const & n) {
        while (true) {
            name r = n.append_after(m_next_idx);
            m_next_idx++;
            if (!m_env.find(r)) return r;
        }
    }

    void throw_ill_formed() {
        throw kernel_exception(m_env, "invalid nested inductive datatype, ill-formed declaration");
    }

    expr replace_params(expr const & e, buffer<expr> const & As) {
        lean_assert(m_params.size() == As.size());
        return instantiate_rev(abstract(e, As.size(), As.data()), m_params.size(), m_params.data());
    }

    /* IF `e` is of the form `I Ds is` where
          1) `I` is a nested inductive datatype (i.e., a previously declared inductive datatype),
          2) the parametric arguments `Ds` do not contain loose bound variables, and do contain inductive datatypes in `m_new_types`
       THEN return the `inductive_val` in the `constant_info` associated with `I`.
       Otherwise, return none. */
    optional<inductive_val> is_nested_inductive_app(expr const & e) {
        if (!is_app(e)) return optional<inductive_val>();
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn)) return optional<inductive_val>();
        optional<constant_info> info = m_env.find(const_name(fn));
        if (!info || !info->is_inductive()) return optional<inductive_val>();
        buffer<expr> args;
        get_app_args(e, args);
        unsigned nparams = info->to_inductive_val().get_nparams();
        if (nparams > args.size()) return optional<inductive_val>();
        bool is_nested   = false;
        bool loose_bvars = false;
        for (unsigned i = 0; i < nparams; i++) {
            if (has_loose_bvars(args[i])) {
                loose_bvars = true;
            }
            if (find(args[i], [&](expr const & t, unsigned) {
                        if (is_constant(t)) {
                            for (inductive_type const & ind_type : m_new_types) {
                                if (const_name(t) == ind_type.get_name())
                                    return true;
                            }
                        }
                        return false;
                    })) {
                is_nested = true;
            }
        }
        if (!is_nested) return optional<inductive_val>();
        if (loose_bvars)
            throw kernel_exception(m_env, sstream() << "invalid nested inductive datatype '" << const_name(fn) << "', nested inductive datatypes parameters cannot contain local variables.");
        return optional<inductive_val>(info->to_inductive_val());
    }

    expr instantiate_pi_params(expr e, unsigned nparams, expr const * params) {
        for (unsigned i = 0; i < nparams; i++) {
            if (!is_pi(e)) throw_ill_formed();
            e = binding_body(e);
        }
        return instantiate_rev(e, nparams, params);
    }

    /* If `e` is a nested occurrence `I Ds is`, return `Iaux As is` */
    optional<expr> replace_if_nested(local_ctx const & lctx, buffer<expr> const & As, expr const & e) {
        optional<inductive_val> I_val = is_nested_inductive_app(e);
        if (!I_val) return none_expr();
        /* `e` is of the form `I As is` where `As` are the parameters and `is` the indices */
        buffer<expr> args;
        expr const & fn       = get_app_args(e, args);
        name const & I_name   = const_name(fn);
        levels const & I_lvls = const_levels(fn);
        lean_assert(I_val->get_nparams() <= args.size());
        unsigned I_nparams = I_val->get_nparams();
        expr IAs = mk_app(fn, I_nparams, args.data()); /* `I As` */
        /* Check whether we have already created an auxiliary inductive_type for `I As` */
        optional<name> auxI_name;
        /* Replace `As` with `m_params` before searching at `m_nested_aux`.
           We need this step because we re-create parameters for each constructor with the correct binding info */
        expr Iparams = replace_params(IAs, As);
        for (pair<expr, name> const & p : m_nested_aux) {
            /* Remark: we could have used `is_def_eq` here instead of structural equality.
               It is probably not needed, but if one day we decide to do it, we have to populate
               an auxiliary environment with the inductive datatypes we are defining since `p.first` and `Iparams`
               contain references to them. */
            if (p.first == Iparams) {
                auxI_name = p.second;
                break;
            }
        }
        if (auxI_name) {
            expr auxI = mk_constant(*auxI_name, m_lvls);
            auxI      = mk_app(auxI, As);
            return some_expr(mk_app(auxI, args.size() - I_nparams, args.data() + I_nparams));
        } else {
            optional<expr> result;
            /* We should copy all inductive datatypes `J` in the mutual declaration containing `I` to
               the `m_new_types` mutual declaration as new auxiliary types. */
            for (name const & J_name : I_val->get_all()) {
                constant_info J_info = m_env.get(J_name);
                lean_assert(J_info.is_inductive());
                expr J               = mk_constant(J_name, I_lvls);
                expr JAs             = mk_app(J, I_nparams, args.data());
                name auxJ_name       = mk_unique_name(*g_nested + J_name);
                expr auxJ_type       = instantiate_lparams(J_info.get_type(), J_info.get_lparams(), I_lvls);
                auxJ_type            = instantiate_pi_params(auxJ_type, I_nparams, args.data());
                auxJ_type            = lctx.mk_pi(As, auxJ_type);
                m_nested_aux.push_back(mk_pair(replace_params(JAs, As), auxJ_name));
                if (J_name == I_name) {
                    /* Create result */
                    expr auxI = mk_constant(auxJ_name, m_lvls);
                    auxI      = mk_app(auxI, As);
                    result    = mk_app(auxI, args.size() - I_nparams, args.data() + I_nparams);
                }
                buffer<constructor> auxJ_constructors;
                for (name const & J_cnstr_name : J_info.to_inductive_val().get_cnstrs()) {
                    constant_info J_cnstr_info = m_env.get(J_cnstr_name);
                    name auxJ_cnstr_name = J_cnstr_name.replace_prefix(J_name, auxJ_name);
                    /* auxJ_cnstr_type still has references to `J`, this will be fixed later when we process it. */
                    expr auxJ_cnstr_type    = instantiate_lparams(J_cnstr_info.get_type(), J_cnstr_info.get_lparams(), I_lvls);
                    auxJ_cnstr_type         = instantiate_pi_params(auxJ_cnstr_type, I_nparams, args.data());
                    auxJ_cnstr_type         = lctx.mk_pi(As, auxJ_cnstr_type);
                    auxJ_constructors.push_back(constructor(auxJ_cnstr_name, auxJ_cnstr_type));
                }
                m_new_types.push_back(inductive_type(auxJ_name, auxJ_type, constructors(auxJ_constructors)));
            }
            lean_assert(result);
            return result;
        }
    }

    /* Replace all nested inductive datatype occurrences in `e`. */
    expr replace_all_nested(local_ctx const & lctx, buffer<expr> const & As, expr const & e) {
        return replace(e, [&](expr const & e, unsigned) { return replace_if_nested(lctx, As, e); });
    }

    expr get_params(expr type, unsigned nparams, local_ctx & lctx, buffer<expr> & params) {
        lean_assert(params.empty());
        for (unsigned i = 0; i < nparams; i++) {
            if (!is_pi(type)) throw kernel_exception(m_env, "invalid inductive datatype declaration, incorrect number of parameters");
            params.push_back(lctx.mk_local_decl(m_ngen, binding_name(type), binding_domain(type), binding_info(type)));
            type = instantiate(binding_body(type), params.back());
        }
        return type;
    }

    elim_nested_inductive_result operator()() {
        inductive_decl ind_d(m_d);
        if (!ind_d.get_nparams().is_small()) throw_ill_formed();
        unsigned d_nparams = ind_d.get_nparams().get_small_value();
        to_buffer(ind_d.get_types(), m_new_types);
        if (m_new_types.size() == 0) throw kernel_exception(m_env, "invalid empty (mutual) inductive datatype declaration, it must contain at least one inductive type.");
        /* initialize m_params and m_params_lctx */
        get_params(m_new_types[0].get_type(), d_nparams, m_params_lctx, m_params);
        unsigned qhead = 0;
        /* Main elimination loop. */
        while (qhead < m_new_types.size()) {
            inductive_type ind_type = m_new_types[qhead];
            buffer<constructor> new_cnstrs;
            for (constructor cnstr : ind_type.get_cnstrs()) {
                expr cnstr_type = constructor_type(cnstr);
                local_ctx lctx;
                buffer<expr> As;
                /* Consume parameters.

                   We (re-)create the parameters for each constructor because we want to preserve the binding_info. */
                cnstr_type = get_params(cnstr_type, d_nparams, lctx, As);
                lean_assert(As.size() == d_nparams);
                expr new_cnstr_type = replace_all_nested(lctx, As, cnstr_type);
                new_cnstr_type = lctx.mk_pi(As, new_cnstr_type);
                new_cnstrs.push_back(constructor(constructor_name(cnstr), new_cnstr_type));
            }
            m_new_types[qhead] = inductive_type(ind_type.get_name(), ind_type.get_type(), constructors(new_cnstrs));
            qhead++;
        }
        declaration aux_decl = mk_inductive_decl(ind_d.get_lparams(), ind_d.get_nparams(), inductive_types(m_new_types), ind_d.is_unsafe());
        return elim_nested_inductive_result(m_ngen, m_params, m_nested_aux, aux_decl);
    }
};

/* Given the auxiliary environment `aux_env` generated by processing the auxiliary mutual declaration,
   and the original declaration `d`. This function return a pair `(aux_rec_names, aux_rec_name_map)`
   where `aux_rec_names` contains the recursor names associated to auxiliary inductive types used to
   eliminated nested inductive occurrences.
   The mapping `aux_rec_name_map` contains an entry `(aux_rec_name -> rec_name)` for each
   element in `aux_rec_names`. It provides the new names for these recursors.

   We compute the new recursor names using the first inductive datatype in the original declaration `d`,
   and the suffice `.rec_<idx>`. */
static pair<names, name_map<name>> mk_aux_rec_name_map(environment const & aux_env, inductive_decl const & d) {
    unsigned ntypes = length(d.get_types());
    lean_assert(ntypes > 0);
    inductive_type const & main_type = head(d.get_types());
    name const & main_name  = main_type.get_name();
    constant_info main_info = aux_env.get(main_name);
    names const & all_names = main_info.to_inductive_val().get_all();
    /* This function is only called if we have created auxiliary inductive types when eliminating
       the nested inductives. */
    lean_assert(length(all_names) > ntypes);
    /* Remark: we use the `main_name` to declare the auxiliary recursors as: <main_name>.rec_1, <main_name>.rec_2, ...
       This is a little bit asymmetrical if `d` is a mutual declaration, but it makes sure we have simple names. */
    buffer<name>   old_rec_names;
    name_map<name> rec_map;
    unsigned i = 0;
    unsigned next_idx = 1;
    for (name const & ind_name : all_names) {
        if (i >= ntypes) {
            old_rec_names.push_back(mk_rec_name(ind_name));
            name new_rec_name = mk_rec_name(main_name).append_after(next_idx);
            next_idx++;
            rec_map.insert(old_rec_names.back(), new_rec_name);
        }
        i++;
    }
    return mk_pair(names(old_rec_names), rec_map);
}

environment environment::add_inductive(declaration const & d) const {
    elim_nested_inductive_result res = elim_nested_inductive_fn(*this, d)();
    bool is_nested = !res.m_aux2nested.empty();
    environment aux_env = add_inductive_fn(*this, inductive_decl(res.m_aux_decl), is_nested)();
    if (!is_nested) {
        /* `d` did not contain nested inductive types. */
        return aux_env;
    } else {
        /* Restore nested inductives. */
        inductive_decl ind_d(d);
        names all_ind_names = get_all_inductive_names(ind_d);
        names aux_rec_names; name_map<name> aux_rec_name_map;
        std::tie(aux_rec_names, aux_rec_name_map) = mk_aux_rec_name_map(aux_env, d);
        environment new_env = *this;
        auto process_rec = [&](name const & rec_name) {
            name new_rec_name      = rec_name;
            if (name const * new_name = aux_rec_name_map.find(rec_name))
                new_rec_name = *new_name;
            constant_info rec_info = aux_env.get(rec_name);
            expr new_rec_type      = res.restore_nested(rec_info.get_type(), aux_env, aux_rec_name_map);
            recursor_val rec_val   = rec_info.to_recursor_val();
            buffer<recursor_rule> new_rules;
            for (recursor_rule const & rule : rec_val.get_rules()) {
                expr new_rhs        = res.restore_nested(rule.get_rhs(), aux_env, aux_rec_name_map);
                name cnstr_name     = rule.get_cnstr();
                name new_cnstr_name = cnstr_name;
                if (new_rec_name != rec_name) {
                    /* We need to fix the constructor name */
                    new_cnstr_name  = res.restore_constructor_name(aux_env, cnstr_name);
                }
                new_rules.push_back(recursor_rule(new_cnstr_name, rule.get_nfields(), new_rhs));
            }
            new_env.check_name(new_rec_name);
            new_env.add_core(constant_info(recursor_val(new_rec_name, rec_info.get_lparams(), new_rec_type,
                                                        all_ind_names, rec_val.get_nparams(), rec_val.get_nindices(), rec_val.get_nmotives(),
                                                        rec_val.get_nminors(), recursor_rules(new_rules),
                                                        rec_val.is_k(), rec_val.is_unsafe())));
        };
        for (inductive_type const & ind_type : ind_d.get_types()) {
            constant_info ind_info = aux_env.get(ind_type.get_name());
            inductive_val ind_val  = ind_info.to_inductive_val();
            /* We just need to "fix" the `all` fields for ind_info.

               Remark: if we decide to store the recursor names, we will also need to fix it. */
            new_env.add_core(constant_info(inductive_val(ind_info.get_name(), ind_info.get_lparams(), ind_info.get_type(),
                                                         ind_val.get_nparams(), ind_val.get_nindices(),
                                                         all_ind_names, ind_val.get_cnstrs(),
                                                         ind_val.is_rec(), ind_val.is_unsafe(), ind_val.is_reflexive(), ind_val.is_nested())));
            for (name const & cnstr_name : ind_val.get_cnstrs()) {
                constant_info   cnstr_info = aux_env.get(cnstr_name);
                constructor_val cnstr_val  = cnstr_info.to_constructor_val();
                expr new_type = res.restore_nested(cnstr_info.get_type(), aux_env);
                new_env.add_core(constant_info(constructor_val(cnstr_info.get_name(), cnstr_info.get_lparams(), new_type,
                                                               cnstr_val.get_induct(), cnstr_val.get_cidx(), cnstr_val.get_nparams(),
                                                               cnstr_val.get_nfields(), cnstr_val.is_unsafe())));
            }
            process_rec(mk_rec_name(ind_type.get_name()));
        }
        for (name const & aux_rec : aux_rec_names) {
            process_rec(aux_rec);
        }
        return new_env;
    }
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
    g_nested         = new name("_nested");
    mark_persistent(g_nested->raw());
    g_ind_fresh      = new name("_ind_fresh");
    mark_persistent(g_ind_fresh->raw());
    g_nested_fresh   = new name("_nested_fresh");
    mark_persistent(g_nested_fresh->raw());
    g_nat_zero       = new expr(mk_constant(name{"Nat", "zero"}));
    mark_persistent(g_nat_zero->raw());
    g_nat_succ       = new expr(mk_constant(name{"Nat", "succ"}));
    mark_persistent(g_nat_succ->raw());
    g_string_mk      = new expr(mk_constant(name{"String", "mk"}));
    mark_persistent(g_string_mk->raw());
    expr char_type   = mk_constant(name{"Char"});
    g_list_cons_char = new expr(mk_app(mk_constant(name{"List", "cons"}, {level()}), char_type));
    mark_persistent(g_list_cons_char->raw());
    g_list_nil_char  = new expr(mk_app(mk_constant(name{"List", "nil"}, {level()}), char_type));
    mark_persistent(g_list_nil_char->raw());
    g_char_of_nat    = new expr(mk_constant(name{"Char", "ofNat"}));
    mark_persistent(g_char_of_nat->raw());
    register_name_generator_prefix(*g_ind_fresh);
    register_name_generator_prefix(*g_nested_fresh);
}

void finalize_inductive() {
    delete g_nested;
    delete g_ind_fresh;
    delete g_nested_fresh;
    delete g_nat_succ;
    delete g_nat_zero;
    delete g_string_mk;
    delete g_list_cons_char;
    delete g_list_nil_char;
}
}
