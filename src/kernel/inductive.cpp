/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/sstream.h"
#include "util/name_generator.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/find_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/kernel_exception.h"

namespace lean {
static name * g_ind_fresh = nullptr;

/**\ brief Return recursor name for the given inductive datatype name */
name mk_rec_name(name const & I) {
    return I + name("rec");
}

/* Auxiliary class for adding a mutual inductive datatype declaration.

   \remak It does not support nested inductive datatypes. The helper
   class elim_nested_inductive_fn should be used as a preprocessing step. */
class add_inductive_fn {
    environment            m_env;
    name_generator         m_ngen;
    local_ctx              m_lctx;
    level_param_names      m_lparams;
    unsigned               m_nparams;
    bool                   m_is_meta;
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
    add_inductive_fn(environment const & env, inductive_decl const & decl):
        m_env(env), m_ngen(*g_ind_fresh), m_lparams(decl.get_lparams()), m_is_meta(decl.is_meta()) {
        if (!decl.get_nparams().is_small())
            throw kernel_exception(env, "invalid inductive datatype, number of parameters is too big");
        m_nparams = decl.get_nparams().get_small_value();
        to_buffer(decl.get_types(), m_ind_types);
    }

    type_checker tc(local_ctx const & lctx = local_ctx()) { return type_checker(m_env, lctx, true, !m_is_meta); }

    /** Return type of the parameter at position `i` */
    expr get_param_type(unsigned i) const {
        return m_lctx.get_local_decl(m_params[i]).get_type();
    }

    expr mk_local_decl(local_ctx & lctx, name const & n, expr const & t, binder_info const & bi = binder_info()) {
        return lctx.mk_local_decl(m_ngen, n, t, bi);
    }

    expr mk_local_decl_for(local_ctx & lctx, expr const & t) {
        lean_assert(is_pi(t));
        return lctx.mk_local_decl(m_ngen, binding_name(t), binding_domain(t), binding_info(t));
    }

    expr whnf(local_ctx const & lctx, expr const & t) { return tc(lctx).whnf(t); }

    expr infer_type(local_ctx const & lctx, expr const & t) { return tc(lctx).infer(t); }

    bool is_def_eq(local_ctx const & lctx, expr const & t1, expr const & t2) { return tc(lctx).is_def_eq(t1, t2); }

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
        m_levels   = param_names_to_levels(m_lparams);
        bool first = true;
        for (inductive_type const & ind_type : m_ind_types) {
            expr type = ind_type.get_type();
            m_env.check_name(ind_type.get_name());
            m_env.check_name(mk_rec_name(ind_type.get_name()));
            check_no_metavar_no_fvar(m_env, ind_type.get_name(), type);
            tc().check(type, m_lparams);
            m_nindices.push_back(0);
            unsigned i = 0;
            while (is_pi(type)) {
                if (i < m_nparams) {
                    if (first) {
                        expr param = mk_local_decl_for(m_lctx, type);
                        m_params.push_back(param);
                        type = instantiate(binding_body(type), param);
                    } else {
                        if (!is_def_eq(m_lctx, binding_domain(type), get_param_type(i)))
                            throw kernel_exception(m_env, "parameters of all inductive datatypes must match");
                        type = instantiate(binding_body(type), m_params[i]);
                    }
                    i++;
                } else {
                    type = binding_body(type);
                    m_nindices.back()++;
                }
            }
            if (i != m_nparams)
                throw kernel_exception(m_env, "number of parameters mismatch in inductive datatype declaration");

            type = tc(m_lctx).ensure_sort(type);

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

    /** Return list with the names of all inductive datatypes in the mutual declaration. */
    names get_all_names() const {
        buffer<name> all_names;
        for (inductive_type const & ind_type : m_ind_types) {
            all_names.push_back(ind_type.get_name());
        }
        return names(all_names);
    }

    /** \brief Add all datatype declarations to environment. */
    void declare_inductive_types() {
        bool rec  = is_rec();
        names all = get_all_names();
        for (unsigned idx = 0; idx < m_ind_types.size(); idx++) {
            inductive_type const & ind_type = m_ind_types[idx];
            name const & n = ind_type.get_name();
            buffer<name> cnstr_names;
            for (constructor const & cnstr : ind_type.get_cnstrs()) {
                cnstr_names.push_back(constructor_name(cnstr));
            }
            m_env.add_core(constant_info(inductive_val(n, m_lparams, ind_type.get_type(), m_nparams, m_nindices[idx],
                                                       all, names(cnstr_names), rec, m_is_meta)));
        }
    }

    /** \brief Return true iff `t` is a term of the form `I As t`
        where `I` is the inductive datatype at position `i` being declared and
        `As` are the global parameters of this declaration. */
    bool is_valid_ind_app(expr const & t, unsigned i) {
        buffer<expr> args;
        expr I = get_app_args(t, args);
        if (I != m_ind_cnsts[i] || args.size() != m_nparams + m_nindices[i])
            return false;
        for (unsigned i = 0; i < m_nparams; i++) {
            if (m_params[i] != args[i])
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
    optional<unsigned> is_rec_argument(local_ctx lctx, expr t) {
        t = whnf(lctx, t);
        while (is_pi(t)) {
            expr local = mk_local_decl_for(lctx, t);
            t = whnf(lctx, instantiate(binding_body(t), local));
        }
        return is_valid_ind_app(t);
    }

    /** \brief Check if \c t contains only positive occurrences of the inductive datatypes being declared. */
    void check_positivity(local_ctx lctx, expr t, name const & cnstr_name, int arg_idx) {
        t = whnf(lctx, t);
        if (!has_ind_occ(t)) {
            // nonrecursive argument
        } else if (is_pi(t)) {
            if (has_ind_occ(binding_domain(t)))
                throw kernel_exception(m_env, sstream() << "arg #" << (arg_idx + 1) << " of '" << cnstr_name << "' "
                                       "has a non positive occurrence of the datatypes being declared");
            expr local = mk_local_decl_for(lctx, t);
            check_positivity(lctx, instantiate(binding_body(t), local), cnstr_name, arg_idx);
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
            for (constructor const & cnstr : ind_type.get_cnstrs()) {
                name const & n = constructor_name(cnstr);
                expr t = constructor_type(cnstr);
                m_env.check_name(n);
                check_no_metavar_no_fvar(m_env, n, t);
                tc().check(t, m_lparams);
                unsigned i = 0;
                local_ctx lctx = m_lctx;
                while (is_pi(t)) {
                    if (i < m_nparams) {
                        if (!is_def_eq(lctx, binding_domain(t), get_param_type(i)))
                            throw kernel_exception(m_env, sstream() << "arg #" << (i + 1) << " of '" << n << "' "
                                                   << "does not match inductive datatypes parameters'");
                        t = instantiate(binding_body(t), m_params[i]);
                    } else {
                        expr s = tc(lctx).ensure_type(binding_domain(t));
                        // the sort is ok IF
                        //   1- its level is <= inductive datatype level, OR
                        //   2- is an inductive predicate
                        if (!is_geq(m_result_level, sort_level(s)) || is_zero(m_result_level)) {
                            throw kernel_exception(m_env, sstream() << "universe level of type_of(arg #" << (i + 1) << ") "
                                                   << "of '" << n << "' is too big for the corresponding inductive datatype");
                        }
                        if (!m_is_meta)
                            check_positivity(lctx, binding_domain(t), n, i);
                        expr local = mk_local_decl_for(lctx, t);
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
            for (constructor const & cnstr : ind_type.get_cnstrs()) {
                name const & n = constructor_name(cnstr);
                expr const & t = constructor_type(cnstr);
                m_env.add_core(constant_info(constructor_val(n, m_lparams, t, ind_type.get_name(), m_nparams, m_is_meta)));
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
        local_ctx lctx;
        while (is_pi(type)) {
            expr fvar = mk_local_decl_for(lctx, type);
            if (i >= m_nparams) {
                expr s = tc(lctx).ensure_type(binding_domain(type));
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
        /* First, populate the fields, m_C, m_indices, m_lctx, m_major */
        for (inductive_type const & ind_type : m_ind_types) {
            rec_info info;
            expr t      = ind_type.get_type();
            unsigned i  = 0;
            while (is_pi(t)) {
                if (i < m_nparams) {
                    t = instantiate(binding_body(t), m_params[i]);
                } else {
                    expr idx = mk_local_decl_for(m_lctx, t);
                    info.m_indices.push_back(idx);
                    t = instantiate(binding_body(t), idx);
                }
                i++;
            }
            info.m_major = mk_local_decl(m_lctx, "t",
                                         mk_app(mk_app(m_ind_cnsts[d_idx], m_params), info.m_indices));
            expr C_ty = mk_sort(m_elim_level);
            C_ty      = m_lctx.mk_pi(info.m_major, C_ty);
            C_ty      = m_lctx.mk_pi(info.m_indices, C_ty);
            name C_name("C");
            if (m_ind_types.size() > 1)
                C_name = name(C_name).append_after(d_idx+1);
            info.m_C = mk_local_decl(m_lctx, C_name, C_ty);
            m_rec_infos.push_back(info);
            d_idx++;
        }
        /* First, populate the field m_minors */
        unsigned minor_idx = 1;
        d_idx = 0;
        for (inductive_type const & ind_type : m_ind_types) {
            for (constructor const & cnstr : ind_type.get_cnstrs()) {
                buffer<expr> b_u; // nonrec and rec args;
                buffer<expr> u;   // rec args
                buffer<expr> v;   // inductive args
                expr t     = constructor_type(cnstr);
                unsigned i = 0;
                while (is_pi(t)) {
                    if (i < m_nparams) {
                        t = instantiate(binding_body(t), m_params[i]);
                    } else {
                        expr l = mk_local_decl_for(m_lctx, t);
                        b_u.push_back(l);
                        if (is_rec_argument(m_lctx, binding_domain(t)))
                            u.push_back(l);
                        t = instantiate(binding_body(t), l);
                    }
                    i++;
                }
                buffer<expr> it_indices;
                unsigned it_idx = get_I_indices(t, it_indices);
                expr C_app      = mk_app(m_rec_infos[it_idx].m_C, it_indices);
                expr intro_app  = mk_app(mk_app(mk_constant(constructor_name(cnstr), m_levels), m_params), b_u);
                C_app = mk_app(C_app, intro_app);
                /* populate v using u */
                for (unsigned i = 0; i < u.size(); i++) {
                    expr u_i    = u[i];
                    expr u_i_ty = whnf(m_lctx, infer_type(m_lctx, u_i));
                    buffer<expr> xs;
                    while (is_pi(u_i_ty)) {
                        expr x = mk_local_decl_for(m_lctx, u_i_ty);
                        xs.push_back(x);
                        u_i_ty = whnf(m_lctx, instantiate(binding_body(u_i_ty), x));
                    }
                    buffer<expr> it_indices;
                    unsigned it_idx = get_I_indices(u_i_ty, it_indices);
                    expr C_app  = mk_app(m_rec_infos[it_idx].m_C, it_indices);
                    expr u_app  = mk_app(u_i, xs);
                    C_app = mk_app(C_app, u_app);
                    expr v_i_ty = m_lctx.mk_pi(xs, C_app);
                    expr v_i    = mk_local_decl(m_lctx, name("v").append_after(i), v_i_ty, binder_info());
                    v.push_back(v_i);
                }
                expr minor_ty = m_lctx.mk_pi(b_u, m_lctx.mk_pi(v, C_app));
                expr minor    = mk_local_decl(m_lctx, name("m").append_after(minor_idx), minor_ty);
                m_rec_infos[d_idx].m_minors.push_back(minor);
                minor_idx++;
            }
            d_idx++;
        }
    }

    /** \brief Return the levels for the recursor. */
    levels get_rec_level_params() {
        if (is_param(m_elim_level))
            return levels(m_elim_level, m_levels);
        else
            return m_levels;
    }

    /** \brief Return the level parameter names for the recursor. */
    names get_rec_level_param_names() {
        if (is_param(m_elim_level))
            return level_param_names(param_id(m_elim_level), m_lparams);
        else
            return m_lparams;
    }

    /** \brief Declare recursors. */
    void declare_recursors() {
        names all = get_all_names();
        for (unsigned d_idx = 0; d_idx < m_ind_types.size(); d_idx++) {
            rec_info const & info = m_rec_infos[d_idx];
            expr C_app            = mk_app(mk_app(info.m_C, info.m_indices), info.m_major);
            expr rec_ty           = m_lctx.mk_pi(info.m_major, C_app);
            rec_ty                = m_lctx.mk_pi(info.m_indices, rec_ty);
            /* Add minor premises */
            unsigned nminors = 0;
            unsigned i = m_ind_types.size();
            while (i > 0) {
                --i;
                unsigned j = m_rec_infos[i].m_minors.size();
                while (j > 0) {
                    --j;
                    rec_ty = m_lctx.mk_pi(m_rec_infos[i].m_minors[j], rec_ty);
                    nminors++;
                }
            }
            /* Add type formers (aka motives) */
            unsigned nmotives = 0;
            i = m_ind_types.size();
            while (i > 0) {
                --i;
                rec_ty = m_lctx.mk_pi(m_rec_infos[i].m_C, rec_ty);
                nmotives++;
            }
            rec_ty   = m_lctx.mk_pi(m_params, rec_ty);
            rec_ty   = infer_implicit(rec_ty, true /* strict */);
            /*
               TODO(Leo): gen reduction rule
            */
            recursor_rules rules;
            name rec_name     = mk_rec_name(m_ind_types[d_idx].get_name());
            names rec_lparams = get_rec_level_param_names();
            m_env.add_core(constant_info(recursor_val(rec_name, rec_lparams, rec_ty, all,
                                                      m_nparams, m_nindices[d_idx], nmotives, nminors,
                                                      rules, m_K_target, m_is_meta)));
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

/* Eliminate nested inductive datatypes by creating a new (auxiliary) declaration which contains and inductive types in `d`
   and copies of the nested inductive datatypes used in `d`. For each nested occurrence `I Ds is` where `I` is a nested inductive
   datatype and `Ds` are the parametric arguments and `is` the indices, we create an auxiliary type `Iaux` in the (mutual) inductive
   declaration `d`, and replace `I Ds is` with `Iaux As is` where `As` are `d`'s parameters.
   Moreover, we add the pair `(I Ds, Iaux)` to `nested_aux`.

   Note that, `As` and `Ds` may have a different sizes. */
struct elim_nested_inductive_fn {
    environment const &        m_env;
    declaration const &        m_d;
    buffer<pair<expr, name>> & m_nested_aux;
    levels                     m_lvls;
    buffer<inductive_type>     m_new_types;
    unsigned                   m_next_idx{1};

    elim_nested_inductive_fn(environment const & env, declaration const & d, buffer<pair<expr, name>> & nested_aux):
        m_env(env), m_d(d), m_nested_aux(nested_aux) {
        m_lvls = param_names_to_levels(inductive_decl(m_d).get_lparams());
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
        nat const & nparams = info->to_inductive_val().get_nparams();
        if (nparams > args.size()) return optional<inductive_val>();
        bool is_nested   = false;
        bool loose_bvars = false;
        for (unsigned i = 0; i < nparams.get_small_value(); i++) {
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
        unsigned I_nparams = I_val->get_nparams().get_small_value();
        expr IAs = mk_app(fn, I_nparams, args.data()); /* `I As` */
        /* Check whether we have already created an auxiliary inductive_type for `I As` */
        optional<name> auxI_name;
        for (pair<expr, name> const & p : m_nested_aux) {
            if (p.first == IAs) {
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
                expr auxJ_type       = instantiate_univ_params(J_info.get_type(), J_info.get_univ_params(), I_lvls);
                auxJ_type            = instantiate_pi_params(auxJ_type, I_nparams, args.data());
                auxJ_type            = lctx.mk_pi(As, auxJ_type);
                m_nested_aux.push_back(mk_pair(JAs, auxJ_name));
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
                    expr auxJ_cnstr_type    = instantiate_univ_params(J_cnstr_info.get_type(), J_cnstr_info.get_univ_params(), I_lvls);
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

    declaration operator()() {
        inductive_decl ind_d(m_d);
        if (!ind_d.get_nparams().is_small()) throw_ill_formed();
        unsigned d_nparams = ind_d.get_nparams().get_small_value();
        to_buffer(ind_d.get_types(), m_new_types);
        if (m_new_types.size() == 0) throw kernel_exception(m_env, "invalid empty (mutual) inductive datatype declaration, it must contain at least one inductive type.");
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
                for (unsigned i = 0; i < d_nparams; i++) {
                    if (!is_pi(cnstr_type)) throw kernel_exception(m_env, "invalid inductive datatype declaration, incorrect number of parameters");
                    As.push_back(lctx.mk_local_decl(binding_name(cnstr_type), binding_domain(cnstr_type), binding_info(cnstr_type)));
                    cnstr_type = instantiate(binding_body(cnstr_type), As.back());
                }
                lean_assert(As.size() == d_nparams);
                expr new_cnstr_type = replace_all_nested(lctx, As, cnstr_type);
                new_cnstr_type = lctx.mk_pi(As, new_cnstr_type);
                new_cnstrs.push_back(constructor(constructor_name(cnstr), new_cnstr_type));
            }
            m_new_types[qhead] = inductive_type(ind_type.get_name(), ind_type.get_type(), constructors(new_cnstrs));
            qhead++;
        }
        return mk_inductive_decl(ind_d.get_lparams(), ind_d.get_nparams(), inductive_types(m_new_types), ind_d.is_meta());
    }
};

environment environment::add_inductive(declaration const & d) const {
    buffer<pair<expr, name>> nested_aux;
    declaration aux_d   = elim_nested_inductive_fn(*this, d, nested_aux)();
    environment aux_env = add_inductive_fn(*this, inductive_decl(aux_d))();
    // TODO(Leo): if `nested_aux` is not empty, we must create a new environment using `aux_env` and `aux_d`
    return aux_env;
}

void initialize_inductive() {
    g_nested    = new name("_nested");
    g_ind_fresh = new name("_ind_fresh");
}

void finalize_inductive() {
    delete g_nested;
    delete g_ind_fresh;
}
}
