/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <unordered_map>
#include "kernel/environment.h"
#include "library/relation_manager.h"
#include "library/io_state.h"
#include "library/reducible.h"
#include "library/type_context.h"

namespace lean {
class app_builder_cache {
    struct entry {
        unsigned             m_num_umeta;
        unsigned             m_num_emeta;
        expr                 m_app;
        list<optional<expr>> m_inst_args; // "mask" of implicit instance arguments
        list<expr>           m_expl_args; // metavars for explicit arguments
        /*
          IMPORTANT: for m_inst_args we store the arguments in reverse order.
          For example, the first element in the list indicates whether the last argument
          is an instance implicit argument or not. If it is not none, then the element
          is the associated metavariable

          m_expl_args are also stored in reverse order
        */
    };

    struct key {
        name       m_name;
        unsigned   m_num_expl;
        unsigned   m_hash;
        // If nil, then the mask is composed of the last m_num_expl arguments.
        // If nonnil, then the mask is NOT of the form [false*, true*]
        list<bool> m_mask;

        key(name const & c, unsigned n);
        key(name const & c, list<bool> const & m);
        bool check_invariant() const;
        unsigned hash() const { return m_hash; }
        friend bool operator==(key const & k1, key const & k2) {
            return k1.m_name == k2.m_name && k1.m_num_expl == k2.m_num_expl && k1.m_mask == k2.m_mask;
        }
    };

    struct key_hash_fn {
        unsigned operator()(key const & k) const { return k.hash(); }
    };

    typedef std::unordered_map<key, entry, key_hash_fn> map;

    environment          m_env;
    map                  m_map;
    relation_info_getter m_rel_getter;
    refl_info_getter     m_refl_getter;
    symm_info_getter     m_symm_getter;
    trans_info_getter    m_trans_getter;
    friend class app_builder;
public:
    app_builder_cache(environment const & env);
    environment const & env() const { return m_env; }
};

class app_builder_exception : public exception {
public:
    // We may provide more information in the future.
    app_builder_exception():exception("app_builder_exception, more information can be obtained using commad `set_option trace.app_builder true`") {}
};

/** \brief Helper for creating simple applications where some arguments are inferred using
    type inference.

    Example, given
        rel.{l_1 l_2} : Pi (A : Type.{l_1}) (B : A -> Type.{l_2}), (Pi x : A, B x) -> (Pi x : A, B x) -> , Prop
        nat     : Type.{1}
        real    : Type.{1}
        vec.{l} : Pi (A : Type.{l}) (n : nat), Type.{l1}
        f g     : Pi (n : nat), vec real n
    then
        builder.mk_app(rel, f, g)
    returns the application
        rel.{1 2} nat (fun n : nat, vec real n) f g
*/
class app_builder {
    type_context &      m_ctx;
    app_builder_cache & m_cache;
    typedef app_builder_cache::key   key;
    typedef app_builder_cache::entry entry;

    levels mk_metavars(declaration const & d, buffer<expr> & mvars, buffer<optional<expr>> & inst_args);
    optional<entry> get_entry(name const & c, unsigned nargs);
    levels mk_metavars(declaration const & d, unsigned arity, buffer<expr> & mvars, buffer<optional<expr>> & inst_args);
    optional<entry> get_entry(name const & c, unsigned mask_sz, bool const * mask);
    bool check_all_assigned(entry const & e);
    void init_ctx_for(entry const & e);
    void trace_unify_failure(name const & n, unsigned i, expr const & m, expr const & v);
    level get_level(expr const & A);

public:
    app_builder(type_context & ctx, app_builder_cache & cache):m_ctx(ctx), m_cache(cache) {}
    /** \brief Create an application (d.{_ ... _} _ ... _ args[0] ... args[nargs-1]).
        The missing arguments and universes levels are inferred using type inference.

        \remark The method throwns an app_builder_exception if: not all arguments can be inferred;
        or constraints are created during type inference; or an exception is thrown
        during type inference.

        \remark This methods uses just higher-order pattern matching.
    */
    expr mk_app(name const & c, unsigned nargs, expr const * args);

    expr mk_app(name const & c, std::initializer_list<expr> const & args) {
        return mk_app(c, args.size(), args.begin());
    }

    expr mk_app(name const & c, expr const & a1) {
        return mk_app(c, {a1});
    }

    expr mk_app(name const & c, expr const & a1, expr const & a2) {
        return mk_app(c, {a1, a2});
    }

    expr mk_app(name const & c, expr const & a1, expr const & a2, expr const & a3) {
        return mk_app(c, {a1, a2, a3});
    }

    expr mk_app(name const & c, unsigned mask_sz, bool const * mask, expr const * args);

    /** \brief Shortcut for mk_app(c, total_nargs, mask, expl_nargs), where
        \c mask starts with total_nargs - expl_nargs false's followed by expl_nargs true's
        \pre total_nargs >= expl_nargs */
    expr mk_app(name const & c, unsigned total_nargs, unsigned expl_nargs, expr const * expl_args);

    expr mk_app(name const & c, unsigned total_nargs, std::initializer_list<expr> const & args) {
        return mk_app(c, total_nargs, args.size(), args.begin());
    }

    expr mk_app(name const & c, unsigned total_nargs, expr const & a1) {
        return mk_app(c, total_nargs, {a1});
    }

    expr mk_app(name const & c, unsigned total_nargs, expr const & a1, expr const & a2) {
        return mk_app(c, total_nargs, {a1, a2});
    }

    expr mk_app(name const & c, unsigned total_nargs, expr const & a1, expr const & a2, expr const & a3) {
        return mk_app(c, total_nargs, {a1, a2, a3});
    }

    /** \brief Similar to mk_app(n, lhs, rhs), but handles eq and iff more efficiently. */
    expr mk_rel(name const & n, expr const & lhs, expr const & rhs);
    expr mk_eq(expr const & lhs, expr const & rhs);
    expr mk_iff(expr const & lhs, expr const & rhs);
    expr mk_heq(expr const & lhs, expr const & rhs);

    /** \brief Similar a reflexivity proof for the given relation */
    expr mk_refl(name const & relname, expr const & a);
    expr mk_eq_refl(expr const & a);
    expr mk_iff_refl(expr const & a);
    expr mk_heq_refl(expr const & a);

    /** \brief Similar a symmetry proof for the given relation */
    expr mk_symm(name const & relname, expr const & H);
    expr mk_eq_symm(expr const & H);
    expr mk_iff_symm(expr const & H);
    expr mk_heq_symm(expr const & H);

    /** \brief Similar a transitivity proof for the given relation */
    expr mk_trans(name const & relname, expr const & H1, expr const & H2);
    expr mk_eq_trans(expr const & H1, expr const & H2);
    expr mk_iff_trans(expr const & H1, expr const & H2);
    expr mk_heq_trans(expr const & H1, expr const & H2);

    /** \brief Create a (non-dependent) eq.rec application.
        C is the motive. The expected types for C, H1 and H2 are
             C : A -> Type
             H1 : C a
             H2 : a = b
        The resultant application is
             @eq.rec A a C H1 b H2
        In the HoTT library, we actually create an eq.nrec application
        since eq.rec is a dependent eliminator in HoTT. */
    expr mk_eq_rec(expr const & C, expr const & H1, expr const & H2);

    /** \brief Create a (dependent) eq.drec application.
        C is the motive. The expected types for C, H1 and H2 are
             C : Pi (x : A), a = x -> Type
             H1 : C a (eq.refl a)
             H2 : a = b
        The resultant application is
             @eq.drec A a C H1 b H2
        In the HoTT library, we actually create an eq.rec application
        because eq.rec is a dependent eliminator in HoTT. */
    expr mk_eq_drec(expr const & C, expr const & H1, expr const & H2);

    expr mk_eq_of_heq(expr const & H);
    expr mk_heq_of_eq(expr const & H);

    expr mk_congr_arg(expr const & f, expr const & H);
    expr mk_congr_fun(expr const & H, expr const & a);
    expr mk_congr(expr const & H1, expr const & H2);

    /** \brief Given a reflexive relation R, and a proof H : a = b,
        build a proof for (R a b) */
    expr lift_from_eq(name const & R, expr const & H);

    /** \brief not p -> (p <-> false) */
    expr mk_iff_false_intro(expr const & H);
    /** \brief p -> (p <-> true) */
    expr mk_iff_true_intro(expr const & H);
    /** \brief (p <-> false) -> not p */
    expr mk_not_of_iff_false(expr const & H);
    /** \brief (p <-> true) -> p */
    expr mk_of_iff_true(expr const & H);
    /** \brief (true <-> false) -> false */
    expr mk_false_of_true_iff_false(expr const & H);

    expr mk_not(expr const & H);

    expr mk_partial_add(expr const & A);
    expr mk_partial_mul(expr const & A);
    expr mk_zero(expr const & A);
    expr mk_one(expr const & A);
    expr mk_partial_left_distrib(expr const & A);
    expr mk_partial_right_distrib(expr const & A);

    /** \brief Create (@sorry type) */
    expr mk_sorry(expr const & type);

    /** \brief False elimination */
    expr mk_false_rec(expr const & c, expr const & H);

    /** \brief Set the local instances. This method is relevant when we want to expose local class instances
        to the app_builder.

        \remark When the constructor app_builder(tmp_type_context & ctx) is used
        the initialization can be performed outside. */
    void set_local_instances(list<expr> const & insts);
};
void initialize_app_builder();
void finalize_app_builder();
}
