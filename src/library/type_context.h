/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <algorithm>
#include <lean/flet.h>
#include "util/lbool.h"
#include "util/fresh_name.h"
#include "kernel/environment.h"
#include "library/projection.h"
#include "library/abstract_type_context.h"
#include "library/exception.h"
#include "library/expr_pair.h"

namespace lean {
enum class transparency_mode { All = 0, Semireducible, Reducible };

/* Return `f._sunfold` */
name mk_smart_unfolding_name_for(name const & f);

class class_exception : public generic_exception {
public:
    class_exception(expr const & m, char const * msg):generic_exception(m, msg) {}
};

bool is_at_least_semireducible(transparency_mode m);
bool is_at_least_instances(transparency_mode m);

transparency_mode ensure_semireducible_mode(transparency_mode m);

/* Approximation configuration object. */
struct unifier_config {
    bool m_fo_approx{false};
    bool m_ctx_approx{false};
    bool m_quasi_pattern_approx{false};
    bool m_const_approx{false};

    unifier_config() {}
    unifier_config(bool fo_approx, bool ctx_approx, bool qp_approx):
        m_fo_approx(fo_approx), m_ctx_approx(ctx_approx), m_quasi_pattern_approx(qp_approx) {}
};

class type_context_old : public abstract_type_context {
    typedef buffer<optional<level>> tmp_uassignment;
    typedef buffer<expr>            tmp_etype;
    typedef buffer<optional<expr>>  tmp_eassignment;
    enum class tmp_trail_kind { Level, Expr };
    typedef buffer<pair<tmp_trail_kind, unsigned>> tmp_trail;
    friend struct instance_synthesizer;
private:
    environment        m_env;
    /* We only cache results when m_used_assignment is false */
    bool               m_used_assignment{false};
    transparency_mode  m_transparency_mode;
    /* m_in_is_def_eq is a temporary flag set to true in the beginning of is_def_eq. */
    bool               m_in_is_def_eq{false};
    /* m_is_def_eq_depth is only used for tracing purposes */
    unsigned           m_is_def_eq_depth{0};
    /* Stack of backtracking point (aka scope) */
    /* Higher-order unification approximation options.

       Modules that use approximations:
       - elaborator
       - apply and rewrite tactics use it by default (it can be disabled). */
    unifier_config     m_unifier_cfg;

    /* If m_update_left, then when processing `is_def_eq(t, s)`, metavariables
       occurring in `t` can be assigned. */
    bool               m_update_left{true};
    /* If m_update_right, then when processing `is_def_eq(t, s)`, metavariables
       occurring in `t` can be assigned. */
    bool               m_update_right{true};

    bool               m_smart_unfolding{true};
    unsigned           m_unfold_depth{0}; // used in tracing messages

    /* Auxiliary object used to temporarily swap `m_update_left` and `m_update_right`.
       We use it before invoking methods where we swap left/right. */
    struct swap_update_flags_scope {
        type_context_old & m_ctx;
        swap_update_flags_scope(type_context_old & ctx):m_ctx(ctx) {
            std::swap(m_ctx.m_update_left, m_ctx.m_update_right);
        }
        ~swap_update_flags_scope() {
            std::swap(m_ctx.m_update_left, m_ctx.m_update_right);
        }
    };

    buffer<pair<level, level>> m_postponed;
    /* If m_full_postponed is false, then postponed constraints involving max and imax
       that cannot be solved precisely are ignored. This step is approximate, and it is
       useful to skip it until we have additional information. */
    bool                       m_full_postponed{true};

    std::function<bool(name const & e)> const * m_transparency_pred{nullptr}; // NOLINT

    static bool is_equiv_cache_target(expr const &, expr const &) {
        lean_unreachable();
    }
    bool is_cached_equiv(expr const &, expr const &) { lean_unreachable(); }
    void cache_equiv(expr const &, expr const &) {
        lean_unreachable();
    }

    void cache_failure(expr const & t, expr const & s);
    bool is_cached_failure(expr const & t, expr const & s);

    void init_local_instances();
    void update_local_instances(expr const & new_local, expr const & new_type);

    optional<projection_info> is_projection(expr const & e);
    optional<expr> reduce_projection_core(optional<projection_info> const & info, expr const & e);

public:
    type_context_old(environment const & env, options const & o, transparency_mode m = transparency_mode::Reducible);
    explicit type_context_old(environment const & env, transparency_mode m = transparency_mode::Reducible):
        type_context_old(env, options(), m) {}
    virtual ~type_context_old();

    type_context_old & operator=(type_context_old const &) = delete;
    type_context_old & operator=(type_context_old &&) = delete;

    virtual environment const & env() const override { return m_env; }
    options const & get_options() const { lean_unreachable(); }

    // TODO(Leo): avoid ::lean::mk_fresh_name
    virtual name next_name() override { return ::lean::mk_fresh_name(); }

    virtual optional<name> get_local_pp_name(expr const &) override {
        lean_unreachable();
    }


    void set_env(environment const & env);

    /* Store the current local instances in the local context.
       This has the following implications:

       1- (Fewer cache resets)
          Since the set of local instances has been frozen, we don't need to update it
          when using `push_local` or `push_let`. We also do not need to flush the instance/subsingleton cache
          when we using `push_local`, `push_let` and `pop_local`.

       2- (Faster type_context_old initialization)
          We don't need to recompute the set of local instances when we initialize
          another type_context_old using a local_context object with frozen local instances.
          This is particularly useful if the local_context is huge. Recall that to compute the set of
          local instance, we need to traverse the whole local context.
          Recall that we create many short lived type_context_old objects in the tactic framework.
          For example, the tactic `infer_type t` creates a type_context_old object just to infer the type of `t`.

       3- The instance and subsingleton caches can be reused in other type_context_old objects
          IF the local_context is set with the same frozen local instances.

       4- (Drawback) Local instances cannot be reverted anymore.

       This method is invoked after we parse the header of a declaration.

       TODO(Leo):
       add tactic `unfreeze_local_instances : tactic unit` which unfreezes the set of frozen local instances
       for the current goal. */
    void freeze_local_instances();

    bool is_def_eq(level const & l1, level const & l2);
    virtual expr whnf(expr const &) override {
        lean_unreachable();
    }

    virtual expr infer(expr const &) override {
        lean_unreachable();
    }

    virtual expr check(expr const &) override {
        lean_unreachable();
    }

    virtual bool is_def_eq(expr const &, expr const &) override { lean_unreachable(); }

    bool match(expr const & e1, expr const & e2) {
        flet<bool> update_left(m_update_left, true);
        flet<bool> no_update_right(m_update_right, false);
        return is_def_eq(e1, e2);
    }

    bool unify(expr const & e1, expr const & e2) {
        flet<bool> update_left(m_update_left, true);
        flet<bool> update_right(m_update_right, true);
        return is_def_eq(e1, e2);
    }

    virtual expr relaxed_whnf(expr const &) override {
        lean_unreachable();
    }
    virtual bool relaxed_is_def_eq(expr const &, expr const &) override {
        lean_unreachable();
    }

    optional<expr> unfold_definition(expr const &) {
        lean_unreachable();
    }

    /** Non destructive is_def_eq (i.e., metavariables cannot be assigned) */
    bool pure_is_def_eq(level const & l1, level const & l2) {
        flet<bool> no_update_left(m_update_left, false);
        flet<bool> no_update_right(m_update_right, false);
        return is_def_eq(l1, l2);
    }

    /** Non destructive is_def_eq (i.e., metavariables cannot be assigned) */
    bool pure_is_def_eq(expr const & e1, expr const & e2) {
        flet<bool> no_update_left(m_update_left, false);
        flet<bool> no_update_right(m_update_right, false);
        return is_def_eq(e1, e2);
    }

    /** Non destructive relaxed_is_def_eq (i.e., metavariables cannot be assigned) */
    bool pure_relaxed_is_def_eq(expr const & e1, expr const & e2) {
        flet<bool> no_update_left(m_update_left, false);
        flet<bool> no_update_right(m_update_right, false);
        return relaxed_is_def_eq(e1, e2);
    }

    optional<expr> is_stuck_projection(expr const &) { lean_unreachable(); }
    virtual optional<expr> is_stuck(expr const &) override { lean_unreachable(); }

    virtual expr push_local(name const &, expr const &, binder_info) override {
        lean_unreachable();
    }
    virtual expr push_local_from_binding(expr const &) {
        lean_unreachable();
    }

    virtual void pop_local() override {
        lean_unreachable();
    }

    /** Similar to whnf, but invokes the given predicate before unfolding constant symbols in the head.
        If pred(e') is false, then the method will not unfold definition in the head of e', and will return e'.
        This method is useful when we want to normalize the expression until we get a particular symbol as the head symbol. */
    expr whnf_head_pred(expr const & e, std::function<bool(expr const &)> const & pred); // NOLINT
    optional<expr> reduce_projection(expr const & e);
    optional<expr> reduce_proj(expr const & e);
    optional<expr> reduce_aux_recursor(expr const & e);
    optional<expr> reduce_recursor(expr const & e);

    /** Similar to whnf, but ignores transparency annotations, and use
        the given predicate to decide whether a constant should be unfolded or not.

        Remark: cache is not used. */
    expr whnf_transparency_pred(expr const & e, std::function<bool(name const &)> const & pred); // NOLINT

    /** \brief Put \c e in whnf, it is a Pi, then return whnf, otherwise return e */
    expr try_to_pi(expr const & e);
    /** \brief Put \c e in relaxed_whnf, it is a Pi, then return whnf, otherwise return e */
    expr relaxed_try_to_pi(expr const &) {
        lean_unreachable();
    }

    /** Given a metavariable \c mvar, and local constants in \c locals, return (mvar' C) where
        C is a superset of \c locals and includes all local constants that depend on \c locals.
        \pre all local constants in \c locals are in metavariable context.
        \remark locals is updated with dependencies.

        \remark If preserve_locals_order is true, then the initial order elements in locals
        are not reordered, and an exception is thrown if locals[i] depends on locals[j] for i < j.
    */
    expr revert(buffer<expr> & locals, expr const & mvar, bool preserve_locals_order);

    expr mk_lambda(buffer<expr> const & locals, expr const & e);
    expr mk_pi(buffer<expr> const & locals, expr const & e);
    expr mk_lambda(expr const & local, expr const & e);
    expr mk_pi(expr const & local, expr const & e);
    expr mk_lambda(std::initializer_list<expr> const & locals, expr const & e);
    expr mk_pi(std::initializer_list<expr> const & locals, expr const & e);

    /* Add a let-decl (aka local definition) to the local context */
    expr push_let(name const & ppn, expr const & type, expr const & value);

    bool is_prop(expr const &) { lean_unreachable(); }
    bool is_proof(expr const &) { lean_unreachable(); }

    optional<name> is_class(expr const &) { lean_unreachable(); }
    optional<expr> mk_class_instance(expr const & type);
    optional<expr> mk_subsingleton_instance(expr const & type);
    /* Create type class instance in a different local context */

    transparency_mode mode() const { return m_transparency_mode; }
    unsigned mode_idx() const { return static_cast<unsigned>(mode()); }

    expr eta_expand(expr const & e);

    /* Try to assign metavariables occuring in e using type class resolution */
    expr complete_instance(expr const & e);

    struct transparency_scope : public flet<transparency_mode> {
        transparency_scope(type_context_old & ctx, transparency_mode m):
            flet<transparency_mode>(ctx.m_transparency_mode, m) {
        }
    };

    /* Enable/disable all unifier approximations. */
    struct approximate_scope : public flet<unifier_config> {
        approximate_scope(type_context_old & ctx, bool approx = true):
            flet<unifier_config>(ctx.m_unifier_cfg, unifier_config(approx, approx, approx)) {}
    };

    struct fo_unif_approx_scope : public flet<bool> {
        fo_unif_approx_scope(type_context_old & ctx, bool approx = true):
            flet<bool>(ctx.m_unifier_cfg.m_fo_approx, approx) {}
    };

    struct const_unif_approx_scope : public flet<bool> {
        const_unif_approx_scope(type_context_old & ctx, bool approx = true):
            flet<bool>(ctx.m_unifier_cfg.m_const_approx, approx) {}
    };

    struct ctx_unif_approx_scope : public flet<bool> {
        ctx_unif_approx_scope(type_context_old & ctx, bool approx = true):
            flet<bool>(ctx.m_unifier_cfg.m_ctx_approx, approx) {}
    };

    struct quasi_pattern_unif_approx_scope : public flet<bool> {
        quasi_pattern_unif_approx_scope(type_context_old & ctx, bool approx = true):
            flet<bool>(ctx.m_unifier_cfg.m_quasi_pattern_approx, approx) {}
    };

    struct full_postponed_scope : public flet<bool> {
        full_postponed_scope(type_context_old & ctx, bool full = true):
            flet<bool>(ctx.m_full_postponed, full) {}
    };

    struct smart_unfolding_scope : public flet<bool> {
        smart_unfolding_scope(type_context_old & ctx, bool enable = true):
            flet<bool>(ctx.m_smart_unfolding, enable) {}
    };

    struct relaxed_scope {
        transparency_scope m_transparency_scope;
        relaxed_scope(type_context_old & ctx, transparency_mode m = transparency_mode::All):
            m_transparency_scope(ctx, m) {
        }
    };

    /* --------------------------
       Temporary assignment mode.
       It is used when performing type class resolution and matching.
       -------------------------- */
public:
    optional<level> get_tmp_uvar_assignment(unsigned idx) const;
    optional<expr> get_tmp_mvar_assignment(unsigned idx) const;
    optional<level> get_tmp_assignment(level const & l) const;
    optional<expr> get_tmp_assignment(expr const & e) const;
    level mk_tmp_univ_mvar();
    expr mk_tmp_mvar(expr const & type);
    expr get_tmp_mvar_type(expr const & mvar) const;

    /* Helper class to reset m_used_assignment flag */
    class reset_used_assignment {
        type_context_old & m_ctx;
        bool           m_old_used_assignment;
    public:
        reset_used_assignment(type_context_old & ctx):
            m_ctx(ctx),
            m_old_used_assignment(m_ctx.m_used_assignment) {
            m_ctx.m_used_assignment = false;
        }

        ~reset_used_assignment() {
            /* If m_used_assignment was set since construction time, then we keep it set.
               Otherwise, we restore the previous value. */
            if (!m_ctx.m_used_assignment) {
                m_ctx.m_used_assignment = m_old_used_assignment;
            }
        }
    };

    level mk_fresh_univ_metavar();

private:
    void init_core(transparency_mode m);
    optional<expr> unfold_definition_core(expr const & e);
    expr whnf_core(expr const & e, bool proj_reduce, bool aux_rec_reduce);
    optional<constant_info> get_decl(transparency_mode, name const &) { lean_unreachable(); }
    optional<constant_info> get_decl(name const &) { lean_unreachable(); }

private:
    /* ------------
       Temporary metavariable assignment.
       ------------ */
    void assign_tmp(level const & u, level const & l);
    void assign_tmp(expr const & m, expr const & v);

    /* ------------
       Uniform interface to tmp/regular metavariables
       ------------ */
public:
    bool is_mvar(level const & l) const;
    /* Return true iff `e` is a regular or temporary metavar */
    bool is_mvar(expr const & e) const;
    /* Return true iff
       1- `l` is a temporary universe metavariable and type_context_old is in tmp mode, OR
       2- `l` is a regular universe metavariable an type_context_old is not in tmp_mode. */
    bool is_mode_mvar(level const & l) const;
    /* Return true iff
       1- `e` is a temporary metavariable and type_context_old is in tmp mode, OR
       2- `e` is a regular metavariable an type_context_old is not in tmp_mode. */
    bool is_mode_mvar(expr const & e) const;

    bool is_assigned(level const & l) const;
    bool is_assigned(expr const & e) const;
    optional<level> get_assignment(level const & l) const;
    optional<expr> get_assignment(expr const & e) const;
    void assign(level const & u, level const & l);
    void assign(expr const & m, expr const & v);
    level instantiate_mvars(level const & l);
    expr instantiate_mvars(expr const &) { lean_unreachable(); }
    /** \brief Instantiate the assigned meta-variables in the type of \c m
        \pre get_metavar_decl(m) is not none */
    /** Set the number of tmp metavars.
        \pre in_tmp_mode() */
    void resize_tmp_mvars(unsigned new_sz = 0);

private:
    /* ------------
       Type inference
       ------------ */
    expr infer_core(expr const & e);
    expr infer_fvar(expr const & e);
    expr infer_metavar(expr const & e);
    expr infer_constant(expr const & e);
    expr infer_lambda(expr e);
    optional<level> get_level_core(expr const & A);
    level get_level(expr const & A);
    expr infer_pi(expr e);
    expr infer_app(expr const & e);
    expr infer_proj(expr const & e);
    expr infer_let(expr e);

public:
    /* ------------
       is_def_eq
       ------------ */
    void push_scope();
    void pop_scope();
private:
    void commit_scope();
    class scope {
        friend class type_context_old;
        type_context_old & m_owner;
        bool           m_keep;
        unsigned       m_postponed_sz;
    public:
        scope(type_context_old & o):m_owner(o), m_keep(false), m_postponed_sz(o.m_postponed.size()) { m_owner.push_scope(); }
        ~scope() { m_owner.m_postponed.resize(m_postponed_sz); if (!m_keep) m_owner.pop_scope(); }
        void commit() { m_postponed_sz = m_owner.m_postponed.size(); m_owner.commit_scope(); m_keep = true; }
    };
    bool process_postponed(scope const & s);
    bool fo_unif_approx() const { return m_unifier_cfg.m_fo_approx; }
    bool ctx_unif_approx() const { return m_unifier_cfg.m_ctx_approx; }
    bool quasi_pattern_unif_approx() const { return m_unifier_cfg.m_quasi_pattern_approx; }
    bool approximate() const { return fo_unif_approx() || ctx_unif_approx() || quasi_pattern_unif_approx(); }
    expr try_zeta(expr const & e);
    expr expand_let_decls(expr const & e);
    friend struct check_assignment_fn;
    optional<expr> check_assignment(buffer<expr> const & locals, buffer<expr> const & in_ctx_locals, expr const & mvar, expr v);
    bool process_assignment(expr const & m, expr const & v);
    bool process_assignment_fo_approx(expr const & mvar, buffer<expr> const & args, expr const & new_v);
    bool process_assignment_fo_approx_core(expr const & mvar, buffer<expr> const & args, expr const & v);

    optional<constant_info> is_delta(expr const & e);
    enum class reduction_status { Continue, DefUnknown, DefEqual, DefDiff };

    bool solve_u_eq_max_u_v(level const & lhs, level const & rhs);
    lbool is_def_eq_core(level const & l1, level const & l2, bool partial);
    lbool partial_is_def_eq(level const & l1, level const & l2);
    bool full_is_def_eq(level const & l1, level const & l2);
    bool is_def_eq(levels const & ls1, levels const & ls2);
    bool is_def_eq_core_core(expr t, expr s);
    bool is_def_eq_core(expr const & t, expr const & s);
    bool is_def_eq_binding(expr e1, expr e2);
    expr try_to_unstuck_using_complete_instance(expr const &) {
        lean_unreachable();
    }
    optional<expr> is_eta_unassigned_mvar(expr const & e);
    bool is_def_eq_args(expr const & e1, expr const & e2);
    bool is_def_eq_eta(expr const & e1, expr const & e2);
    bool is_def_eq_proof_irrel(expr const & e1, expr const & e2);
    lbool quick_is_def_eq(expr const & e1, expr const & e2);
    lbool is_def_eq_delta(expr const & t, expr const & s);
    lbool is_def_eq_proj(expr t, expr s);
    optional<pair<expr, expr>> find_unsynth_metavar(expr const & e);
    bool mk_nested_instance(expr const & m, expr const & m_type);

    /* Support for solving offset constraints, see issue #1226 */
    optional<unsigned> to_small_num(expr const & e);
    optional<unsigned> is_offset_term (expr const & t);
    lbool try_offset_eq_offset(expr const & t, expr const & s);
    lbool try_offset_eq_numeral(expr const & t, expr const & s);
    lbool try_numeral_eq_numeral(expr const & t, expr const & s);
    lbool try_nat_offset_cnstrs(expr const & t, expr const & s);

protected:
    virtual bool on_is_def_eq_failure(expr const &, expr const &) {
        lean_unreachable();
    }

private:
    /* ------------
       Type classes
       ------------ */
    optional<name> constant_is_class(expr const & e);
    optional<name> is_full_class(expr type);
    lbool is_quick_class(expr const & type, name & result);
    expr preprocess_class(expr const & type, buffer<level_pair> & u_replacements, buffer<expr_pair> & e_replacements);

public:
    /* Helper class for creating pushing local declarations into the local context m_lctx */
    class tmp_locals {
        type_context_old & m_ctx;
        buffer<expr>       m_locals;

        /* \brief Return true iff all locals in m_locals are let-decls */
        bool all_let_decls() const;
    public:
        tmp_locals(type_context_old & ctx):m_ctx(ctx) {}
        ~tmp_locals();

        type_context_old & ctx() { return m_ctx; }

        expr push_local(name const & pp_name, expr const & type, binder_info bi = mk_binder_info()) {
            expr r = m_ctx.push_local(pp_name, type, bi);
            m_locals.push_back(r);
            return r;
        }

        expr push_let(name const &, expr const &, expr const &) {
            lean_unreachable();
        }

        expr push_local_from_binding(expr const & e) {
            lean_assert(is_binding(e));
            return push_local(binding_name(e), binding_domain(e), binding_info(e));
        }

        expr push_local_from_let(expr const &) {
            lean_unreachable();
        }

        unsigned size() const { return m_locals.size(); }
        expr const * data() const { return m_locals.data(); }

        buffer<expr> const & as_buffer() const { return m_locals; }

        expr mk_lambda(expr const & e) { return m_ctx.mk_lambda(m_locals, e); }
        expr mk_pi(expr const & e) { return m_ctx.mk_pi(m_locals, e); }
        expr mk_let(expr const & e) { lean_assert(all_let_decls()); return m_ctx.mk_lambda(m_locals, e); }
    };
    friend class tmp_locals;
};

void initialize_type_context();
void finalize_type_context();
}
