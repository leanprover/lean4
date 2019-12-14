/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <algorithm>
#include "runtime/flet.h"
#include "util/lbool.h"
#include "util/fresh_name.h"
#include "kernel/environment.h"
#include "library/abstract_type_context.h"
#include "library/idx_metavar.h"
#include "library/projection.h"
#include "library/metavar_context.h"
#include "library/abstract_context_cache.h"
#include "library/exception.h"
#include "library/expr_pair.h"
#include "library/local_instances.h"

namespace lean {
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
    typedef buffer<metavar_context> mctx_stack;
    enum class tmp_trail_kind { Level, Expr };
    typedef buffer<pair<tmp_trail_kind, unsigned>> tmp_trail;
    friend struct instance_synthesizer;
    struct scope_data {
        metavar_context m_mctx;
        unsigned        m_tmp_uassignment_sz;
        unsigned        m_tmp_eassignment_sz;
        unsigned        m_tmp_trail_sz;
        scope_data(metavar_context const & mctx, unsigned usz, unsigned esz, unsigned tsz):
            m_mctx(mctx), m_tmp_uassignment_sz(usz), m_tmp_eassignment_sz(esz), m_tmp_trail_sz(tsz) {}
    };
public:
    /*
      NEW DESIGN notes. (This is work in progress)

      Two kinds of metavariables are supported: regular and temporary.

      *** Regular metavariables ***

      The regular metavariable declarations are stored in the metavariable
      context object defined at `metavar_context`. Each declaration
      contain the local context and the type of the metavariable.
      We use the notation

          ?m : ctx |- type

      to represent a metavariable `?m` with local context `ctx` and
      type `type`. In the tactic framework, each goal is represented
      as a regular metavariable. We also have regular universe metavariables.
      We assign (universe) terms to (universe) metavariables. The assignments
      are stored in the `metavar_context` object. The context is used
      to decide whether an assignment is valid or not. For example,
      given the metavariable

          ?m : (n m : nat) (h : m = n) |- n = m

      The assignment

          ?m := h'

      is not valid since `h'` is not part of the local context, but

          ?m := @eq.symm nat m n h

      is a valid assignment because all locals are in the local context,
      and the type of the term being assigned to `?m` is definitionally
      equal to the type of `?m`.

      Regular metavariables are also used to represent `_` holes
      during the elaboration process.

      *** Temporary metavariables ***

      Several procedures (e.g., type class resolution, simplifier) need
      to create metavariables that are needed for a short period of time.
      For example, when applying a simplification lemma such as

         forall x, f x x = x

      to a subterm `t`, we need need to check whether the term
      `t` is an instance of `f ?x ?x`, where `?x` is a fresh metavariable.
      That is, we need to find an assignment for `?x` such that `t`
      and `f ?x ?x` become definitionally equal. If the assignment is found,
      we replace the term `t` with the term assigned to `?x`. After that,
      we don't need the metavariable `?x` anymore. We don't want to
      use regular metavariables for this operation since we don't want
      to waste time declaring them (i.e., updating `metavar_context`),
      then creating the term `f ?x ?x` with the newly created metavariable,
      and then performing the matching operation, and finally deleting `?x`.
      We avoid this overhead by using temporary metavariables.
      All temporary metavariables used to solve a particular problem (e.g., matching)
      share the same local context, the type of a metavariable is stored in
      the metavariable itself, finally the metavariable uses an unique
      (usually) small integer as its identifier. The raw API for creating
      temporary metavariables is defined in the file idx_metavar.h.
      Since, the identifiers of temporary metavariables are small integers,
      we implement the temporary metavariable assignment using arrays.
      This is much more efficient than using a map datastructure.

      *** Temporary metavariable Offsets (discarded) ***

      Remark: this is a feature we considered using, but discarded.
      We briefly describe it here, and then describe the problems that made
      us discard it.

      When trying to apply a simplification such as `forall x, f x x = x` to a term `t`,
      we don't want to create a fresh metavariable `?x` and a new term `f ?x ?x` (called pattern)
      every single time. This would be too inefficient.  We create the temporary
      metavariables and the pattern once for each simplification lemma
      and use them multiple times. However, sometimes we need to solve a subproblem S that
      requires temporary metavariables while solving a problem P that
      also requires temporary metavariables. If both S and P use
      pre-allocated temporary metavariables and patterns, the small
      integers used to identify temporary metavariables may overlap.
      We address this issue  by using `offsets`. The operation
      `lift k t`, where `k` is an offset and `t` is a term, returns
      the term `t'` where each temporary metavariable with index `i` in `t`
      is replaced with one with index `i+k`. To avoid the explicit construction of
      term `t'`, we considered using an `is_def_eq` predicate that takes offsets as parameters.
      That is, `is_def_eq(k_1, t_1, k_2, t_2)` checks whether
      the terms `lift k_1 t_1` and `lift k_2 t_2` are definitionally equal
      without constructing these terms explicitly.

      Remark: when assigning `(k_1, ?x) := (k_2, t)` where `?x` is a temporary metavariable
      and `k_1` and `k_2` are offsets, we update the array entry `idx(?x) + k_1` with
      `(lift k_2 t)`.

      Remark: when solving `(k_1, ?x) =?= (k_2, t)` where `?x` is an assigned temporary metavariable,
      i.e., `assignment[idx(?x) + k_1] := s`, we reduce the constraint to
      `(0, s) =?= (k_2, t)`.

      This approach is used in several automated first-order theorem provers.
      However, we found several complications when trying to use it
      in Lean. Some of the problems affect any prover based on
      dependent type theory. The main problem is reduction, that is,
      `is_def_eq` can reduce a constraint `t =?= s` into `t' =?= s`,
      if `t` reduces to `t'`. Reduction modulo offsets is messy.
      The problem is that reduction may need to access the assignment, and invoke `is_def_eq` recursively.
      If reduction tries to substitute a metavar with its assignment, we are in trouble since the offset
      would not be the same for all subterms. For example, if we have a term `C.rec_on ?x_i h` and offset `k`.
      If we replace `x_i` with its assignment `v`, the offset for `v` is 0. We would need to have a macro
      to mark the offset of subterms, but then this macro would have to interact with reduction.
      Another problem is that `type_context_old` invokes many auxiliary functions and modules.
      Most of them would have to be offset aware.

      So, we decide to use a different and simpler approach, where we simply cache the
      result of the lift operation.

      *** Backtracking and scopes ***

      The type context performs "local backtracking" when deciding whether two terms
      are definitionally equal or not (i.e., at the `is_def_eq` method).
      When backtracking, assignments have to be undone.
      For example, when checking `f a =?= f b` (i.e., `f a` is definitionally equal
      fo `f b`), we first check `a =?= b`, if it fails, we backtrack and try
      to unfold the `f`-applications. We say the backtracking is local
      because if `a =?= b` succeeds, we commit to this choice.

      This kind of local backtracking is implemeted using "scope" objects.
      It saves the current state of `metavar_context` and the size of the
      trail stack (aka undo stack) for temporary metavariables. Whenever a temporary
      metavariable is assigned a new entry is inserted into the trail stack.

      Remark: tyhe type class resolution procedure uses "global backtracking",
      and can be viewed as a (very) basic lambda prolog interpreter.

      *** Unification vs Matching vs pure definitional equality ***

      Suppose we have a simplification lemma `forall x, f x 0 = x`,
      and a term `f a ?m`, where `?m` is a regular metavariable, from our goal.
      We don't want to solve the constraint `f ?x 0 =?= f a ?m` by assigning
      `?x := a` and `?m := 0`. That is, we don't want to restrict the
      possible interpretations for `?m` based on a simplification rule
      that is being applied automatically. In this kind of scenario,
      we want to treat `?m` as a constant instead of a metavariable.
      We say `f ?x 0 =?= f a ?m` is a matching problem when only the
      metavariables occurring on the left-hand-side can be assigned.

      If metavariables occurring on both sides can be assigned, we say it is
      a unification problem.

      If metavariables on both sides cannot be assigned, we say it is
      a pure definitional equality problem. This mode is used to implement
      the tactic `tactic.is_def_eq t s` that should only succeed if
      `t` and `s` are definitionally equal without assigining any
      metavariables occurring in them.

      The three kinds of problems described above are implemented using the `is_def_eq`
      method. It uses two flags to track whether metavariables occurring on the
      right and left hand side can be assigned or not.

      There is a special case where a metavariable can be assigned even
      if the flag indicates no metavariable can be assigned.
      Suppose we are trying to solve the following matching problem:

          nat.add ?x_0 (nat.succ ?x_1) =?= nat.add n (@one nat ?m)

      The term `@one nat ?m` cannot be reduced to `nat.succ nat.zero`
      because the type class instance has not been synthesized yet.
      This kind of problem occurs in practice. We have considered two
      solutions

      a) Make sure we solve any pending type class resolution problem
         before trying to match. Unfortunately, this is too expensive.

      b) Allow metavariables on the right hand side to be assigned
         by type class resolution during the matching.
         We use this option. We say this design decision is fine
         because we are not changing the meaning of the right hand
         side, we are just solving a pending type class resolution
         problem that would be solved later anyway.
         This also forces us to have an offset for the right hand side
         even if we are solving a matching problem.

         Corner case: we could synthesize `?m`,
         but the assignment is undone during backtracking.
         In versions <= 3.3, this would not be a problem if `inout` parameters were not used.
         In this case, we should produce the same solution again when we
         try to synthesize `?m` again. Here, we are assuming that the same
         set of local type class instances will be used. If `inout` parameters
         were used, we may be in a situation that when we try again we have
         more information about this parameter and a different instance is
         selected.
         We addressed this issue by replacing `inout` parameters with `out` parameters.
         Then, the result of the type class resolution procedure will not depend on
         partial information available on `out` parameters.

      *** TMP mode ***

      To be able to use temporary metavariables, the type_context_old must
      be put into TMP mode. We have an auxiliary object to set/unset
      TMP mode.

      *** Cache ***

      We only cache results for `is_def_eq` if the terms do not contain
      metavariables. Thus, the cached results do not depend
      on whether metavariable assignments are allowed on
      the left/right hand sides or not.

      Possible improvement: cache results if metavariable assignments
      did not occur AND we are not in TMP mode.
      We use this approach for the infer and whnf caches.

      *** Temporary metavariable leaks ***

      When checking `t =?= s` using `is_def_eq`, we want to make sure we
      cannot assign a term `t` to a regular metavariable `?m` IF `t` contains temporary
      metavariables. This is important because the scope of temporary metavariable is
      defined by the problem that created it.
      Moreover, the same metavariable id may be used by different
      modules. So, we should make sure a temporary metavariable should not
      leak into a goal. More generally, the temporary metavariables used to solve
      a problem P should not leak outside of P.

      Ideally, when checking `t =?= s` we would like to assume that
      `t` (`s`) contains only regular metavariables OR only temporary metavariables.
      That is, it cannot mix both.
      Unfortunately, this property is not true. For example, a local type class instance
      may contain assigned regular metavariables. So, if we use this local instance
      during type class resolution, we would have create a term containing regular and temporary
      metavariables. The refinement

          `t` (`s`) contains only regular metavariables OR (temporary metavariables and assigned regular metavariables)

      is also not sufficient. The problem is universe metavariables. Again, local type class instances
      and local simplification lemmas may contain regular metavariables. When using them during
      type class resolution or simplification, we would create terms containing both kinds of
      metavariables. Here is an example that exposes this problem:
      ```
      protected def erase {α} [decidable_eq α] : list α → α → list α
      | []     b := []
      | (a::l) b := if a = b then l else a :: erase l b
      ```
      We could avoid this particular instances IF we convert unassigned universe metavariables occurring
      in the type into local universe parameters before we process the body of this definition.
      However, this is not a general solution because the local instance may be used to resolve type
      class resolution problems in the type itself.

      Thus, to avoid these problems, when the `type_context_old` is in TMP mode, we do not
      assign regular metavariables. In TMP mode, regular metavariables are always treated
      as opaque constants.

      *** Applications ***

      Here we assume the `is_def_eq` general form is

      lctx | (a_1, t_1) =?= (a_2, t_2)

      where `lctx` is the local context for the temporary metavariables occurring in `t_i`;
      `a_i` is a flag indicating whether metavariables occurring in `t_i` can be assigned or not.
      The local context `lctx` is only relevant for `t_i` is `a_i` is set to true.
      `lctx` is only relevant if we are in TMP mode. We use `lctx` to validate
      whether an assignment to a temporary metavariable is valid or not.

      We use the following shorthands

      `(unify) t =?= s` denotes `_ | (true, t) =?= (true, s)`
      `(match) t =?= s` denotes `_ | (true, t) =?= (false, s)`
      `(pure) t =?= s` denotes `_ | (false, t) =?= (false, s)`
      `(tmp-match) lctx | t =?= s` denotes `lctx | (true, t) =?= (false, s)`
      `(nested-tmp-match) lctx | (k', t) =?= s` denotes `lctx | (true, lift k' t) =?= (false, s)`
      `(tmp-unify) lctx | t =?= s` denotes `lctx | (true, t) =?= (true, s)`

      - Elaboration and tactics such as `apply`. We use `(unify) t =?= s`

      - We also want to support a version of `apply` where metavariables
      in the goal cannot be assigned. This variant does not exist
      in versions <= 3.3. We use `(match) t =?= s`

      - `rewrite` tactic, we use `(unify) t =?= s`.
      We also have the a variant (not available in versions <= 3.3) where
      we use regular metavariables and matching. In this case, we use `(match) t =?= s`

      - `tactic.is_def_eq`: we use `(pure) t =?= s`

      - `app_builder`: a helper procedure for creating applications
      where missing arguments and universes levels are inferred using type inference.
      It takes a `type_context_old` `ctx` as argument.
      We use `(tmp-match) lctx | t =?= s` where `lctx` is `ctx.lctx()`

      - (Internal) Type class resolution: we use temporary metavariables and unification.
      Before trying to synthesize `?m : C a_1 ... a_n`,
      we use a preprocessing step that creates `C a_1' ... a_n'` where `a_i'` contains
      only fresh new temporary metavariables. So, no offsets are needed since
      we don't use pre-allocated temporary metavars. Thus, we use
      `(tmp-unify) lctx | t =?= s` where `lctx` is the local context for `?m`.
    */

    /* This class supports temporary meta-variables "mode". In this "tmp" mode,
       is_metavar_decl_ref and is_univ_metavar_decl_ref are treated as opaque constants,
       and temporary metavariables (idx_metavar) are treated as metavariables,
       and their assignment is stored at m_tmp_eassignment and m_tmp_uassignment.

       m_tmp_eassignment and m_tmp_uassignment store assignment for temporary/idx metavars

       These assignments are only used during type class resolution and matching operations.
       They are references to stack allocated buffers provided by customers.
       They are nullptr if type_context_old is not in tmp_mode. */
    struct tmp_data {
        tmp_uassignment & m_uassignment;
        tmp_etype       & m_etype;
        tmp_eassignment & m_eassignment;
        /* m_tmp_mvar_local_context contains m_lctx when tmp mode is activated.
           This is the context for all temporary meta-variables. */
        local_context     m_mvar_lctx;
        /* undo/trail stack for m_tmp_uassignment/m_tmp_eassignment */
        tmp_trail         m_trail;
        tmp_data(tmp_uassignment & uassignment, tmp_etype & etype, tmp_eassignment & eassignment, local_context const & lctx):
            m_uassignment(uassignment), m_etype(etype), m_eassignment(eassignment), m_mvar_lctx(lctx) {}
    };
private:
    typedef buffer<scope_data> scopes;
    typedef abstract_context_cache cache;
    typedef context_cacheless dummy_cache;
    environment        m_env;
    metavar_context    m_mctx;
    local_context      m_lctx;
    dummy_cache        m_dummy_cache; /* cache used when user does not provide a cache */
    cache *            m_cache;
    local_instances    m_local_instances;
    /* We only cache results when m_used_assignment is false */
    bool               m_used_assignment{false};
    transparency_mode  m_transparency_mode;
    /* m_in_is_def_eq is a temporary flag set to true in the beginning of is_def_eq. */
    bool               m_in_is_def_eq{false};
    /* m_is_def_eq_depth is only used for tracing purposes */
    unsigned           m_is_def_eq_depth{0};
    /* Stack of backtracking point (aka scope) */
    scopes             m_scopes;
    tmp_data *         m_tmp_data{nullptr};
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

    /*
      When unfolding recursive functions during `is_def_eq`,
      we don't want to expose the internal details used to compile
      recursive equations. The equation compiler uses
      different strategies, and exposing these internal details
      may confuse users (see issue #1794). This was a recurrent
      problem before smart unfolding was implemented.
      The idea is quite simple, given an application `f a_1 ... a_n`,
      type_context_old checks whether there is a `f._sunfold` helper
      definition in the environment, if there is one, it uses it
      to unfold the term, and then reduces the resulting term until an
      `id_rhs _ t` application is the head. If this application is found,
      then `t` is the result of the unfolding. If not, then the application
      is not unfolded. The helper `f._sunfold` declarations are automatically
      generated by the equation compiler. Here is an example, given the declaration

      ```
      def nat.add : nat -> nat -> nat
      | 0            b := b
      | (nat.succ a) b := nat.succ (nat.add a b)
      ```

      the equation compiler generates the auxiliary definition

      ```
      def nat.add._sunfold (a b : nat) : nat :=
      nat.cases_on a (id_rhs nat b) (fun a_1, id_rhs nat (nat.succ (nat.add a_1 b)))
      ```

      Then, when trying to unfold `nat.add x (nat.succ y)`, the term `nat.succ (nat.add x y)`
      is produced instead of `nat.succ (... incomprehensible mess that uses nat.brec_on ...)`.

      Note that `nat.add._sunfold` and `nat.add` are not definitionally equal.
      Given an application `f a_1 ... a_n`, the type_context_old only assumes that
      if `f._sunfold a_1 ... a_n` can be reduced to `id_rhs _ t`, then `f a_1 ... a_n` and
      `t` are definitionally equal.

      Remark: type_context_old also uses smart unfolding for definitions `f._match_<idx>`
    */

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

    /* Postponed universe constraints.
       We postpone universe constraints containing max/imax. Examples:

               max 1 ?u =?= max 1 a
               2        =?= max ?u ?v

       The universe constraint postponement is effective because universe
       metavariables get assigned later. For example consider the following unification
       problem

          M.{1 3 3} L.{3} =?= M.{1 ?u ?v} L.{(max 1 ?u ?v)}

       is solved by first solving

              L.{3} =?= L.{(max 1 ?u ?v)}

       which postpones the universe constraint

                3 =?= max 1 ?u ?v

       and then solves

             M.{1 3 3} =?= M.{1 ?u ?v}

       which generates the easy constraints

                ?u =?= 3 and ?v =?= 3

       Now, the postponed contraint (3 =?= max ?u ?v) can be easily solved.

       Note that providing universe levels explicitly is not always a viable workaround.
       The problem is that unification problems like the one above are often created by
       automation (e.g., type class resolution, tactics, etc). In these situations, users
       have no way of providing the universe parameters. The alternative would be to write
       the whole definition by hand without using any form of automation.

       We also make sure any choice-point only succeeds if all postponed universe
       constraints created by it are resolved.

       We also only cache results that do not have pending postponed constraints. */
    buffer<pair<level, level>> m_postponed;
    /* If m_full_postponed is false, then postponed constraints involving max and imax
       that cannot be solved precisely are ignored. This step is approximate, and it is
       useful to skip it until we have additional information. */
    bool                       m_full_postponed{true};

    std::function<bool(name const & e)> const * m_transparency_pred{nullptr}; // NOLINT

    static bool is_equiv_cache_target(expr const & e1, expr const & e2) {
        return !has_metavar(e1) && !has_metavar(e2) && (!is_atomic(e1) || !is_atomic(e2));
    }
    bool is_cached_equiv(expr const & e1, expr const & e2) {
        return is_equiv_cache_target(e1, e2) && m_cache->get_equiv(m_transparency_mode, e1, e2);
    }
    void cache_equiv(expr const & e1, expr const & e2) {
        if (is_equiv_cache_target(e1, e2)) m_cache->set_equiv(m_transparency_mode, e1, e2);
    }

    void cache_failure(expr const & t, expr const & s);
    bool is_cached_failure(expr const & t, expr const & s);

    void init_local_instances();
    void update_local_instances(expr const & new_local, expr const & new_type);

    optional<projection_info> is_projection(expr const & e);
    optional<expr> reduce_projection_core(optional<projection_info> const & info, expr const & e);

    type_context_old(abstract_context_cache * cache, metavar_context const & mctx, local_context const & lctx,
                 transparency_mode m);
public:
    type_context_old(environment const & env, metavar_context const & mctx, local_context const & lctx,
                 abstract_context_cache & cache, transparency_mode m = transparency_mode::Reducible);
    type_context_old(environment const & env, options const & o, metavar_context const & mctx, local_context const & lctx,
                 transparency_mode m = transparency_mode::Reducible);
    type_context_old(environment const & env, options const & o, local_context const & lctx,
                 transparency_mode m = transparency_mode::Reducible):
        type_context_old(env, o, metavar_context(), lctx, m) {}
    explicit type_context_old(environment const & env, transparency_mode m = transparency_mode::Reducible):
        type_context_old(env, options(), metavar_context(), local_context(), m) {}
    type_context_old(environment const & env, options const & o, transparency_mode m = transparency_mode::Reducible):
        type_context_old(env, o, metavar_context(), local_context(), m) {}
    type_context_old(environment const & env, abstract_context_cache & cache, transparency_mode m = transparency_mode::Reducible):
        type_context_old(env, metavar_context(), local_context(), cache, m) {}
    type_context_old(type_context_old const &) = delete;
    type_context_old(type_context_old &&);
    virtual ~type_context_old();

    type_context_old & operator=(type_context_old const &) = delete;
    type_context_old & operator=(type_context_old &&) = delete;

    virtual environment const & env() const override { return m_env; }
    options const & get_options() const { return m_cache->get_options(); }

    // TODO(Leo): avoid ::lean::mk_fresh_name
    virtual name next_name() override { return ::lean::mk_fresh_name(); }

    virtual optional<name> get_local_pp_name(expr const & e) override {
        if (optional<local_decl> decl = m_lctx.find_local_decl(e)) {
            return optional<name>(decl->get_user_name());
        }
        return optional<name>();
    }


    local_context const & lctx() const { return m_lctx; }
    metavar_context const & mctx() const { return m_mctx; }
    expr mk_metavar_decl(local_context const & ctx, expr const & type) { return m_mctx.mk_metavar_decl(ctx, type); }
    expr mk_metavar_decl(name const & pp_n, local_context const & ctx, expr const & type) { return m_mctx.mk_metavar_decl(pp_n, ctx, type); }
    optional<metavar_decl> find_metavar_decl(expr const & mvar) const { return m_mctx.find_metavar_decl(mvar); }

    level mk_univ_metavar_decl() { return m_mctx.mk_univ_metavar_decl(); }

    name get_unused_name(name const & prefix, unsigned & idx) const { return m_lctx.get_unused_name(prefix, idx); }
    name get_unused_name(name const & suggestion) const { return m_lctx.get_unused_name(suggestion); }

    /* note: mctx must be a descendant of m_mctx */
    void set_mctx(metavar_context const & mctx) { m_mctx = mctx; }
    /* note: env must be a descendant of m_env */
    void set_env(environment const & env);

    abstract_context_cache & get_cache() { return *m_cache; }

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
    virtual expr whnf(expr const & e) override;
    virtual expr infer(expr const & e) override;
    virtual expr check(expr const & e) override;
    virtual bool is_def_eq(expr const & e1, expr const & e2) override;
    bool is_def_eq_at(local_context const & lctx, expr const & a, expr const & b);

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

    virtual expr relaxed_whnf(expr const & e) override;
    virtual bool relaxed_is_def_eq(expr const & e1, expr const & e2) override;

    optional<expr> unfold_definition(expr const & e);

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

    optional<expr> is_stuck_projection(expr const & e);
    virtual optional<expr> is_stuck(expr const &) override;

    virtual expr push_local(name const & pp_name, expr const & type, binder_info bi = mk_binder_info()) override;
    virtual expr push_local_from_binding(expr const & e) {
        lean_assert(is_binding(e));
        return push_local(binding_name(e), binding_domain(e), binding_info(e));
    }

    virtual void pop_local() override;

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
    expr relaxed_try_to_pi(expr const & e);

    /** Given a metavariable \c mvar, and local constants in \c locals, return (mvar' C) where
        C is a superset of \c locals and includes all local constants that depend on \c locals.
        \pre all local constants in \c locals are in metavariable context.
        \remark locals is updated with dependencies.

        \remark If preserve_locals_order is true, then the initial order elements in locals
        are not reordered, and an exception is thrown if locals[i] depends on locals[j] for i < j.
    */
    expr revert(buffer<expr> & locals, expr const & mvar, bool preserve_locals_order);

    expr mk_lambda(local_context const & lctx, buffer<expr> const & locals, expr const & e);
    expr mk_pi(local_context const & lctx, buffer<expr> const & locals, expr const & e);
    expr mk_lambda(local_context const & lctx, expr const & local, expr const & e);
    expr mk_pi(local_context const & lctx, expr const & local, expr const & e);
    expr mk_lambda(local_context const & lctx, std::initializer_list<expr> const & locals, expr const & e);
    expr mk_pi(local_context const & lctx, std::initializer_list<expr> const & locals, expr const & e);

    expr mk_lambda(buffer<expr> const & locals, expr const & e);
    expr mk_pi(buffer<expr> const & locals, expr const & e);
    expr mk_lambda(expr const & local, expr const & e);
    expr mk_pi(expr const & local, expr const & e);
    expr mk_lambda(std::initializer_list<expr> const & locals, expr const & e);
    expr mk_pi(std::initializer_list<expr> const & locals, expr const & e);

    /* Add a let-decl (aka local definition) to the local context */
    expr push_let(name const & ppn, expr const & type, expr const & value);

    bool is_prop(expr const & e);
    bool is_proof(expr const & e);

    optional<name> is_class(expr const & type);
    optional<expr> mk_class_instance(expr const & type);
    optional<expr> mk_subsingleton_instance(expr const & type);
    /* Create type class instance in a different local context */
    optional<expr> mk_class_instance_at(local_context const & lctx, expr const & type);

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
    struct tmp_mode_scope {
        type_context_old &      m_ctx;
        buffer<optional<level>> m_tmp_uassignment;
        buffer<expr>            m_tmp_etype;
        buffer<optional<expr>>  m_tmp_eassignment;
        tmp_data *              m_old_data;
        tmp_data                m_data;
        tmp_mode_scope(type_context_old & ctx):
            m_ctx(ctx), m_old_data(ctx.m_tmp_data), m_data(m_tmp_uassignment, m_tmp_etype, m_tmp_eassignment, ctx.lctx()) {
            m_ctx.m_tmp_data = &m_data;
        }
        ~tmp_mode_scope() {
            m_ctx.m_tmp_data = m_old_data;
        }
    };
    struct tmp_mode_scope_with_data {
        type_context_old & m_ctx;
        tmp_data *     m_old_data;
        tmp_mode_scope_with_data(type_context_old & ctx, tmp_data & data):
            m_ctx(ctx), m_old_data(ctx.m_tmp_data) {
            m_ctx.m_tmp_data = &data;
        }
        ~tmp_mode_scope_with_data() {
            m_ctx.m_tmp_data = m_old_data;
        }
    };
    bool in_tmp_mode() const { return m_tmp_data != nullptr; }
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
    optional<constant_info> get_decl(transparency_mode m, name const & n);
    optional<constant_info> get_decl(name const & n);

private:
    pair<local_context, expr> revert_core(buffer<expr> & to_revert, local_context const & ctx,
                                          expr const & type, bool preserve_to_revert_order);
    expr revert_core(buffer<expr> & to_revert, expr const & mvar, bool preserve_to_revert_order);
    expr elim_mvar_deps(expr const & e, unsigned num, expr const * locals);
    expr mk_binding(bool is_pi, local_context const & lctx, unsigned num_locals, expr const * locals, expr const & e);

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
    bool is_regular_mvar(expr const & e) const { return is_metavar_decl_ref(e); }
    bool is_tmp_mvar(level const & l) const { return is_idx_metauniv(l); }
    bool is_tmp_mvar(expr const & e) const { return is_idx_metavar(e); }
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
    expr instantiate_mvars(expr const & e);
    /** \brief Instantiate the assigned meta-variables in the type of \c m
        \pre get_metavar_decl(m) is not none */
    void instantiate_mvars_at_type_of(expr const & m) {
        m_mctx.instantiate_mvars_at_type_of(m);
    }
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
    expr try_to_unstuck_using_complete_instance(expr const & e);
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
    virtual bool on_is_def_eq_failure(expr const & t, expr const & s);

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

        expr push_let(name const & name, expr const & type, expr const & value) {
            expr r = m_ctx.push_let(name, type, value);
            m_locals.push_back(r);
            return r;
        }

        expr push_local_from_binding(expr const & e) {
            lean_assert(is_binding(e));
            return push_local(binding_name(e), binding_domain(e), binding_info(e));
        }

        expr push_local_from_let(expr const & e) {
            lean_assert(is_let(e));
            return push_let(let_name(e), let_type(e), let_value(e));
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

/** Create a formatting function that can 'decode' metavar_decl_refs and local_decl_refs
    with declarations stored in mctx and lctx */
std::function<format(expr const &)>
mk_pp_ctx(environment const & env, options const & opts, metavar_context const & mctx, local_context const & lctx);

/** Create a formatting function that can 'decode' metavar_decl_refs and local_decl_refs
    with declarations stored in ctx */
std::function<format(expr const &)>
mk_pp_ctx(type_context_old const & ctx);

void initialize_type_context();
void finalize_type_context();
}
