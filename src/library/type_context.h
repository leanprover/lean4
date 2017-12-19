/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include "util/flet.h"
#include "util/lbool.h"
#include "kernel/environment.h"
#include "kernel/abstract_type_context.h"
#include "kernel/expr_maps.h"
#include "kernel/equiv_manager.h"
#include "kernel/pos_info_provider.h"
#include "library/idx_metavar.h"
#include "library/projection.h"
#include "library/metavar_context.h"
#include "library/expr_pair_maps.h"
#include "library/exception.h"
#include "library/unification_hint.h"

namespace lean {
class class_exception : public generic_exception {
public:
    class_exception(expr const & m, char const * msg):generic_exception(m, msg) {}
};

#define LEAN_NUM_TRANSPARENCY_MODES 5
enum class transparency_mode { All = 0, Semireducible, Instances, Reducible, None };


bool is_at_least_semireducible(transparency_mode m);
bool is_at_least_instances(transparency_mode m);

transparency_mode ensure_semireducible_mode(transparency_mode m);
transparency_mode ensure_instances_mode(transparency_mode m);

/* \brief Cached information for type_context. */
class type_context_cache {
    typedef std::unordered_map<name, optional<declaration>, name_hash> transparency_cache;
    typedef std::unordered_map<name, bool, name_hash> name2bool;

    /** We use expr_cond_bi_struct_map because sometimes we want the inferred type to
        contain precise binder information (e.g., in the elaborator).
        Binder information includes the the binder annotations: {}, [], etc.

        That is, we want the type of (fun {A : Type} (a : A), a) to be (Pi {A : Type}, A -> A).

        When binder information is considered in the infer_cache, we can't reuse the
        cached value for (fun {A : Type} (a : A), a) when inferring the type of
        (fun (A : Type) (a : A), a). This is wasteful in modules such as the tactic framework.

        So, when we create a type_context_cache object we can specify whether this extra
        level of precision is required or not. */
    typedef expr_cond_bi_struct_map<expr> infer_cache;
    typedef expr_struct_map<expr> whnf_cache;
    typedef expr_struct_map<optional<expr>> instance_cache;
    typedef expr_struct_map<optional<expr>> subsingleton_cache;
    typedef std::unordered_set<expr_pair, expr_pair_hash, expr_pair_eq> failure_cache;

    environment                   m_env;
    options                       m_options;
    name_map<projection_info>     m_proj_info;

    /* We only cache inferred types if the metavariable assignment was not accessed.
       This restriction is sufficient to make sure the cached information can be reused
       because local declarations have unique global names, and these names
       are never reused. So, a term `t` containing locals `l_1, ..., l_n`
       will have the same type in any valid local context containing `l_1, ..., l_n`.

       \remark The inferred type does not depend on reducibility annotations. */
    infer_cache                   m_infer_cache;

    /* Mapping from name to optional<declaration>, this mapping is faster than the one
       at environment. Moreover, it takes into account constant reducibility annotations.
       We have four different modes.
       - ALL (everything is transparent).
       - SEMIREDUCIBLE (semireducible and reducible constants are considered transparent).
       - REDUCIBLE (only reducible constants are considered transparent).
       - NONE (everything is opaque).

       \remark In SEMIREDUCIBLE and REDUCIBLE modes, projections and theorems are considered
       opaque independently of annotations. In ALL mode, projections are considered opaque,
       this is not a problem since type_context implements a custom reduction rule for projections.

       The ALL mode is used for type inference where it is unacceptable to fail to infer a type.
       The SEMIREDUCIBLE mode is used for scenarios where an is_def_eq is expected to succeed
       (e.g., exact and apply tactics).
       The REDUCIBLE mode (more restrictive) is used during search (e.g., type class resolution,
       blast, etc).
       The NONE mode is used when normalizing expressions without using delta-reduction. */
    transparency_cache            m_transparency_cache[LEAN_NUM_TRANSPARENCY_MODES];

    equiv_manager                 m_equiv_manager[LEAN_NUM_TRANSPARENCY_MODES];

    failure_cache                 m_failure_cache[LEAN_NUM_TRANSPARENCY_MODES];

    whnf_cache                    m_whnf_cache[LEAN_NUM_TRANSPARENCY_MODES];

    name2bool                     m_aux_recursor_cache;

    /* We use the following approach for caching type class instances.

       Whenever a type_context object is initialized with a local_context lctx

       1) If lctx has an instance_fingerprint, then we compare with the instance_fingerprint
          stored in this cache, if they are equal, we keep m_local_instances,
          m_instance_cache and m_subsingleton_cache.

          New local instances added using methods type_context::push_local and type_context::push_let will
          be ignored.

       2) If lctx doesn't have one, we clear m_local_instances, m_instance_cache and m_subsingleton_cache.
          We also traverse lctx and collect the local instances.

          The methods type_context::push_local and type_context::push_let will flush the cache
          whenever new local instances are pushed into the local context.

          m_instance_cache and m_subsingleton_cache are flushed before the cache is returned to the
          cache manager. */
    optional<unsigned>            m_instance_fingerprint;
    list<pair<name, expr>>        m_local_instances;
    instance_cache                m_instance_cache;
    subsingleton_cache            m_subsingleton_cache;

    pos_info_provider const *     m_pip{nullptr};
    optional<pos_info>            m_ci_pos;

    /* Options */

    /* Maximum search depth when performing type class resolution. */
    unsigned                      m_ci_max_depth;
    /* See issue #1226 */
    unsigned                      m_nat_offset_cnstr_threshold;

    friend class type_context;
    friend class type_context_cache_manager;
    friend struct instance_synthesizer;
    void init(local_context const & lctx);
    bool is_transparent(transparency_mode m, declaration const & d);
    optional<declaration> is_transparent(transparency_mode m, name const & n);
    bool is_aux_recursor(name const & n);
public:
    /** When use_bi == true, the cache for inferred types take binder information into account.
        See comment above for infer_cache. */
    type_context_cache(environment const & env, options const & opts, bool use_bi = false);
    environment const & env() const { return m_env; }

    options const & get_options() const { return m_options; }

    /** \brief Auxiliary object used to set position information for the type class resolution trace. */
    class scope_pos_info {
        type_context_cache &      m_owner;
        pos_info_provider const * m_old_pip;
        optional<pos_info>        m_old_pos;
    public:
        scope_pos_info(type_context_cache & o, pos_info_provider const * pip, expr const & pos_ref);
        ~scope_pos_info();
    };
};

typedef std::shared_ptr<type_context_cache> type_context_cache_ptr;

/* \brief Type context cache managers are thread local data that we use
   to try to reuse type_context_cache objects */
class type_context_cache_manager {
    type_context_cache_ptr m_cache_ptr;
    unsigned               m_reducibility_fingerprint;
    unsigned               m_instance_fingerprint;
    environment            m_env;
    unsigned               m_max_depth;
    bool                   m_use_bi;
    type_context_cache_ptr release();
public:
    type_context_cache_manager(bool use_bi = false):m_use_bi(use_bi) {}
    type_context_cache_ptr mk(environment const & env, options const & o);
    void recycle(type_context_cache_ptr const & ptr);
};

class type_context : public abstract_type_context {
    typedef type_context_cache_ptr cache_ptr;
    typedef type_context_cache_manager cache_manager;
    typedef buffer<optional<level>> tmp_uassignment;
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

      *** Temporary metavariable Offsets ***

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
      term `t'`, the `is_def_eq` predicate takes offsets as parameters.
      That is, `is_def_eq(k_1, t_1, k_2, t_2)` checks whether
      the terms `lift k_1 t_1` and `lift k_2 t_2` are definitionally equal
      without constructing these terms explicitly.

      Remark: when assigning `(k_1, ?x) := (k_2, t)` where `?x` is a temporary metavariable
      and `k_1` and `k_2` are offsets, we update the array entry `idx(?x) + k_1` with
      `(lift k_2 t)`.

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

      To be able to use temporary metavariables, the type_context must
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

      Thus, to avoid these problems, when the `type_context` is in TMP mode, we do not
      assign regular metavariables. In TMP mode, regular metavariables are always treated
      as opaque constants.

      *** Applications ***
      Here we assume the `is_def_eq` general form is

      lctx | (a_1, k_1, t_1) =?= (a_2, k_2, t_2)

      where `lctx` is the local context for the temporary metavariables occurring in `t_i`;
      `a_i` is a flag indicating whether metavariables occurring in `t_i` can be assigned or not;
      `k_i` is the offset for the metavariables occurring in `t_i`.
      The local context `lctx` is only relevant for `t_i` is `a_i` is set to true.
      `lctx`, `k_i` are only relevant if we are in TMP mode. We use `lctx` to validate
      whether an assignment to a temporary metavariable is valid or not.

      We use the following shorthands

      `(unify) t =?= s` denotes `_ | (true, 0, t) =?= (true, 0, s)`
      `(match) t =?= s` denotes `_ | (true, 0, t) =?= (false, 0, s)`
      `(pure) t =?= s` denotes `_ | (false, 0, t) =?= (false, 0, s)`
      `(tmp-match) lctx | (k, t) =?= s` denotes `lctx | (true, k, t) =?= (false, 0, s)`
      `(nested-tmp-match) lctx | (k', t) =?= (k, s)` denotes `lctx | (true, k', t) =?= (false, k, s)`
      `(tmp-unify) lctx | t =?= s` denotes `lctx | (true, 0, t) =?= (true, 0, s)`

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
      It takes a `type_context` `ctx` as argument.
      We use `(tmp-match) lctx | (k, t) =?= s` where `k` is the number of
      temporary metavariables in `ctx` when invoked the `app_builder`, and the `lctx` is
      `ctx.lctx()`

      - Simplifier and Ematcher. They solve nested matching problems.
      In versions <= 3.3, we use the `tmp_type_context` hack to be able
      to use multiple temporary assignments. Now, we use a single tmp assignment
      and offsets. We set `k` as the number of temporary metavariables we had
      before we create a new matching problem. Thus, we use `(tmp-match) lctx | (k, t) =?= s`.
      Note that, `s` does not contain temporary metavariables. It is a term from the current goal.

      - (Internal) Type class resolution: we use temporary metavariables and unification.
      Before trying to synthesize `?m : C a_1 ... a_n`,
      we use a preprocessing step that creates `C a_1' ... a_n'` where `a_i'` contains
      only fresh new temporary metavariables. So, no offsets are needed since
      we don't use pre-allocated temporary metavars. Thus, we use
      `(tmp-unify) lctx | t =?= s` where `lctx` is the local context for `?m`.

      - (Internal) Recursive function unfolding during `is_def_eq`.
      (This feature is also not available in versions <= 3.3).
      When unfolding recursive functions during `is_def_eq`,
      we don't want to expose the internal recursors used when
      compiling recursive applications. Thus, we use "refl"
      equational lemmas produced by the equation compiler.
      We are essentially using the equational lemma to
      perform a delta reduction while we are solvind a
      unification/matching problem.
      We use `(nested-tmp-match) lctx | (k', t) =?= (k, s)`
      where `lctx` is `this.lctx()`, `k'` is the number of temporary metavariable in `this`,
      `t` is the left-hand-side of the "refl" equational lemma,
      and `k` is the current offset associated with `s`.
      If `s` is on the left (right) hand side of the
      current `is_def_eq` call, then we use the current left (right) offset.

      - (Internal) Unification hints. For versions <= 3.3, we used a
      custom and very basic matching procedure to implement
      this feature. This created several stability problems
      and counterintuitive behavior. We use temporary
      metavariables and matching.
      We also use `(nested-tmp-match) lctx | (k', t) =?= (k, s)`.
      This case is very similar to the previous one.
    */

    /* This class supports temporary meta-variables "mode". In this "tmp" mode,
       is_metavar_decl_ref and is_univ_metavar_decl_ref are treated as opaque constants,
       and temporary metavariables (idx_metavar) are treated as metavariables,
       and their assignment is stored at m_tmp_eassignment and m_tmp_uassignment.

       m_tmp_eassignment and m_tmp_uassignment store assignment for temporary/idx metavars

       These assignments are only used during type class resolution and matching operations.
       They are references to stack allocated buffers provided by customers.
       They are nullptr if type_context is not in tmp_mode. */
    struct tmp_data {
        tmp_uassignment & m_uassignment;
        tmp_eassignment & m_eassignment;
        /* m_tmp_mvar_local_context contains m_lctx when tmp mode is activated.
           This is the context for all temporary meta-variables. */
        local_context     m_mvar_lctx;
        /* undo/trail stack for m_tmp_uassignment/m_tmp_eassignment */
        tmp_trail         m_trail;
        tmp_data(tmp_uassignment & uassignment, tmp_eassignment & eassignment, local_context const & lctx):
            m_uassignment(uassignment), m_eassignment(eassignment), m_mvar_lctx(lctx) {}
    };
private:
    typedef buffer<scope_data> scopes;
    typedef list<pair<name, expr>> local_instances;
    metavar_context    m_mctx;
    local_context      m_lctx;
    cache_manager *    m_cache_manager;
    cache_ptr          m_cache;
    local_instances    m_local_instances;
    /* We only cache results when m_used_assignment is false */
    bool               m_used_assignment;
    transparency_mode  m_transparency_mode;
    /* m_in_is_def_eq is a temporary flag set to true in the beginning of is_def_eq. */
    bool               m_in_is_def_eq;
    /* m_is_def_eq_depth is only used for tracing purposes */
    unsigned           m_is_def_eq_depth;
    /* Stack of backtracking point (aka scope) */
    scopes             m_scopes;
    tmp_data *         m_tmp_data;
    /* If m_approximate == true, then enable approximate higher-order unification
       even if we are not in tmp_mode

       Users:
       - elaborator
       - apply and rewrite tactics use it by default (it can be disabled).
    */
    bool               m_approximate;

    /* If m_zeta, then use zeta-reduction (i.e., expand let-expressions at whnf) */
    bool               m_zeta{true};

    /* If m_update, then metavariables can be assigned by is_def_eq and similar methods.
       This is used to implement nd_is_def_eq (non-destructive is_def_eq predicate. */
    bool               m_update{true};

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
    unification_hints          m_uhints;

    std::function<bool(expr const & e)> const * m_unfold_pred; // NOLINT
    std::function<bool(name const & e)> const * m_transparency_pred; // NOLINT

    static bool is_equiv_cache_target(expr const & e1, expr const & e2) {
        return !has_metavar(e1) && !has_metavar(e2) && (get_weight(e1) > 1 || get_weight(e2) > 1);
    }
    equiv_manager & get_equiv_cache() { return m_cache->m_equiv_manager[static_cast<unsigned>(m_transparency_mode)]; }
    bool is_cached_equiv(expr const & e1, expr const & e2) {
        return is_equiv_cache_target(e1, e2) && get_equiv_cache().is_equiv(e1, e2);
    }
    void cache_equiv(expr const & e1, expr const & e2) {
        if (is_equiv_cache_target(e1, e2)) get_equiv_cache().add_equiv(e1, e2);
    }

    type_context_cache::failure_cache & get_failure_cache() { return m_cache->m_failure_cache[static_cast<unsigned>(m_transparency_mode)]; }
    void cache_failure(expr const & t, expr const & s);
    bool is_cached_failure(expr const & t, expr const & s);

    void init_local_instances();
    void flush_instance_cache();
    void update_local_instances(expr const & new_local, expr const & new_type);

    projection_info const * is_projection(expr const & e);
    optional<expr> reduce_projection_core(projection_info const * info, expr const & e);

    type_context(type_context_cache_ptr const & ptr, metavar_context const & mctx, local_context const & lctx,
                 transparency_mode m);
public:
    type_context(environment const & env, options const & o, metavar_context const & mctx, local_context const & lctx,
                 transparency_mode m = transparency_mode::Reducible);
    type_context(environment const & env, options const & o, local_context const & lctx,
                 transparency_mode m = transparency_mode::Reducible):
        type_context(env, o, metavar_context(), lctx, m) {}
    type_context(environment const & env, transparency_mode m = transparency_mode::Reducible):
        type_context(env, options(), metavar_context(), local_context(), m) {}
    type_context(environment const & env, options const & o, transparency_mode m = transparency_mode::Reducible):
        type_context(env, o, metavar_context(), local_context(), m) {}
    type_context(environment const & env, options const & o, metavar_context const & mctx, local_context const & lctx,
                 type_context_cache_manager & manager, transparency_mode m = transparency_mode::Reducible);
    virtual ~type_context();

    virtual environment const & env() const override { return m_cache->m_env; }
    options const & get_options() const { return m_cache->m_options; }
    local_context const & lctx() const { return m_lctx; }
    metavar_context const & mctx() const { return m_mctx; }
    expr mk_metavar_decl(local_context const & ctx, expr const & type) { return m_mctx.mk_metavar_decl(ctx, type); }
    expr mk_metavar_decl(name const & pp_n, local_context const & ctx, expr const & type) { return m_mctx.mk_metavar_decl(pp_n, ctx, type); }
    level mk_univ_metavar_decl() { return m_mctx.mk_univ_metavar_decl(); }

    name get_unused_name(name const & prefix, unsigned & idx) const { return m_lctx.get_unused_name(prefix, idx); }
    name get_unused_name(name const & suggestion) const { return m_lctx.get_unused_name(suggestion); }

    /* note: mctx must be a descendant of m_mctx */
    void set_mctx(metavar_context const & mctx) { m_mctx = mctx; }
    /* note: env must be a descendant of m_env */
    void set_env(environment const & env);

    /* Set the instance fingerprint of the current local context.

       \remark After this method is invoked we cannot push local instances anymore
       using the method push_local. */
    void set_instance_fingerprint();

    bool is_def_eq(level const & l1, level const & l2);
    virtual expr whnf(expr const & e) override;
    virtual expr infer(expr const & e) override;
    virtual expr check(expr const & e) override;
    virtual bool is_def_eq(expr const & e1, expr const & e2) override;

    virtual expr relaxed_whnf(expr const & e) override;
    virtual bool relaxed_is_def_eq(expr const & e1, expr const & e2) override;

    /** Non destructive is_def_eq (i.e., metavariables cannot be assigned) */
    bool nd_is_def_eq(level const & l1, level const & l2) {
        flet<bool> no_update(m_update, false);
        return is_def_eq(l1, l2);
    }

    /** Non destructive is_def_eq (i.e., metavariables cannot be assigned) */
    bool nd_is_def_eq(expr const & e1, expr const & e2) {
        flet<bool> no_update(m_update, false);
        return is_def_eq(e1, e2);
    }

    /** Non destructive relaxed_is_def_eq (i.e., metavariables cannot be assigned) */
    bool nd_relaxed_is_def_eq(expr const & e1, expr const & e2) {
        flet<bool> no_update(m_update, false);
        return relaxed_is_def_eq(e1, e2);
    }

    optional<expr> is_stuck_projection(expr const & e);
    virtual optional<expr> is_stuck(expr const &) override;

    virtual expr push_local(name const & pp_name, expr const & type, binder_info const & bi = binder_info()) override;
    virtual expr push_local_from_binding(expr const & e) {
        lean_assert(is_binding(e));
        return push_local(binding_name(e), binding_domain(e), binding_info(e));
    }

    virtual void pop_local() override;
    virtual bool has_local_pp_name(name const & pp_name) override {
        return static_cast<bool>(m_lctx.m_user_name2idxs.find(pp_name));
    }
    virtual expr abstract_locals(expr const & e, unsigned num_locals, expr const * locals) override;

    /** Similar to whnf, but invokes the given predicate before unfolding constant symbols in the head.
        If pred(e') is false, then the method will not unfold definition in the head of e', and will return e'.
        This method is useful when we want to normalize the expression until we get a particular symbol as the head symbol. */
    expr whnf_head_pred(expr const & e, std::function<bool(expr const &)> const & pred); // NOLINT
    optional<expr> reduce_aux_recursor(expr const & e);
    optional<expr> reduce_large_elim_recursor(expr const & e);
    optional<expr> reduce_projection(expr const & e);
    optional<expr> norm_ext(expr const & e) { return env().norm_ext()(e, *this); }
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

    optional<expr> expand_macro(expr const & e);

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
        transparency_scope(type_context & ctx, transparency_mode m):
            flet<transparency_mode>(ctx.m_transparency_mode, m) {
        }
    };

    struct approximate_scope : public flet<bool> {
        approximate_scope(type_context & ctx, bool approx = true):
            flet<bool>(ctx.m_approximate, approx) {}
    };

    struct zeta_scope : public flet<bool> {
        zeta_scope(type_context & ctx, bool val):
            flet<bool>(ctx.m_zeta, val) {}
    };

    struct nozeta_scope : public zeta_scope {
        nozeta_scope(type_context & ctx):zeta_scope(ctx, false) {}
    };

    struct full_postponed_scope : public flet<bool> {
        full_postponed_scope(type_context & ctx, bool full = true):
            flet<bool>(ctx.m_full_postponed, full) {}
    };

    struct relaxed_scope {
        transparency_scope m_transparency_scope;
        zeta_scope         m_zeta_scope;
        relaxed_scope(type_context & ctx):
            m_transparency_scope(ctx, transparency_mode::All),
            m_zeta_scope(ctx, true) {}
    };

    /* --------------------------
       Temporary assignment mode.
       It is used when performing type class resolution and matching.
       -------------------------- */
public:
    struct tmp_mode_scope {
        type_context &          m_ctx;
        buffer<optional<level>> m_tmp_uassignment;
        buffer<optional<expr>>  m_tmp_eassignment;
        tmp_data *              m_old_data;
        tmp_data                m_data;
        tmp_mode_scope(type_context & ctx, unsigned next_uidx = 0, unsigned next_midx = 0):
            m_ctx(ctx), m_old_data(ctx.m_tmp_data), m_data(m_tmp_uassignment, m_tmp_eassignment, ctx.lctx()) {
            m_tmp_uassignment.resize(next_uidx, none_level());
            m_tmp_eassignment.resize(next_midx, none_expr());
            m_ctx.m_tmp_data = &m_data;
        }
        ~tmp_mode_scope() {
            m_ctx.m_tmp_data = m_old_data;
        }
    };
    struct tmp_mode_scope_with_data {
        type_context & m_ctx;
        tmp_data *     m_old_data;
        tmp_mode_scope_with_data(type_context & ctx, tmp_data & data):
            m_ctx(ctx), m_old_data(ctx.m_tmp_data) {
            m_ctx.m_tmp_data = &data;
        }
        ~tmp_mode_scope_with_data() {
            m_ctx.m_tmp_data = m_old_data;
        }
    };
    bool in_tmp_mode() const { return m_tmp_data != nullptr; }
    void ensure_num_tmp_mvars(unsigned num_uvars, unsigned num_mvars);
    optional<level> get_tmp_uvar_assignment(unsigned idx) const;
    optional<expr> get_tmp_mvar_assignment(unsigned idx) const;
    optional<level> get_tmp_assignment(level const & l) const;
    optional<expr> get_tmp_assignment(expr const & e) const;
    level mk_tmp_univ_mvar();
    expr mk_tmp_mvar(expr const & type);

    /* Helper class to reset m_used_assignment flag */
    class reset_used_assignment {
        type_context & m_ctx;
        bool           m_old_used_assignment;
    public:
        reset_used_assignment(type_context & ctx):
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
    optional<expr> unfold_definition(expr const & e);
    optional<expr> try_unfold_definition(expr const & e);
    bool should_unfold_macro(expr const & e);
    expr whnf_core(expr const & e, bool iota_proj_reduce);
    optional<declaration> is_transparent(transparency_mode m, name const & n);
    optional<declaration> is_transparent(name const & n);
    bool use_zeta() const;

private:
    pair<local_context, expr> revert_core(buffer<expr> & to_revert, local_context const & ctx,
                                          expr const & type, bool preserve_to_revert_order);
    expr revert_core(buffer<expr> & to_revert, expr const & mvar, bool preserve_to_revert_order);
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
       1- `l` is a temporary universe metavariable and type_context is in tmp mode, OR
       2- `l` is a regular universe metavariable an type_context is not in tmp_mode. */
    bool is_mode_mvar(level const & l) const;
    /* Return true iff
       1- `e` is a temporary metavariable and type_context is in tmp mode, OR
       2- `e` is a regular metavariable an type_context is not in tmp_mode. */
    bool is_mode_mvar(expr const & e) const;

    bool is_assigned(level const & l) const;
    bool is_assigned(expr const & e) const;
    optional<level> get_assignment(level const & l) const;
    optional<expr> get_assignment(expr const & e) const;
    void assign(level const & u, level const & l);
    void assign(expr const & m, expr const & v);
    level instantiate_mvars(level const & l);
    expr instantiate_mvars(expr const & e, bool postpone_push_delayed = false);
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
    expr infer_local(expr const & e);
    expr infer_metavar(expr const & e);
    expr infer_constant(expr const & e);
    expr infer_macro(expr const & e);
    expr infer_lambda(expr e);
    optional<level> get_level_core(expr const & A);
    level get_level(expr const & A);
    expr infer_pi(expr e);
    expr infer_app(expr const & e);
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
        friend class type_context;
        type_context & m_owner;
        bool           m_keep;
        unsigned       m_postponed_sz;
    public:
        scope(type_context & o):m_owner(o), m_keep(false), m_postponed_sz(o.m_postponed.size()) { m_owner.push_scope(); }
        ~scope() { m_owner.m_postponed.resize(m_postponed_sz); if (!m_keep) m_owner.pop_scope(); }
        void commit() { m_postponed_sz = m_owner.m_postponed.size(); m_owner.commit_scope(); m_keep = true; }
    };
    bool process_postponed(scope const & s);
    bool approximate();
    expr try_zeta(expr const & e);
    expr expand_let_decls(expr const & e);
    friend struct check_assignment_fn;
    optional<expr> check_assignment(buffer<expr> const & locals, expr const & mvar, expr v);
    bool process_assignment(expr const & m, expr const & v);

    optional<declaration> is_delta(expr const & e);
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
    bool is_def_eq_args(expr const & e1, expr const & e2);
    bool is_def_eq_eta(expr const & e1, expr const & e2);
    bool is_def_eq_proof_irrel(expr const & e1, expr const & e2);
    optional<expr> elim_delayed_abstraction(expr const & e);
    lbool quick_is_def_eq(expr const & e1, expr const & e2);
    bool try_unification_hint(unification_hint const & h, expr const & e1, expr const & e2);
    bool try_unification_hints(expr const & e1, expr const & e2);
    bool is_productive(expr const & e);
    expr reduce_if_productive(expr const & t);
    lbool is_def_eq_delta(expr const & t, expr const & s);
    lbool is_def_eq_proj(expr t, expr s);
    optional<pair<expr, expr>> find_unsynth_metavar(expr const & e);
    bool mk_nested_instance(expr const & m, expr const & m_type);
    friend class unification_hint_fn;

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
        type_context & m_ctx;
        buffer<expr>   m_locals;

        /* \brief Return true iff all locals in m_locals are let-decls */
        bool all_let_decls() const;
    public:
        tmp_locals(type_context & ctx):m_ctx(ctx) {}
        ~tmp_locals();

        type_context & ctx() { return m_ctx; }

        expr push_local(name const & pp_name, expr const & type, binder_info const & bi = binder_info()) {
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

class tmp_type_context : public abstract_type_context {
    type_context &          m_ctx;
    buffer<optional<level>> m_tmp_uassignment;
    buffer<optional<expr>>  m_tmp_eassignment;
    type_context::tmp_data  m_tmp_data;
public:
    tmp_type_context(type_context & ctx, unsigned num_umeta = 0, unsigned num_emeta = 0);
    type_context & ctx() const { return m_ctx; }

    virtual environment const & env() const override { return m_ctx.env(); }
    virtual expr infer(expr const & e) override;
    virtual expr whnf(expr const & e) override;
    virtual bool is_def_eq(expr const & e1, expr const & e2) override;

    expr mk_lambda(buffer<expr> const & locals, expr const & e);
    expr mk_pi(buffer<expr> const & locals, expr const & e);
    expr mk_lambda(expr const & local, expr const & e);
    expr mk_pi(expr const & local, expr const & e);
    expr mk_lambda(std::initializer_list<expr> const & locals, expr const & e);
    expr mk_pi(std::initializer_list<expr> const & locals, expr const & e);

    bool is_prop(expr const & e);
    void assign(expr const & m, expr const & v);

    level mk_tmp_univ_mvar();
    expr mk_tmp_mvar(expr const & type);
    bool is_uassigned(unsigned i) const;
    bool is_eassigned(unsigned i) const;
    void clear_eassignment();
    expr instantiate_mvars(expr const & e);
};

/** Create a formatting function that can 'decode' metavar_decl_refs and local_decl_refs
    with declarations stored in mctx and lctx */
std::function<format(expr const &)>
mk_pp_ctx(environment const & env, options const & opts, metavar_context const & mctx, local_context const & lctx);

/** Create a formatting function that can 'decode' metavar_decl_refs and local_decl_refs
    with declarations stored in ctx */
std::function<format(expr const &)>
mk_pp_ctx(type_context const & ctx);

void initialize_type_context();
void finalize_type_context();
}
