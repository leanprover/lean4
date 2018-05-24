/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic
import init.control.combinators
import init.meta.interactive_base

open lean3
open lean3.parser

local postfix `?`:9001 := optional
local postfix *:9001 := many

namespace tactic
/- allows metavars -/
meta def i_to_expr (q : pexpr) : tactic expr :=
to_expr q tt

/- allow metavars and no subgoals -/
meta def i_to_expr_no_subgoals (q : pexpr) : tactic expr :=
to_expr q tt ff

/- doesn't allows metavars -/
meta def i_to_expr_strict (q : pexpr) : tactic expr :=
to_expr q ff

/- Auxiliary version of i_to_expr for apply-like tactics.
   This is a workaround for comment
      https://github.com/leanprover/lean/issues/1342#issuecomment-307912291
   at issue #1342.

   In interactive mode, given a tactic

        apply f

   we want the apply tactic to create all metavariables. The following
   definition will return `@f` for `f`. That is, it will **not** create
   metavariables for implicit arguments.

   Before we added `i_to_expr_for_apply`, the tactic

       apply le_antisymm

   would first elaborate `le_antisymm`, and create

       @le_antisymm ?m_1 ?m_2 ?m_3 ?m_4

   The type class resolution problem
        ?m_2 : weak_order ?m_1
   by the elaborator since ?m_1 is not assigned yet, and the problem is
   discarded.

   Then, we would invoke `apply_core`, which would create two
   new metavariables for the explicit arguments, and try to unify the resulting
   type with the current target. After the unification,
   the metavariables ?m_1, ?m_3 and ?m_4 are assigned, but we lost
   the information about the pending type class resolution problem.

   With `i_to_expr_for_apply`, `le_antisymm` is elaborate into `@le_antisymm`,
   the apply_core tactic creates all metavariables, and solves the ones that
   can be solved by type class resolution.

   Another possible fix: we modify the elaborator to return pending
   type class resolution problems, and store them in the tactic_state.
-/
meta def i_to_expr_for_apply (q : pexpr) : tactic expr :=
let aux (n : name) : tactic expr := do
  p ← resolve_name n,
  match p with
  | (expr.const c []) := do r ← mk_const c, save_type_info r q, return r
  | _                 := i_to_expr p
in match q with
| (expr.const c [])    := aux c
| (expr.local_const c) := aux c
| _                    := i_to_expr q

namespace interactive
open interactive interactive.types expr

/--
itactic: parse a nested "interactive" tactic. That is, parse
  `{` tactic `}`
-/
meta def itactic : Type :=
tactic unit

meta def propagate_tags (tac : tactic unit) : tactic unit :=
do tag ← get_main_tag,
   if tag = [] then tac
   else focus1 $ do
     tac,
     gs ← get_goals,
     when (bnot gs.empty) $ do
       new_tag ← get_main_tag,
       when new_tag.empty $ with_enable_tags (set_main_tag tag)

meta def concat_tags (tac : tactic (list (name × expr))) : tactic unit :=
mcond tags_enabled
  (do in_tag ← get_main_tag,
      r ← tac,
      /- remove assigned metavars -/
      r ← r.mfilter $ λ ⟨n, m⟩, bnot <$> is_assigned m,
      match r with
      | [(_, m)] := set_tag m in_tag /- if there is only new subgoal, we just propagate `in_tag` -/
      | _        := r.mfor (λ ⟨n, m⟩, set_tag m (n::in_tag)))
  (tac >> skip)

/--
If the current goal is a Pi/forall `∀ x : t, u` (resp. `let x := t in u`) then `intro` puts `x : t` (resp. `x := t`) in the local context. The new subgoal target is `u`.

If the goal is an arrow `t → u`, then it puts `h : t` in the local context and the new goal target is `u`.

If the goal is neither a Pi/forall nor begins with a let binder, the tactic `intro` applies the tactic `whnf` until an introduction can be applied or the goal is not head reducible. In the latter case, the tactic fails.
-/
meta def intro : parse ident_? → tactic unit
| none     := propagate_tags (intro1 >> skip)
| (some h) := propagate_tags (tactic.intro h >> skip)

/--
Similar to `intro` tactic. The tactic `intros` will keep introducing new hypotheses until the goal target is not a Pi/forall or let binder.

The variant `intros h₁ ... hₙ` introduces `n` new hypotheses using the given identifiers to name them.
-/
meta def intros : parse ident_* → tactic unit
| [] := propagate_tags (tactic.intros >> skip)
| hs := propagate_tags (intro_lst hs >> skip)

/--
The tactic `introv` allows the user to automatically introduce the variables of a theorem and explicitly name the hypotheses involved. The given names are used to name non-dependent hypotheses.

Examples:
```
example : ∀ a b : nat, a = b → b = a :=
begin
  introv h,
  exact h.symm
end
```
The state after `introv h` is
```
a b : ℕ,
h : a = b
⊢ b = a
```
```
example : ∀ a b : nat, a = b → ∀ c, b = c → a = c :=
begin
  introv h₁ h₂,
  exact h₁.trans h₂
end
```
The state after `introv h₁ h₂` is
```
a b : ℕ,
h₁ : a = b,
c : ℕ,
h₂ : b = c
⊢ a = c
```
-/
meta def introv (ns : parse ident_*) : tactic unit :=
propagate_tags (tactic.introv ns >> return ())

/--
The tactic `rename h₁ h₂` renames hypothesis `h₁` to `h₂` in the current local context.
-/
meta def rename (h₁ h₂ : parse ident) : tactic unit :=
propagate_tags (tactic.rename h₁ h₂)

/--
The `apply` tactic tries to match the current goal against the conclusion of the type of term. The argument term should be a term well-formed in the local context of the main goal. If it succeeds, then the tactic returns as many subgoals as the number of premises that have not been fixed by type inference or type class resolution. Non-dependent premises are added before dependent ones.

The `apply` tactic uses higher-order pattern matching, type class resolution, and first-order unification with dependent types.
-/
meta def apply (q : parse texpr) : tactic unit :=
concat_tags (do h ← i_to_expr_for_apply q, tactic.apply h)

/--
Similar to the `apply` tactic, but does not reorder goals.
-/
meta def fapply (q : parse texpr) : tactic unit :=
concat_tags (i_to_expr_for_apply q >>= tactic.fapply)

/--
Similar to the `apply` tactic, but only creates subgoals for non-dependent premises that have not been fixed by type inference or type class resolution.
-/
meta def eapply (q : parse texpr) : tactic unit :=
concat_tags (i_to_expr_for_apply q >>= tactic.eapply)

/--
Similar to the `apply` tactic, but allows the user to provide a `apply_cfg` configuration object.
-/
meta def apply_with (q : parse parser.pexpr) (cfg : apply_cfg) : tactic unit :=
concat_tags (do e ← i_to_expr_for_apply q, tactic.apply e cfg)

/--
Similar to the `apply` tactic, but uses matching instead of unification.
`apply_match t` is equivalent to `apply_with t {unify := ff}`
-/
meta def mapply (q : parse texpr) : tactic unit :=
concat_tags (do e ← i_to_expr_for_apply q, tactic.apply e {unify := ff})

/--
This tactic tries to close the main goal `... ⊢ t` by generating a term of type `t` using type class resolution.
-/
meta def apply_instance : tactic unit :=
tactic.apply_instance

/--
This tactic behaves like `exact`, but with a big difference: the user can put underscores `_` in the expression as placeholders for holes that need to be filled, and `refine` will generate as many subgoals as there are holes.

Note that some holes may be implicit. The type of each hole must either be synthesized by the system or declared by an explicit type ascription like `(_ : nat → Prop)`.
-/
meta def refine (q : parse texpr) : tactic unit :=
tactic.refine q

/--
This tactic looks in the local context for a hypothesis whose type is equal to the goal target. If it finds one, it uses it to prove the goal, and otherwise it fails.
-/
meta def assumption : tactic unit :=
tactic.assumption

/-- Try to apply `assumption` to all goals. -/
meta def assumption' : tactic unit :=
tactic.any_goals tactic.assumption

private meta def change_core (e : expr) : option expr → tactic unit
| none     := tactic.change e
| (some h) :=
  do num_reverted : ℕ ← revert h,
     expr.pi n bi d b ← target,
     tactic.change $ expr.pi n bi e b,
     intron num_reverted

/--
`change u` replaces the target `t` of the main goal to `u` provided that `t` is well formed with respect to the local context of the main goal and `t` and `u` are definitionally equal.

`change u at h` will change a local hypothesis to `u`.

`change t with u at h1 h2 ...` will replace `t` with `u` in all the supplied hypotheses (or `*`), or in the goal if no `at` clause is specified, provided that `t` and `u` are definitionally equal.
-/
meta def change (q : parse texpr) : parse (tk "with" *> texpr)? → parse location → tactic unit
| none (loc.ns [none]) := do e ← i_to_expr q, change_core e none
| none (loc.ns [some h]) := do eq ← i_to_expr q, eh ← get_local h, change_core eq (some eh)
| none _ := fail "change-at does not support multiple locations"
| (some w) l :=
  do u ← mk_meta_univ,
     ty ← mk_meta_var (sort u),
     eq ← i_to_expr ``(%%q : %%ty),
     ew ← i_to_expr ``(%%w : %%ty),
     let repl := λe : expr, e.replace (λ a n, if a = eq then some ew else none),
     l.try_apply
       (λh, do e ← infer_type h, change_core (repl e) (some h))
       (do g ← target, change_core (repl g) none)

/--
This tactic provides an exact proof term to solve the main goal. If `t` is the goal and `p` is a term of type `u` then `exact p` succeeds if and only if `t` and `u` can be unified.
-/
meta def exact (q : parse texpr) : tactic unit :=
do tgt : expr ← target,
   i_to_expr_strict ``(%%q : %%tgt) >>= tactic.exact
/--
Like `exact`, but takes a list of terms and checks that all goals are discharged after the tactic.
-/
meta def exacts : parse pexpr_list_or_texpr → tactic unit
| [] := done
| (t :: ts) := exact t >> exacts ts

/--
A synonym for `exact` that allows writing `have/suffices/show ..., from ...` in tactic mode.
-/
meta def «from» := exact

/--
`revert h₁ ... hₙ` applies to any goal with hypotheses `h₁` ... `hₙ`. It moves the hypotheses and their dependencies to the target of the goal. This tactic is the inverse of `intro`.
-/
meta def revert (ids : parse ident*) : tactic unit :=
propagate_tags (do hs ← ids.mmap tactic.get_local, revert_lst hs, skip)

private meta def resolve_name' (n : name) : tactic expr :=
do {
  p ← resolve_name n,
  match p with
  | expr.const n _ := mk_const n -- create metavars for universe levels
  | _              := i_to_expr p }

/- Version of to_expr that tries to bypass the elaborator if `p` is just a constant or local constant.
   This is not an optimization, by skipping the elaborator we make sure that no unwanted resolution is used.
   Example: the elaborator will force any unassigned ?A that must have be an instance of (has_one ?A) to nat.
   Remark: another benefit is that auxiliary temporary metavariables do not appear in error messages. -/
meta def to_expr' (p : pexpr) : tactic expr :=
match p with
| (const c [])    := do new_e ← resolve_name' c, save_type_info new_e p, return new_e
| (local_const c) := do new_e ← resolve_name' c, save_type_info new_e p, return new_e
| _               := i_to_expr p

precedence `generalizing` : 0

private meta def collect_hyps_uids : tactic name_set :=
do ctx ← local_context,
   return $ ctx.foldl (λ r h, r.insert h.local_uniq_name) mk_name_set

private meta def revert_new_hyps (input_hyp_uids : name_set) : tactic unit :=
do ctx ← local_context,
   let to_revert := ctx.foldr (λ h r, if input_hyp_uids.contains h.local_uniq_name then r else h::r) [],
   tag ← get_main_tag,
   m   ← revert_lst to_revert,
   set_main_tag (mk_num_name `_case m :: tag)

/--
Apply `t` to main goal, and revert any new hypothesis in the generated goals,
and tag generated goals when using supported tactics such as: `induction`, `apply`, `cases`, `constructor`, ...

This tactic is useful for writing robust proof scripts that are not sensitive
to the name generation strategy used by `t`.

```
example (n : ℕ) : n = n :=
begin
  with_cases { induction n },
  case nat.zero { reflexivity },
  case nat.succ : n' ih { reflexivity }
end
```

TODO(Leo): improve docstring
-/
meta def with_cases (t : itactic) : tactic unit :=
with_enable_tags $ focus1 $ do
  input_hyp_uids ← collect_hyps_uids,
  t,
  all_goals (revert_new_hyps input_hyp_uids)

private meta def get_type_name (e : expr) : tactic name :=
do e_type ← infer_type e >>= whnf,
   (const I ls) ← return $ get_app_fn e_type,
   return I

private meta def generalize_arg_p_aux : pexpr → parser (pexpr × name)
| (app (app (macro _ [const `eq _ ]) h) (local_const x)) := pure (h, x)
| _ := fail "parse error"


private meta def generalize_arg_p : parser (pexpr × name) :=
with_desc "expr = id" $ parser.pexpr 0 >>= generalize_arg_p_aux

/--
`generalize : e = x` replaces all occurrences of `e` in the target with a new hypothesis `x` of the same type.

`generalize h : e = x` in addition registers the hypothesis `h : e = x`.
-/
meta def generalize (h : parse ident?) (_ : parse $ tk ":") (p : parse generalize_arg_p) : tactic unit :=
propagate_tags $
do let (p, x) := p,
   e ← i_to_expr p,
   some h ← pure h | tactic.generalize e x >> intro1 >> skip,
   tgt ← target,
   -- if generalizing fails, fall back to not replacing anything
   tgt' ← do {
     ⟨tgt', _⟩ ← solve_aux tgt (tactic.generalize e x >> target),
     to_expr ``(Π x, %%e = x → %%(tgt'.binding_body.lift_vars 0 1))
   } <|> to_expr ``(Π x, %%e = x → %%tgt),
   t ← assert h tgt',
   swap,
   exact ``(%%t %%e rfl),
   intro x,
   intro h

meta def cases_arg_p : parser (option name × pexpr) :=
with_desc "(id :)? expr" $ do
  t ← texpr,
  match t with
  | (local_const x) :=
    (tk ":" *> do t ← texpr, pure (some x, t)) <|> pure (none, t)
  | _ := pure (none, t)

/--
  Given the initial tag `in_tag` and the cases names produced by `induction` or `cases` tactic,
  update the tag of the new subgoals.
-/
private meta def set_cases_tags (in_tag : tag) (rs : list name) : tactic unit :=
do te ← tags_enabled,
   gs ← get_goals,
   match gs with
   | [g] := when te (set_tag g in_tag) -- if only one goal was produced, we should not make the tag longer
   | _   := do
     let tgs : list (name × expr) := rs.map₂ (λ n g, (n, g)) gs,
     if te
     then tgs.mfor (λ ⟨n, g⟩, set_tag g (n::in_tag))
          /- If `induction/cases` is not in a `with_cases` block, we still set tags using `_case_simple` to make
             sure we can use the `case` notation.
             ```
             induction h,
             case c { ... }
             ```
          -/
     else tgs.mfor (λ ⟨n, g⟩, with_enable_tags (set_tag g (`_case_simple::n::[])))

private meta def set_induction_tags (in_tag : tag) (rs : list (name × list expr × list (name × expr))) : tactic unit :=
set_cases_tags in_tag (rs.map (λ e, e.1))

/--
Assuming `x` is a variable in the local context with an inductive type, `induction x` applies induction on `x` to the main goal, producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor and an inductive hypothesis is added for each recursive argument to the constructor. If the type of an element in the local context depends on `x`, that element is reverted and reintroduced afterward, so that the inductive hypothesis incorporates that hypothesis as well.

For example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `induction n` produces one goal with hypothesis `h : P 0` and target `Q 0`, and one goal with hypotheses `h : P (nat.succ a)` and `ih₁ : P a → Q a` and target `Q (nat.succ a)`. Here the names `a` and `ih₁` ire chosen automatically.

`induction e`, where `e` is an expression instead of a variable, generalizes `e` in the goal, and then performs induction on the resulting variable.

`induction e with y₁ ... yₙ`, where `e` is a variable or an expression, specifies that the sequence of names `y₁ ... yₙ` should be used for the arguments to the constructors and inductive hypotheses, including implicit arguments. If the list does not include enough names for all of the arguments, additional names are generated automatically. If too many names are given, the extra ones are ignored. Underscores can be used in the list, in which case the corresponding names are generated automatically. Note that for long sequences of names, the `case` tactic provides a more convenient naming mechanism.

`induction e using r` allows the user to specify the principle of induction that should be used. Here `r` should be a theorem whose result type must be of the form `C t`, where `C` is a bound variable and `t` is a (possibly empty) sequence of bound variables

`induction e generalizing z₁ ... zₙ`, where `z₁ ... zₙ` are variables in the local context, generalizes over `z₁ ... zₙ` before applying the induction but then introduces them in each goal. In other words, the net effect is that each inductive hypothesis is generalized.

`induction h : t` will introduce an equality of the form `h : t = C x y`, asserting that the input term is equal to the current constructor case, to the context.
-/
meta def induction (hp : parse cases_arg_p) (rec_name : parse using_ident) (ids : parse with_ident_list)
  (revert : parse $ (tk "generalizing" *> ident*)?) : tactic unit :=
do in_tag ← get_main_tag,
focus1 $ do {
    -- process `h : t` case
    e ← (match hp with
         | (some h, p) := do
           x ← get_unused_name,
           generalize h () (p, x),
           get_local x
         | (none, p) := i_to_expr p),
   -- generalize major premise
   e ← if e.is_local_constant then pure e
       else tactic.generalize e >> intro1,

   -- generalize major premise args
   (e, newvars, locals) ← do {
      none ← pure rec_name | pure (e, [], []),
      t ← infer_type e,
      t ← whnf_ginductive t,
      const n _ ← pure t.get_app_fn | pure (e, [], []),
      env ← get_env,
      tt ← pure $ env.is_inductive n | pure (e, [], []),
      let (locals, nonlocals) := (t.get_app_args.drop $ env.inductive_num_params n).partition
        (λ arg : expr, arg.is_local_constant),
      _ :: _ ← pure nonlocals | pure (e, [], []),

      n ← tactic.revert e,
      newvars ← nonlocals.mmap $ λ arg, do {
        n ← revert_kdeps arg,
        tactic.generalize arg,
        h ← intro1,
        intron n,
        -- now try to clear hypotheses that may have been abstracted away
        let locals := arg.fold [] (λ e _ acc, if e.is_local_constant then e::acc else acc),
        locals.mfor (try ∘ clear),
        pure h
      },
      intron (n-1),
      e ← intro1,
      pure (e, newvars, locals)
   },

   -- revert `generalizing` params
   n ← (revert.get_or_else []).mmap tactic.get_local >>= revert_lst,

   rs ← tactic.induction e ids rec_name,
   all_goals $ do {
     intron n,
     /- TODO: the following command is not reliable since it is based on user facing name.
        Moreover, we are not storing them anymore on local constants. -/
     -- clear_lst (newvars.map local_pp_name),
     (e::locals).mfor (try ∘ clear) },

   set_induction_tags in_tag rs }

private meta def is_case_simple_tag : tag → bool
| (`_case_simple :: _) := tt
| _                    := ff

private meta def is_case_tag : tag → option nat
| (name.mk_numeral `_case n :: _) := some n
| _                               := none

private meta def tag_match (t : tag) (pre : list name) : bool :=
pre.is_prefix_of t.reverse &&
((is_case_tag t).is_some || is_case_simple_tag t)

private meta def collect_tagged_goals (pre : list name) : tactic (list expr) :=
do gs ← get_goals,
   gs.mfoldr (λ g r, do
      t ← get_tag g,
      if tag_match t pre then return (g::r) else return r)
      []

private meta def find_tagged_goal_aux (pre : list name) : tactic expr :=
do gs ← collect_tagged_goals pre,
   match gs with
   | []  := fail ("invalid `case`, there is no goal tagged with prefix " ++ to_string pre)
   | [g] := return g
   | gs  := do
     tags : list (list name) ← gs.mmap get_tag,
     fail ("invalid `case`, there is more than one goal tagged with prefix " ++ to_string pre ++ ", matching tags: " ++ to_string tags)

private meta def find_tagged_goal (pre : list name) : tactic expr :=
match pre with
| [] := do g::gs ← get_goals, return g
| _  :=
  find_tagged_goal_aux pre
  <|>
  -- try to resolve constructor names, and try again
  do env ← get_env,
     pre ← pre.mmap (λ id,
           (do r_id ← resolve_constant id,
               if (env.inductive_type_of r_id).is_none then return id
               else return r_id)
            <|> return id),
     find_tagged_goal_aux pre

private meta def find_case (goals : list expr) (ty : name) (idx : nat) (num_indices : nat) : option expr → expr → option (expr × expr)
| case e := if e.has_meta_var then match e with
  | (mvar _ _ _)    :=
    do case ← case,
       guard $ e ∈ goals,
       pure (case, e)
  | (app _ _)    :=
    let idx :=
     (match e.get_app_fn with
      | const (name.mk_string ty' rec) _ :=
        guard (ty' = ty) >>
        (match mk_simple_name rec with
         | `drec := some idx | `rec := some idx
         -- indices + major premise
         | `dcases_on := some (idx + num_indices + 1) | `cases_on := some (idx + num_indices + 1)
         | _ := none)
      | _ := none) in
    (match idx with
     | none := list.foldl (<|>) (find_case case e.get_app_fn) $ e.get_app_args.map (find_case case)
     | some idx :=
       let args := e.get_app_args in
       do arg ← args.nth idx,
         args.enum.foldl
           (λ acc ⟨i, arg⟩, match acc with
             | some _ := acc
             | _      := if i ≠ idx then find_case none arg else none)
           -- start recursion with likely case
           (find_case (some arg) arg))
  | (lam _ _ _ e) := find_case case e
  | (macro n args) := list.foldl (<|>) none $ args.map (find_case case)
  | _             := none
  else none

private meta def rename_lams : expr → list name → tactic unit
| (lam n _ _ e) (n'::ns) := (rename n n' >> rename_lams e ns) <|> rename_lams e (n'::ns)
| _             _        := skip

/--
Focuses on the `induction`/`cases`/`with_cases` subgoal corresponding to the given tag prefix, optionally renaming introduced locals.

```
example (n : ℕ) : n = n :=
begin
  induction n,
  case nat.zero { reflexivity },
  case nat.succ : a ih { reflexivity }
end
```
-/
meta def case (pre : parse ident_*) (ids : parse $ (tk ":" *> ident_*)?) (tac : itactic) : tactic unit :=
do g   ← find_tagged_goal pre,
   tag ← get_tag g,
   let ids := ids.get_or_else [],
   match is_case_tag tag with
   | some n := do
      let m := ids.length,
      gs ← get_goals,
      set_goals $ g :: gs.filter (≠ g),
      intro_lst ids,
      when (m < n) $ intron (n - m),
      solve1 tac
   | none   :=
     match is_case_simple_tag tag with
     | tt :=
       /- Use the old `case` implementation -/
       do r         ← result,
          env       ← get_env,
          [ctor_id] ← return pre,
          ctor      ← resolve_constant ctor_id
                      <|> fail ("'" ++ to_string ctor_id ++ "' is not a constructor"),
          ty        ← (env.inductive_type_of ctor).to_monad
                      <|> fail ("'" ++ to_string ctor ++ "' is not a constructor"),
          let ctors := env.constructors_of ty,
          let idx   := env.inductive_num_params ty + /- motive -/ 1 +
                       list.index_of ctor ctors,
          /- Remark: we now use `find_case` just to locate the `lambda` used in `rename_lams`.
             The goal is now located using tags. -/
          (case, _) ← (find_case [g] ty idx (env.inductive_num_indices ty) none r ).to_monad
                      <|> fail "could not find open goal of given case",
          gs        ← get_goals,
          set_goals $ g :: gs.filter (≠ g),
          rename_lams case ids,
          solve1 tac
     | ff := failed

/--
Assuming `x` is a variable in the local context with an inductive type, `destruct x` splits the main goal, producing one goal for each constructor of the inductive type, in which `x` is assumed to be a general instance of that constructor. In contrast to `cases`, the local context is unchanged, i.e. no elements are reverted or introduced.

For example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `destruct n` produces one goal with target `n = 0 → Q n`, and one goal with target `∀ (a : ℕ), (λ (w : ℕ), n = w → Q n) (nat.succ a)`. Here the name `a` is chosen automatically.
-/
meta def destruct (p : parse texpr) : tactic unit :=
i_to_expr p >>= tactic.destruct

meta def cases_core (e : expr) (ids : list name := []) : tactic unit :=
do in_tag ← get_main_tag,
focus1 $ do
 rs ← tactic.cases e ids,
 set_cases_tags in_tag rs

/--
Assuming `x` is a variable in the local context with an inductive type, `cases x` splits the main goal, producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor. If the type of an element in the local context depends on `x`, that element is reverted and reintroduced afterward, so that the case split affects that hypothesis as well.

For example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `cases n` produces one goal with hypothesis `h : P 0` and target `Q 0`, and one goal with hypothesis `h : P (nat.succ a)` and target `Q (nat.succ a)`. Here the name `a` is chosen automatically.

`cases e`, where `e` is an expression instead of a variable, generalizes `e` in the goal, and then cases on the resulting variable.

`cases e with y₁ ... yₙ`, where `e` is a variable or an expression, specifies that the sequence of names `y₁ ... yₙ` should be used for the arguments to the constructors, including implicit arguments. If the list does not include enough names for all of the arguments, additional names are generated automatically. If too many names are given, the extra ones are ignored. Underscores can be used in the list, in which case the corresponding names are generated automatically.

`cases h : e`, where `e` is a variable or an expression, performs cases on `e` as above, but also adds a hypothesis `h : e = ...` to each hypothesis, where `...` is the constructor instance for that particular case.
-/
meta def cases : parse cases_arg_p → parse with_ident_list → tactic unit
| (none,   p) ids := do
  e ← i_to_expr p,
  cases_core e ids
| (some h, p) ids := do
  x   ← get_unused_name,
  generalize h () (p, x),
  hx  ← get_local x,
  cases_core hx ids

private meta def try_cases_for_types (type_names : list name) (at_most_one : bool) : tactic unit :=
any_hyp $ λ h, do
  I ← expr.get_app_fn <$> (infer_type h >>= head_beta),
  guard I.is_constant,
  guard (I.const_name ∈ type_names),
  tactic.focus1 (cases_core h >> if at_most_one then do n ← num_goals, guard (n <= 1) else skip)

/--
`cases_type I` applies the `cases` tactic to a hypothesis `h : (I ...)`
`cases_type I_1 ... I_n` applies the `cases` tactic to a hypothesis `h : (I_1 ...)` or ... or `h : (I_n ...)`
`cases_type* I` is shorthand for `focus1 { repeat { cases_type I } }`
`cases_type! I` only applies `cases` if the number of resulting subgoals is <= 1.

Example: The following tactic destructs all conjunctions and disjunctions in the current goal.
```
cases_type* or and
```
-/
meta def cases_type (one : parse $ (tk "!")?) (rec : parse $ (tk "*")?) (type_names : parse ident*) : tactic unit :=
do type_names ← type_names.mmap resolve_constant,
   if rec.is_none
   then try_cases_for_types type_names (bnot one.is_none)
   else tactic.focus1 $ tactic.repeat $ try_cases_for_types type_names (bnot one.is_none)

/--
Tries to solve the current goal using a canonical proof of `true`, or the `reflexivity` tactic, or the `contradiction` tactic.
-/
meta def trivial : tactic unit :=
tactic.triv <|> fail "trivial tactic failed"

/--
`iterate { t }` repeatedly applies tactic `t` until `t` fails. `iterate { t }` always succeeds.

`iterate n { t }` applies `t` `n` times.
-/
meta def iterate (n : parse small_nat?) (t : itactic) : tactic unit :=
match n with
| none   := tactic.iterate t
| some n := iterate_exactly n t

/--
`repeat { t }` applies `t` to each goal. If the application succeeds,
the tactic is applied recursively to all the generated subgoals until it eventually fails.
The recursion stops in a subgoal when the tactic has failed to make progress.
The tactic `repeat { t }` never fails.
-/
meta def repeat : itactic → tactic unit :=
tactic.repeat

/--
`try { t }` tries to apply tactic `t`, but succeeds whether or not `t` succeeds.
-/
meta def try : itactic → tactic unit :=
tactic.try

/--
A do-nothing tactic that always succeeds.
-/
meta def skip : tactic unit :=
tactic.skip

/--
`solve1 { t }` applies the tactic `t` to the main goal and fails if it is not solved.
-/
meta def solve1 : itactic → tactic unit :=
tactic.solve1

/--
`abstract id { t }` tries to use tactic `t` to solve the main goal. If it succeeds, it abstracts the goal as an independent definition or theorem with name `id`. If `id` is omitted, a name is generated automatically.
-/
meta def abstract (id : parse ident?) (tac : itactic) : tactic unit :=
tactic.abstract tac id

/--
`all_goals { t }` applies the tactic `t` to every goal, and succeeds if each application succeeds.
-/
meta def all_goals : itactic → tactic unit :=
tactic.all_goals

/--
`any_goals { t }` applies the tactic `t` to every goal, and succeeds if at least one application succeeds.
-/
meta def any_goals : itactic → tactic unit :=
tactic.any_goals

/--
`focus { t }` temporarily hides all goals other than the first, applies `t`, and then restores the other goals. It fails if there are no goals.
-/
meta def focus (tac : itactic) : tactic unit :=
tactic.focus1 tac

/--
This tactic displays the current state in the tracing buffer.
-/
meta def trace_state : tactic unit :=
tactic.trace_state

/--
`trace a` displays `a` in the tracing buffer.
-/
meta def trace {α : Type} [has_to_tactic_format α] (a : α) : tactic unit :=
tactic.trace a

end interactive
end tactic
