/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.rewrite_tactic init.meta.simp_tactic
import init.meta.smt.congruence_closure init.category.combinators
import init.meta.interactive_base init.meta.derive init.meta.match_tactic
import init.meta.congr_tactic

open lean
open lean.parser

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
  end
in match q with
| (expr.const c [])          := aux c
| (expr.local_const c _ _ _) := aux c
| _                          := i_to_expr q
end

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
      | _        := r.mmap' (λ ⟨n, m⟩, set_tag m (n::in_tag))
      end)
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
propagate_tags (do hs ← mmap tactic.get_local ids, revert_lst hs, skip)

private meta def resolve_name' (n : name) : tactic expr :=
do {
  p ← resolve_name n,
  match p with
  | expr.const n _ := mk_const n -- create metavars for universe levels
  | _              := i_to_expr p
  end
}

/- Version of to_expr that tries to bypass the elaborator if `p` is just a constant or local constant.
   This is not an optimization, by skipping the elaborator we make sure that no unwanted resolution is used.
   Example: the elaborator will force any unassigned ?A that must have be an instance of (has_one ?A) to nat.
   Remark: another benefit is that auxiliary temporary metavariables do not appear in error messages. -/
meta def to_expr' (p : pexpr) : tactic expr :=
match p with
| (const c [])          := do new_e ← resolve_name' c, save_type_info new_e p, return new_e
| (local_const c _ _ _) := do new_e ← resolve_name' c, save_type_info new_e p, return new_e
| _                     := i_to_expr p
end

@[derive has_reflect]
meta structure rw_rule :=
(pos  : pos)
(symm : bool)
(rule : pexpr)

meta def get_rule_eqn_lemmas (r : rw_rule) : tactic (list name) :=
let aux (n : name) : tactic (list name) := do {
  p ← resolve_name n,
  -- unpack local refs
  let e := p.erase_annotations.get_app_fn.erase_annotations,
  match e with
  | const n _ := get_eqn_lemmas_for tt n
  | _         := return []
  end } <|> return [] in
match r.rule with
| const n _           := aux n
| local_const n _ _ _ := aux n
| _                   := return []
end

private meta def rw_goal (cfg : rewrite_cfg) (rs : list rw_rule) : tactic unit :=
rs.mmap' $ λ r, do
 save_info r.pos,
 eq_lemmas ← get_rule_eqn_lemmas r,
 orelse'
   (do e ← to_expr' r.rule, rewrite_target e {symm := r.symm, ..cfg})
   (eq_lemmas.mfirst $ λ n, do e ← mk_const n, rewrite_target e {symm := r.symm, ..cfg})
   (eq_lemmas.empty)

private meta def uses_hyp (e : expr) (h : expr) : bool :=
e.fold ff $ λ t _ r, r || to_bool (t = h)

private meta def rw_hyp (cfg : rewrite_cfg) : list rw_rule → expr → tactic unit
| []      hyp := skip
| (r::rs) hyp := do
  save_info r.pos,
  eq_lemmas ← get_rule_eqn_lemmas r,
  orelse'
    (do e ← to_expr' r.rule, when (not (uses_hyp e hyp)) $ rewrite_hyp e hyp {symm := r.symm, ..cfg} >>= rw_hyp rs)
    (eq_lemmas.mfirst $ λ n, do e ← mk_const n, rewrite_hyp e hyp {symm := r.symm, ..cfg} >>= rw_hyp rs)
    (eq_lemmas.empty)

meta def rw_rule_p (ep : parser pexpr) : parser rw_rule :=
rw_rule.mk <$> cur_pos <*> (option.is_some <$> (with_desc "←" (tk "←" <|> tk "<-"))?) <*> ep

@[derive has_reflect]
meta structure rw_rules_t :=
(rules   : list rw_rule)
(end_pos : option pos)

-- accepts the same content as `pexpr_list_or_texpr`, but with correct goal info pos annotations
meta def rw_rules : parser rw_rules_t :=
(tk "[" *>
 rw_rules_t.mk <$> sep_by (skip_info (tk ",")) (set_goal_info_pos $ rw_rule_p (parser.pexpr 0))
               <*> (some <$> cur_pos <* set_goal_info_pos (tk "]")))
<|> rw_rules_t.mk <$> (list.ret <$> rw_rule_p texpr) <*> return none

private meta def rw_core (rs : parse rw_rules) (loca : parse location) (cfg : rewrite_cfg) : tactic unit :=
match loca with
| loc.wildcard := loca.try_apply (rw_hyp cfg rs.rules) (rw_goal cfg rs.rules)
| _            := loca.apply (rw_hyp cfg rs.rules) (rw_goal cfg rs.rules)
end >> try (reflexivity reducible)
    >> (returnopt rs.end_pos >>= save_info <|> skip)

/--
`rewrite e` applies identity `e` as a rewrite rule to the target of the main goal. If `e` is preceded by left arrow (`←` or `<-`), the rewrite is applied in the reverse direction. If `e` is a defined constant, then the equational lemmas associated with `e` are used. This provides a convenient way to unfold `e`.

`rewrite [e₁, ..., eₙ]` applies the given rules sequentially.

`rewrite e at l` rewrites `e` at location(s) `l`, where `l` is either `*` or a list of hypotheses in the local context. In the latter case, a turnstile `⊢` or `|-` can also be used, to signify the target of the goal.
-/
meta def rewrite (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : tactic unit :=
propagate_tags (rw_core q l cfg)

/--
An abbreviation for `rewrite`.
-/
meta def rw (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : tactic unit :=
propagate_tags (rw_core q l cfg)

/--
`rewrite` followed by `assumption`.
-/
meta def rwa (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : tactic unit :=
rewrite q l cfg >> try assumption

/--
A variant of `rewrite` that uses the unifier more aggressively, unfolding semireducible definitions.
-/
meta def erewrite (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {md := semireducible}) : tactic unit :=
propagate_tags (rw_core q l cfg)

/--
An abbreviation for `erewrite`.
-/
meta def erw (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {md := semireducible}) : tactic unit :=
propagate_tags (rw_core q l cfg)

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
| (app (app (macro _ [const `eq _ ]) h) (local_const x _ _ _)) := pure (h, x)
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
  | (local_const x _ _ _) :=
    (tk ":" *> do t ← texpr, pure (some x, t)) <|> pure (none, t)
  | _ := pure (none, t)
  end

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
     then tgs.mmap' (λ ⟨n, g⟩, set_tag g (n::in_tag))
          /- If `induction/cases` is not in a `with_cases` block, we still set tags using `_case_simple` to make
             sure we can use the `case` notation.
             ```
             induction h,
             case c { ... }
             ```
          -/
     else tgs.mmap' (λ ⟨n, g⟩, with_enable_tags (set_tag g (`_case_simple::n::[])))
   end

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
    e ← match hp with
       | (some h, p) := do
         x ← get_unused_name,
         generalize h () (p, x),
         get_local x
       | (none, p) := i_to_expr p
       end,

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
        locals.mmap' (try ∘ clear),
        pure h
      },
      intron (n-1),
      e ← intro1,
      pure (e, newvars, locals)
   },

   -- revert `generalizing` params
   n ← mmap tactic.get_local (revert.get_or_else []) >>= revert_lst,

   rs ← tactic.induction e ids rec_name,
   all_goals $ do {
     intron n,
     clear_lst (newvars.map local_pp_name),
     (e::locals).mmap' (try ∘ clear) },

   set_induction_tags in_tag rs }

private meta def is_case_simple_tag : tag → bool
| (`_case_simple :: _) := tt
| _                    := ff

private meta def is_case_tag : tag → option nat
| (name.mk_numeral n `_case :: _) := some n.val
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
   end

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
end

private meta def find_case (goals : list expr) (ty : name) (idx : nat) (num_indices : nat) : option expr → expr → option (expr × expr)
| case e := if e.has_meta_var then match e with
  | (mvar _ _ _)    :=
    do case ← case,
       guard $ e ∈ goals,
       pure (case, e)
  | (app _ _)    :=
    let idx :=
      match e.get_app_fn with
      | const (name.mk_string rec ty') _ :=
        guard (ty' = ty) >>
        match mk_simple_name rec with
        | `drec := some idx | `rec := some idx
        -- indices + major premise
        | `dcases_on := some (idx + num_indices + 1) | `cases_on := some (idx + num_indices + 1)
        | _ := none
        end
      | _ := none
      end in
    match idx with
    | none := list.foldl (<|>) (find_case case e.get_app_fn) $ e.get_app_args.map (find_case case)
    | some idx :=
      let args := e.get_app_args in
      do arg ← args.nth idx,
         args.enum.foldl
           (λ acc ⟨i, arg⟩, match acc with
             | some _ := acc
             | _      := if i ≠ idx then find_case none arg else none
             end)
           -- start recursion with likely case
           (find_case (some arg) arg)
    end
  | (lam _ _ _ e) := find_case case e
  | (macro n args) := list.foldl (<|>) none $ args.map (find_case case)
  | _             := none
  end else none

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
     end
   end

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

private meta def find_matching_hyp (ps : list pattern) : tactic expr :=
any_hyp $ λ h, do
  type ← infer_type h,
  ps.mfirst $ λ p, do
  match_pattern p type,
  return h

/--
`cases_matching p` applies the `cases` tactic to a hypothesis `h : type` if `type` matches the pattern `p`.
`cases_matching [p_1, ..., p_n]` applies the `cases` tactic to a hypothesis `h : type` if `type` matches one of the given patterns.
`cases_matching* p` more efficient and compact version of `focus1 { repeat { cases_matching p } }`. It is more efficient because the pattern is compiled once.

Example: The following tactic destructs all conjunctions and disjunctions in the current goal.
```
cases_matching* [_ ∨ _, _ ∧ _]
```
-/
meta def cases_matching (rec : parse $ (tk "*")?) (ps : parse pexpr_list_or_texpr) : tactic unit :=
do ps ← ps.mmap pexpr_to_pattern,
   if rec.is_none
   then find_matching_hyp ps >>= cases_core
   else tactic.focus1 $ tactic.repeat $ find_matching_hyp ps >>= cases_core

/-- Shorthand for `cases_matching` -/
meta def casesm (rec : parse $ (tk "*")?) (ps : parse pexpr_list_or_texpr) : tactic unit :=
cases_matching rec ps

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
tactic.triv <|> tactic.reflexivity <|> tactic.contradiction <|> fail "trivial tactic failed"

/--
Closes the main goal using `sorry`.
-/
meta def admit : tactic unit := tactic.admit

/--
Closes the main goal using `sorry`.
-/
meta def «sorry» : tactic unit := tactic.admit

/--
The contradiction tactic attempts to find in the current local context a hypothesis that is equivalent to an empty inductive type (e.g. `false`), a hypothesis of the form `c_1 ... = c_2 ...` where `c_1` and `c_2` are distinct constructors, or two contradictory hypotheses.
-/
meta def contradiction : tactic unit :=
tactic.contradiction

/--
`iterate { t }` repeatedly applies tactic `t` until `t` fails. `iterate { t }` always succeeds.

`iterate n { t }` applies `t` `n` times.
-/
meta def iterate (n : parse small_nat?) (t : itactic) : tactic unit :=
match n with
| none   := tactic.iterate t
| some n := iterate_exactly n t
end

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

private meta def assume_core (n : name) (ty : pexpr) :=
do t ← target,
    when (not $ t.is_pi ∨ t.is_let) whnf_target,
    t ← target,
    when (not $ t.is_pi ∨ t.is_let) $
      fail "assume tactic failed, Pi/let expression expected",
    ty ← i_to_expr ty,
    unify ty t.binding_domain,
    intro_core n >> skip

/--
Assuming the target of the goal is a Pi or a let, `assume h : t` unifies the type of the binder with `t` and introduces it with name `h`, just like `intro h`. If `h` is absent, the tactic uses the name `this`. If `t` is omitted, it will be inferred.

`assume (h₁ : t₁) ... (hₙ : tₙ)` introduces multiple hypotheses. Any of the types may be omitted, but the names must be present.
-/
meta def «assume» : parse (sum.inl <$> (tk ":" *> texpr) <|> sum.inr <$> parse_binders tac_rbp) → tactic unit
| (sum.inl ty)      := assume_core `this ty
| (sum.inr binders) :=
  binders.mmap' $ λ b, assume_core b.local_pp_name b.local_type

/--
`have h : t := p` adds the hypothesis `h : t` to the current goal if `p` a term of type `t`. If `t` is omitted, it will be inferred.

`have h : t` adds the hypothesis `h : t` to the current goal and opens a new subgoal with target `t`. The new subgoal becomes the main goal. If `t` is omitted, it will be replaced by a fresh metavariable.

If `h` is omitted, the name `this` is used.
-/
meta def «have» (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : tactic unit :=
let h := h.get_or_else `this in
match q₁, q₂ with
| some e, some p := do
  t ← i_to_expr e,
  v ← i_to_expr ``(%%p : %%t),
  tactic.assertv h t v
| none, some p := do
  p ← i_to_expr p,
  tactic.note h none p
| some e, none := i_to_expr e >>= tactic.assert h
| none, none := do
  u ← mk_meta_univ,
  e ← mk_meta_var (sort u),
  tactic.assert h e
end >> skip

/--
`let h : t := p` adds the hypothesis `h : t := p` to the current goal if `p` a term of type `t`. If `t` is omitted, it will be inferred.

`let h : t` adds the hypothesis `h : t := ?M` to the current goal and opens a new subgoal `?M : t`. The new subgoal becomes the main goal. If `t` is omitted, it will be replaced by a fresh metavariable.

If `h` is omitted, the name `this` is used.
-/
meta def «let» (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : tactic unit :=
let h := h.get_or_else `this in
match q₁, q₂ with
| some e, some p := do
  t ← i_to_expr e,
  v ← i_to_expr ``(%%p : %%t),
  tactic.definev h t v
| none, some p := do
  p ← i_to_expr p,
  tactic.pose h none p
| some e, none := i_to_expr e >>= tactic.define h
| none, none := do
  u ← mk_meta_univ,
  e ← mk_meta_var (sort u),
  tactic.define h e
end >> skip

/--
`suffices h : t` is the same as `have h : t, tactic.swap`. In other words, it adds the hypothesis `h : t` to the current goal and opens a new subgoal with target `t`.
-/
meta def «suffices» (h : parse ident?) (t : parse (tk ":" *> texpr)?) : tactic unit :=
«have» h t none >> tactic.swap

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

/--
`existsi e` will instantiate an existential quantifier in the target with `e` and leave the instantiated body as the new target. More generally, it applies to any inductive type with one constructor and at least two arguments, applying the constructor with `e` as the first argument and leaving the remaining arguments as goals.

`existsi [e₁, ..., eₙ]` iteratively does the same for each expression in the list.
-/
meta def existsi : parse pexpr_list_or_texpr → tactic unit
| []      := return ()
| (p::ps) := i_to_expr p >>= tactic.existsi >> existsi ps

/--
This tactic applies to a goal such that its conclusion is an inductive type (say `I`). It tries to apply each constructor of `I` until it succeeds.
-/
meta def constructor : tactic unit :=
concat_tags tactic.constructor

/--
Similar to `constructor`, but only non-dependent premises are added as new goals.
-/
meta def econstructor : tactic unit :=
concat_tags tactic.econstructor

/--
Applies the first constructor when the type of the target is an inductive data type with two constructors.
-/
meta def left : tactic unit :=
concat_tags tactic.left

/--
Applies the second constructor when the type of the target is an inductive data type with two constructors.
-/
meta def right : tactic unit :=
concat_tags tactic.right

/--
Applies the constructor when the type of the target is an inductive data type with one constructor.
-/
meta def split : tactic unit :=
concat_tags tactic.split

private meta def constructor_matching_aux (ps : list pattern) : tactic unit :=
do t ← target, ps.mfirst (λ p, match_pattern p t), constructor

meta def constructor_matching (rec : parse $ (tk "*")?) (ps : parse pexpr_list_or_texpr) : tactic unit :=
do ps ← ps.mmap pexpr_to_pattern,
   if rec.is_none then constructor_matching_aux ps
   else tactic.focus1 $ tactic.repeat $ constructor_matching_aux ps

/--
Replaces the target of the main goal by `false`.
-/
meta def exfalso : tactic unit :=
tactic.exfalso

/--
The `injection` tactic is based on the fact that constructors of inductive data types are injections. That means that if `c` is a constructor of an inductive datatype, and if `(c t₁)` and `(c t₂)` are two terms that are equal then  `t₁` and `t₂` are equal too.

If `q` is a proof of a statement of conclusion `t₁ = t₂`, then injection applies injectivity to derive the equality of all arguments of `t₁` and `t₂` placed in the same positions. For example, from `(a::b) = (c::d)` we derive `a=c` and `b=d`. To use this tactic `t₁` and `t₂` should be constructor applications of the same constructor.

Given `h : a::b = c::d`, the tactic `injection h` adds two new hypothesis with types `a = c` and `b = d` to the main goal. The tactic `injection h with h₁ h₂` uses the names `h₁` and `h₂` to name the new hypotheses.
-/
meta def injection (q : parse texpr) (hs : parse with_ident_list) : tactic unit :=
do e ← i_to_expr q, tactic.injection_with e hs, try assumption

/--
`injections with h₁ ... hₙ` iteratively applies `injection` to hypotheses using the names `h₁ ... hₙ`.
-/
meta def injections (hs : parse with_ident_list) : tactic unit :=
do tactic.injections_with hs, try assumption

end interactive

meta structure simp_config_ext extends simp_config :=
(discharger : tactic unit := failed)

section mk_simp_set
open expr interactive.types

@[derive has_reflect]
meta inductive simp_arg_type : Type
| all_hyps : simp_arg_type
| except   : name  → simp_arg_type
| expr     : pexpr → simp_arg_type

meta def simp_arg : parser simp_arg_type :=
(tk "*" *> return simp_arg_type.all_hyps) <|> (tk "-" *> simp_arg_type.except <$> ident) <|> (simp_arg_type.expr <$> texpr)

meta def simp_arg_list : parser (list simp_arg_type) :=
(tk "*" *> return [simp_arg_type.all_hyps]) <|> list_of simp_arg <|> return []

private meta def resolve_exception_ids (all_hyps : bool) : list name → list name → list name → tactic (list name × list name)
| []        gex hex := return (gex.reverse, hex.reverse)
| (id::ids) gex hex := do
  p ← resolve_name id,
  let e := p.erase_annotations.get_app_fn.erase_annotations,
  match e with
  | const n _           := resolve_exception_ids ids (n::gex) hex
  | local_const n _ _ _ := when (not all_hyps) (fail $ sformat! "invalid local exception {id}, '*' was not used") >>
                           resolve_exception_ids ids gex (n::hex)
  | _                   := fail $ sformat! "invalid exception {id}, unknown identifier"
  end

/- Return (hs, gex, hex, all) -/
meta def decode_simp_arg_list (hs : list simp_arg_type) : tactic $ list pexpr × list name × list name × bool :=
do
  let (hs, ex, all) := hs.foldl
    (λ r h,
       match r, h with
       | (es, ex, all), simp_arg_type.all_hyps  := (es, ex, tt)
       | (es, ex, all), simp_arg_type.except id := (es, id::ex, all)
       | (es, ex, all), simp_arg_type.expr e    := (e::es, ex, all)
       end)
    ([], [], ff),
  (gex, hex) ← resolve_exception_ids all ex [] [],
  return (hs.reverse, gex, hex, all)

private meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

private meta def report_invalid_simp_lemma {α : Type} (n : name): tactic α :=
fail format!"invalid simplification lemma '{n}' (use command 'set_option trace.simp_lemmas true' for more details)"

private meta def check_no_overload (p : pexpr) : tactic unit :=
when p.is_choice_macro $
  match p with
  | macro _ ps :=
    fail $ to_fmt "ambiguous overload, possible interpretations" ++
           format.join (ps.map (λ p, (to_fmt p).indent 4))
  | _ := failed
  end

private meta def simp_lemmas.resolve_and_add (s : simp_lemmas) (u : list name) (n : name) (ref : pexpr) : tactic (simp_lemmas × list name) :=
do
  p ← resolve_name n,
  check_no_overload p,
  -- unpack local refs
  let e := p.erase_annotations.get_app_fn.erase_annotations,
  match e with
  | const n _           :=
    (do b ← is_valid_simp_lemma_cnst n, guard b, save_const_type_info n ref, s ← s.add_simp n, return (s, u))
    <|>
    (do eqns ← get_eqn_lemmas_for tt n, guard (eqns.length > 0), save_const_type_info n ref, s ← add_simps s eqns, return (s, u))
    <|>
    (do env ← get_env, guard (env.is_projection n).is_some, return (s, n::u))
    <|>
    report_invalid_simp_lemma n
  | _ :=
    (do e ← i_to_expr_no_subgoals p, b ← is_valid_simp_lemma e, guard b, try (save_type_info e ref), s ← s.add e, return (s, u))
    <|>
    report_invalid_simp_lemma n
  end

private meta def simp_lemmas.add_pexpr (s : simp_lemmas) (u : list name) (p : pexpr) : tactic (simp_lemmas × list name) :=
match p with
| (const c [])          := simp_lemmas.resolve_and_add s u c p
| (local_const c _ _ _) := simp_lemmas.resolve_and_add s u c p
| _                     := do new_e ← i_to_expr_no_subgoals p, s ← s.add new_e, return (s, u)
end

private meta def simp_lemmas.append_pexprs : simp_lemmas → list name → list pexpr → tactic (simp_lemmas × list name)
| s u []      := return (s, u)
| s u (l::ls) := do (s, u) ← simp_lemmas.add_pexpr s u l, simp_lemmas.append_pexprs s u ls

meta def mk_simp_set_core (no_dflt : bool) (attr_names : list name) (hs : list simp_arg_type) (at_star : bool)
                          : tactic (bool × simp_lemmas × list name) :=
do (hs, gex, hex, all_hyps) ← decode_simp_arg_list hs,
   when (all_hyps ∧ at_star ∧ not hex.empty) $ fail "A tactic of the form `simp [*, -h] at *` is currently not supported",
   s      ← join_user_simp_lemmas no_dflt attr_names,
   (s, u) ← simp_lemmas.append_pexprs s [] hs,
   s      ← if not at_star ∧ all_hyps then do
              ctx ← collect_ctx_simps,
              let ctx := ctx.filter (λ h, h.local_uniq_name ∉ hex), -- remove local exceptions
              s.append ctx
            else return s,
   -- add equational lemmas, if any
   gex ← gex.mmap (λ n, list.cons n <$> get_eqn_lemmas_for tt n),
   return (all_hyps, simp_lemmas.erase s $ gex.join, u)

meta def mk_simp_set (no_dflt : bool) (attr_names : list name) (hs : list simp_arg_type) : tactic (simp_lemmas × list name) :=
prod.snd <$> (mk_simp_set_core no_dflt attr_names hs ff)
end mk_simp_set

namespace interactive
open interactive interactive.types expr

meta def simp_core_aux (cfg : simp_config) (discharger : tactic unit) (s : simp_lemmas) (u : list name) (hs : list expr) (tgt : bool) : tactic unit :=
do to_remove ← hs.mfilter $ λ h, do {
         h_type ← infer_type h,
         (do (new_h_type, pr) ← simplify s u h_type cfg `eq discharger,
             assert h.local_pp_name new_h_type,
             mk_eq_mp pr h >>= tactic.exact >> return tt)
         <|>
         (return ff) },
   goal_simplified ← if tgt then (simp_target s u cfg discharger >> return tt) <|> (return ff) else return ff,
   guard (cfg.fail_if_unchanged = ff ∨ to_remove.length > 0 ∨ goal_simplified) <|> fail "simplify tactic failed to simplify",
   to_remove.mmap' (λ h, try (clear h))

meta def simp_core (cfg : simp_config) (discharger : tactic unit)
                   (no_dflt : bool) (hs : list simp_arg_type) (attr_names : list name)
                   (locat : loc) : tactic unit :=
match locat with
| loc.wildcard := do (all_hyps, s, u) ← mk_simp_set_core no_dflt attr_names hs tt,
                     if all_hyps then tactic.simp_all s u cfg discharger
                     else do hyps ← non_dep_prop_hyps, simp_core_aux cfg discharger s u hyps tt
| _            := do (s, u) ← mk_simp_set no_dflt attr_names hs,
                     ns ← locat.get_locals,
                     simp_core_aux cfg discharger s u ns locat.include_goal
end
>> try tactic.triv >> try (tactic.reflexivity reducible)

/--
The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or non-dependent hypotheses. It has many variants.

`simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.

`simp [h₁ h₂ ... hₙ]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and the given `hᵢ`'s, where the `hᵢ`'s are expressions. If an `hᵢ` is a defined constant `f`, then the equational lemmas associated with `f` are used. This provides a convenient way to unfold `f`.

`simp [*]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and all hypotheses.

`simp *` is a shorthand for `simp [*]`.

`simp only [h₁ h₂ ... hₙ]` is like `simp [h₁ h₂ ... hₙ]` but does not use `[simp]` lemmas

`simp [-id_1, ... -id_n]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]`, but removes the ones named `idᵢ`.

`simp at h₁ h₂ ... hₙ` simplifies the non-dependent hypotheses `h₁ : T₁` ... `hₙ : Tₙ`. The tactic fails if the target or another hypothesis depends on one of them. The token `⊢` or `|-` can be added to the list to include the target.

`simp at *` simplifies all the hypotheses and the target.

`simp * at *` simplifies target and all (non-dependent propositional) hypotheses using the other hypotheses.

`simp with attr₁ ... attrₙ` simplifies the main goal target using the lemmas tagged with any of the attributes `[attr₁]`, ..., `[attrₙ]` or `[simp]`.
-/
meta def simp (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
              (locat : parse location) (cfg : simp_config_ext := {}) : tactic unit :=
let cfg := if use_iota_eqn.is_none then cfg else {iota_eqn := tt, ..cfg} in
propagate_tags (simp_core cfg.to_simp_config cfg.discharger no_dflt hs attr_names locat)

/--
Just construct the simp set and trace it. Used for debugging.
-/
meta def trace_simp_set (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list) : tactic unit :=
do (s, _) ← mk_simp_set no_dflt attr_names hs,
   s.pp >>= trace

/--
`simp_intros h₁ h₂ ... hₙ` is similar to `intros h₁ h₂ ... hₙ` except that each hypothesis is simplified as it is introduced, and each introduced hypothesis is used to simplify later ones and the final target.

As with `simp`, a list of simplification lemmas can be provided. The modifiers `only` and `with` behave as with `simp`.
-/
meta def simp_intros (ids : parse ident_*) (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
                     (cfg : simp_intros_config := {}) : tactic unit :=
do (s, u) ← mk_simp_set no_dflt attr_names hs,
   when (¬u.empty) (fail (sformat! "simp_intros tactic does not support {u}")),
   tactic.simp_intros s u ids cfg,
   try triv >> try (reflexivity reducible)

private meta def to_simp_arg_list (es : list pexpr) : list simp_arg_type :=
es.map simp_arg_type.expr

/--
`dsimp` is similar to `simp`, except that it only uses definitional equalities.
-/
meta def dsimp (no_dflt : parse only_flag) (es : parse simp_arg_list) (attr_names : parse with_ident_list)
               (l : parse location) (cfg : dsimp_config := {}) : tactic unit :=
do (s, u) ← mk_simp_set no_dflt attr_names es,
match l with
| loc.wildcard :=
  /- Remark: we cannot revert frozen local instances.
     We disable zeta expansion because to prevent `intron n` from failing.
     Another option is to put a "marker" at the current target, and
     implement `intro_upto_marker`. -/
  do n ← revert_all,
     dsimp_target s u {zeta := ff ..cfg},
     intron n
| _ := l.apply (λ h, dsimp_hyp h s u cfg) (dsimp_target s u cfg)
end

/--
This tactic applies to a goal whose target has the form `t ~ u` where `~` is a reflexive relation, that is, a relation which has a reflexivity lemma tagged with the attribute `[refl]`. The tactic checks whether `t` and `u` are definitionally equal and then solves the goal.
-/
meta def reflexivity : tactic unit :=
tactic.reflexivity

/--
Shorter name for the tactic `reflexivity`.
-/
meta def refl : tactic unit :=
tactic.reflexivity

/--
This tactic applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation, that is, a relation which has a symmetry lemma tagged with the attribute `[symm]`. It replaces the target with `u ~ t`.
-/
meta def symmetry : tactic unit :=
tactic.symmetry

/--
This tactic applies to a goal whose target has the form `t ~ u` where `~` is a transitive relation, that is, a relation which has a transitivity lemma tagged with the attribute `[trans]`.

`transitivity s` replaces the goal with the two subgoals `t ~ s` and `s ~ u`. If `s` is omitted, then a metavariable is used instead.
-/
meta def transitivity (q : parse texpr?) : tactic unit :=
tactic.transitivity >> match q with
| none := skip
| some q :=
  do (r, lhs, rhs) ← target_lhs_rhs,
     i_to_expr q >>= unify rhs
end

/--
Proves a goal with target `s = t` when `s` and `t` are equal up to the associativity and commutativity of their binary operations.
-/
meta def ac_reflexivity : tactic unit :=
tactic.ac_refl

/--
An abbreviation for `ac_reflexivity`.
-/
meta def ac_refl : tactic unit :=
tactic.ac_refl

/--
Tries to prove the main goal using congruence closure.
-/
meta def cc : tactic unit :=
tactic.cc

/--
Given hypothesis `h : x = t` or `h : t = x`, where `x` is a local constant, `subst h` substitutes `x` by `t` everywhere in the main goal and then clears `h`.
-/
meta def subst (q : parse texpr) : tactic unit :=
i_to_expr q >>= tactic.subst >> try (tactic.reflexivity reducible)

/--
Apply `subst` to all hypotheses of the form `h : x = t` or `h : t = x`.
-/
meta def subst_vars : tactic unit :=
tactic.subst_vars

/--
`clear h₁ ... hₙ` tries to clear each hypothesis `hᵢ` from the local context.
-/
meta def clear : parse ident* → tactic unit :=
tactic.clear_lst

private meta def to_qualified_name_core : name → list name → tactic name
| n []        := fail $ "unknown declaration '" ++ to_string n ++ "'"
| n (ns::nss) := do
  curr ← return $ ns ++ n,
  env  ← get_env,
  if env.contains curr then return curr
  else to_qualified_name_core n nss

private meta def to_qualified_name (n : name) : tactic name :=
do env ← get_env,
   if env.contains n then return n
   else do
     ns ← open_namespaces,
     to_qualified_name_core n ns

private meta def to_qualified_names : list name → tactic (list name)
| []      := return []
| (c::cs) := do new_c ← to_qualified_name c, new_cs ← to_qualified_names cs, return (new_c::new_cs)

/--
Similar to `unfold`, but only uses definitional equalities.
-/
meta def dunfold (cs : parse ident*) (l : parse location) (cfg : dunfold_config := {}) : tactic unit :=
match l with
| (loc.wildcard) := do ls ← tactic.local_context,
                          n ← revert_lst ls,
                          new_cs ← to_qualified_names cs,
                          dunfold_target new_cs cfg,
                          intron n
| _              := do new_cs ← to_qualified_names cs, l.apply (λ h, dunfold_hyp cs h cfg) (dunfold_target new_cs cfg)
end

private meta def delta_hyps : list name → list name → tactic unit
| cs []      := skip
| cs (h::hs) := get_local h >>= delta_hyp cs >> delta_hyps cs hs

/--
Similar to `dunfold`, but performs a raw delta reduction, rather than using an equation associated with the defined constants.
-/
meta def delta : parse ident* → parse location → tactic unit
| cs (loc.wildcard) := do ls ← tactic.local_context,
                          n ← revert_lst ls,
                          new_cs ← to_qualified_names cs,
                          delta_target new_cs,
                          intron n
| cs l              := do new_cs ← to_qualified_names cs, l.apply (delta_hyp new_cs) (delta_target new_cs)

private meta def unfold_projs_hyps (cfg : unfold_proj_config := {}) (hs : list name) : tactic bool :=
hs.mfoldl (λ r h, do h ← get_local h, (unfold_projs_hyp h cfg >> return tt) <|> return r) ff

/--
This tactic unfolds all structure projections.
-/
meta def unfold_projs (l : parse location) (cfg : unfold_proj_config := {}) : tactic unit :=
match l with
| loc.wildcard := do ls ← local_context,
                     b₁ ← unfold_projs_hyps cfg (ls.map expr.local_pp_name),
                     b₂ ← (tactic.unfold_projs_target cfg >> return tt) <|> return ff,
                     when (not b₁ ∧ not b₂) (fail "unfold_projs failed to simplify")
| _            :=
  l.try_apply (λ h, unfold_projs_hyp h cfg)
    (tactic.unfold_projs_target cfg) <|> fail "unfold_projs failed to simplify"
end

end interactive

meta def ids_to_simp_arg_list (tac_name : name) (cs : list name) : tactic (list simp_arg_type) :=
cs.mmap $ λ c, do
  n   ← resolve_name c,
  hs  ← get_eqn_lemmas_for ff n.const_name,
  env ← get_env,
  let p := env.is_projection n.const_name,
  when (hs.empty ∧ p.is_none) (fail (sformat! "{tac_name} tactic failed, {c} does not have equational lemmas nor is a projection")),
  return $ simp_arg_type.expr (expr.const c [])

structure unfold_config extends simp_config :=
(zeta               := ff)
(proj               := ff)
(eta                := ff)
(canonize_instances := ff)
(constructor_eq     := ff)

namespace interactive
open interactive interactive.types expr

/--
Given defined constants `e₁ ... eₙ`, `unfold e₁ ... eₙ` iteratively unfolds all occurrences in the target of the main goal, using equational lemmas associated with the definitions.

As with `simp`, the `at` modifier can be used to specify locations for the unfolding.
-/
meta def unfold (cs : parse ident*) (locat : parse location) (cfg : unfold_config := {}) : tactic unit :=
do es ← ids_to_simp_arg_list "unfold" cs,
   let no_dflt := tt,
   simp_core cfg.to_simp_config failed no_dflt es [] locat

/--
Similar to `unfold`, but does not iterate the unfolding.
-/
meta def unfold1 (cs : parse ident*) (locat : parse location) (cfg : unfold_config := {single_pass := tt}) : tactic unit :=
unfold cs locat cfg

/--
If the target of the main goal is an `opt_param`, assigns the default value.
-/
meta def apply_opt_param : tactic unit :=
tactic.apply_opt_param

/--
If the target of the main goal is an `auto_param`, executes the associated tactic.
-/
meta def apply_auto_param : tactic unit :=
tactic.apply_auto_param

/--
Fails if the given tactic succeeds.
-/
meta def fail_if_success (tac : itactic) : tactic unit :=
tactic.fail_if_success tac

/--
Succeeds if the given tactic fails.
-/
meta def success_if_fail (tac : itactic) : tactic unit :=
tactic.success_if_fail tac

meta def guard_expr_eq (t : expr) (p : parse $ tk ":=" *> texpr) : tactic unit :=
do e ← to_expr p, guard (alpha_eqv t e)

/--
`guard_target t` fails if the target of the main goal is not `t`.
We use this tactic for writing tests.
-/
meta def guard_target (p : parse texpr) : tactic unit :=
do t ← target, guard_expr_eq t p

/--
`guard_hyp h := t` fails if the hypothesis `h` does not have type `t`.
We use this tactic for writing tests.
-/
meta def guard_hyp (n : parse ident) (p : parse $ tk ":=" *> texpr) : tactic unit :=
do h ← get_local n >>= infer_type, guard_expr_eq h p

/--
`match_target t` fails if target does not match pattern `t`.
-/
meta def match_target (t : parse texpr) (m := reducible) : tactic unit :=
tactic.match_target t m >> skip

/--
`by_cases (h :)? p` splits the main goal into two cases, assuming `h : p` in the first branch, and `h : ¬ p` in the second branch.

This tactic requires that `p` is decidable. To ensure that all propositions are decidable via classical reasoning, use  `local attribute classical.prop_decidable [instance]`.
-/
meta def by_cases : parse cases_arg_p → tactic unit
| (n, q) := concat_tags $ do
  p ← tactic.to_expr_strict q,
  tactic.by_cases p (n.get_or_else `h),
  pos_g :: neg_g :: rest ← get_goals,
  return [(`pos, pos_g), (`neg, neg_g)]

/--
Apply function extensionality and introduce new hypotheses.
The tactic `funext` will keep applying new the `funext` lemma until the goal target is not reducible to
```
  |-  ((fun x, ...) = (fun x, ...))
```
The variant `funext h₁ ... hₙ` applies `funext` `n` times, and uses the given identifiers to name the new hypotheses.
-/
meta def funext : parse ident_* → tactic unit
| [] := tactic.funext >> skip
| hs := funext_lst hs >> skip

/--
If the target of the main goal is a proposition `p`, `by_contradiction h` reduces the goal to proving `false` using the additional hypothesis `h : ¬ p`. If `h` is omitted, a name is generated automatically.

This tactic requires that `p` is decidable. To ensure that all propositions are decidable via classical reasoning, use  `local attribute classical.prop_decidable [instance]`.
-/
meta def by_contradiction (n : parse ident?) : tactic unit :=
tactic.by_contradiction n >> return ()

/--
An abbreviation for `by_contradiction`.
-/
meta def by_contra (n : parse ident?) : tactic unit :=
by_contradiction n

/--
Type check the given expression, and trace its type.
-/
meta def type_check (p : parse texpr) : tactic unit :=
do e ← to_expr p, tactic.type_check e, infer_type e >>= trace

/--
Fail if there are unsolved goals.
-/
meta def done : tactic unit :=
tactic.done

private meta def show_aux (p : pexpr) : list expr → list expr → tactic unit
| []      r := fail "show tactic failed"
| (g::gs) r := do
  do {set_goals [g], g_ty ← target, ty ← i_to_expr p, unify g_ty ty, set_goals (g :: r.reverse ++ gs), tactic.change ty}
  <|>
  show_aux gs (g::r)

/--
`show t` finds the first goal whose target unifies with `t`. It makes that the main goal, performs the unification, and replaces the target with the unified version of `t`.
-/
meta def «show» (q : parse texpr) : tactic unit :=
do gs ← get_goals,
   show_aux q gs []

/--
The tactic `specialize h a₁ ... aₙ` works on local hypothesis `h`. The premises of this hypothesis, either universal quantifications or non-dependent implications, are instantiated by concrete terms coming either from arguments `a₁` ... `aₙ`. The tactic adds a new hypothesis with the same name `h := h a₁ ... aₙ` and tries to clear the previous one.
-/
meta def specialize (p : parse texpr) : tactic unit :=
do e ← i_to_expr p,
   let h := expr.get_app_fn e,
   if h.is_local_constant
   then tactic.note h.local_pp_name none e >> try (tactic.clear h)
   else tactic.fail "specialize requires a term of the form `h x_1 .. x_n` where `h` appears in the local context"

meta def congr := tactic.congr

end interactive
end tactic

section add_interactive
open tactic

/- See add_interactive -/
private meta def add_interactive_aux (new_namespace : name) : list name → command
| []      := return ()
| (n::ns) := do
  env    ← get_env,
  d_name ← resolve_constant n,
  (declaration.defn _ ls ty val hints trusted) ← env.get d_name,
  (name.mk_string h _) ← return d_name,
  let new_name := `tactic.interactive <.> h,
  add_decl (declaration.defn new_name ls ty (expr.const d_name (ls.map level.param)) hints trusted),
  add_interactive_aux ns

/--
Copy a list of meta definitions in the current namespace to tactic.interactive.

This command is useful when we want to update tactic.interactive without closing the current namespace.
-/
meta def add_interactive (ns : list name) (p : name := `tactic.interactive) : command :=
add_interactive_aux p ns

meta def has_dup : tactic bool :=
do ctx ← local_context,
   let p : name_set × bool :=
       ctx.foldl (λ ⟨s, r⟩ h,
          if r then (s, r)
          else if s.contains h.local_pp_name then (s, tt)
          else (s.insert h.local_pp_name, ff))
        (mk_name_set, ff),
   return p.2

/--
Renames hypotheses with the same name.
-/
meta def dedup : tactic unit :=
mwhen has_dup $ do
  ctx ← local_context,
  n   ← revert_lst ctx,
  intron n

end add_interactive

namespace tactic
/- Helper tactic for `mk_inj_eq -/
protected meta def apply_inj_lemma : tactic unit :=
do h ← intro `h,
   some (lhs, rhs) ← expr.is_eq <$> infer_type h,
   (expr.const C _) ← return lhs.get_app_fn,
   -- We disable auto_param and opt_param support to address issue #1943
   applyc (name.mk_string "inj" C) {auto_param := ff, opt_param := ff},
   assumption

/- Auxiliary tactic for proving `I.C.inj_eq` lemmas.
   These lemmas are automatically generated by the equation compiler.
   Example:
   ```
   list.cons.inj_eq : forall h1 h2 t1 t2, (h1::t1 = h2::t2) = (h1 = h2 ∧ t1 = t2) :=
   by mk_inj_eq
   ```
-/
meta def mk_inj_eq : tactic unit :=
`[
  intros,
  /-
     We use `_root_.*` in the following tactics because
     names are resolved at tactic execution time in interactive mode.
     See PR #1913

     TODO(Leo): This is probably not the only instance of this problem.
     `[ ... ] blocks are convenient to use because they allow us to use the interactive
     mode to write non interactive tactics.
     One potential fix for this issue is to resolve names in `[ ... ] at tactic
     compilation time.
     After this issue is fixed, we should remove the `_root_.*` workaround.
  -/
  apply _root_.propext,
  apply _root_.iff.intro,
  { tactic.apply_inj_lemma },
  { intro _, try { cases_matching* _ ∧ _ }, refl <|> { congr; { assumption <|> subst_vars } } }
]
end tactic

/- Define inj_eq lemmas for inductive datatypes that were declared before `mk_inj_eq` -/

universes u v

lemma sum.inl.inj_eq {α : Type u} (β : Type v) (a₁ a₂ : α) : (@sum.inl α β a₁ = sum.inl a₂) = (a₁ = a₂) :=
by tactic.mk_inj_eq

lemma sum.inr.inj_eq (α : Type u) {β : Type v} (b₁ b₂ : β) : (@sum.inr α β b₁ = sum.inr b₂) = (b₁ = b₂) :=
by tactic.mk_inj_eq

lemma psum.inl.inj_eq {α : Sort u} (β : Sort v) (a₁ a₂ : α) : (@psum.inl α β a₁ = psum.inl a₂) = (a₁ = a₂) :=
by tactic.mk_inj_eq

lemma psum.inr.inj_eq (α : Sort u) {β : Sort v} (b₁ b₂ : β) : (@psum.inr α β b₁ = psum.inr b₂) = (b₁ = b₂) :=
by tactic.mk_inj_eq

lemma sigma.mk.inj_eq {α : Type u} {β : α → Type v} (a₁ : α) (b₁ : β a₁) (a₂ : α) (b₂ : β a₂) : (sigma.mk a₁ b₁ = sigma.mk a₂ b₂) = (a₁ = a₂ ∧ b₁ == b₂) :=
by tactic.mk_inj_eq

lemma psigma.mk.inj_eq {α : Sort u} {β : α → Sort v} (a₁ : α) (b₁ : β a₁) (a₂ : α) (b₂ : β a₂) : (psigma.mk a₁ b₁ = psigma.mk a₂ b₂) = (a₁ = a₂ ∧ b₁ == b₂) :=
by tactic.mk_inj_eq

lemma subtype.mk.inj_eq {α : Sort u} {p : α → Prop} (a₁ : α) (h₁ : p a₁) (a₂ : α) (h₂ : p a₂) : (subtype.mk a₁ h₁ = subtype.mk a₂ h₂) = (a₁ = a₂) :=
by tactic.mk_inj_eq

lemma option.some.inj_eq {α : Type u} (a₁ a₂ : α) : (some a₁ = some a₂) = (a₁ = a₂) :=
by tactic.mk_inj_eq

lemma list.cons.inj_eq {α : Type u} (h₁ : α) (t₁ : list α) (h₂ : α) (t₂ : list α) : (list.cons h₁ t₁ = list.cons h₂ t₂) = (h₁ = h₂ ∧ t₁ = t₂) :=
by tactic.mk_inj_eq

lemma nat.succ.inj_eq (n₁ n₂ : nat) : (nat.succ n₁ = nat.succ n₂) = (n₁ = n₂) :=
by tactic.mk_inj_eq
