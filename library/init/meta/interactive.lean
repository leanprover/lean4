/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.rewrite_tactic init.meta.simp_tactic
import init.meta.smt.congruence_closure init.category.combinators
import init.meta.interactive_base

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

/--
This tactic applies to a goal that is either a Pi/forall or starts with a let binder.

If the current goal is a Pi/forall `∀ x:T, U` (resp `let x:=t in U`) then intro puts `x:T` (resp `x:=t`) in the local context. The new subgoal target is `U`.

If the goal is an arrow `T → U`, then it puts in the local context either `h:T`, and the new goal target is `U`.

If the goal is neither a Pi/forall nor starting with a let definition,
the tactic `intro` applies the tactic `whnf` until the tactic `intro` can be applied or the goal is not `head-reducible`.
-/
meta def intro : parse ident_? → tactic unit
| none     := intro1 >> skip
| (some h) := tactic.intro h >> skip

/--
Similar to `intro` tactic. The tactic `intros` will keep introducing new hypotheses until the goal target is not a Pi/forall or let binder.
The variant `intros h_1 ... h_n` introduces `n` new hypotheses using the given identifiers to name them.
-/
meta def intros : parse ident_* → tactic unit
| [] := tactic.intros >> skip
| hs := intro_lst hs >> skip

/--
The tactic introv allows to automatically introduce the variables of a theorem and explicitly name the hypotheses involved.
The given names are used to name non-dependent hypotheses.
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
tactic.introv ns >> return ()

/--
The tactic `rename h₁ h₂` renames hypothesis `h₁` into `h₂` in the current local context.
-/
meta def rename : parse ident → parse ident → tactic unit :=
tactic.rename

/--
This tactic applies to any goal.
The argument term is a term well-formed in the local context of the main goal.
The tactic apply tries to match the current goal against the conclusion of the type of term.
If it succeeds, then the tactic returns as many subgoals as the number of premises
that have not been fixed by type inference or type class resolution.
Non dependent premises are added before dependent ones.

The tactic `apply` uses higher-order pattern matching, type class resolution, and
first-order unification with dependent types.
-/
meta def apply (q : parse texpr) : tactic unit :=
i_to_expr_for_apply q >>= tactic.apply

/--
Similar to the `apply` tactic, but it also creates subgoals for dependent premises
that have not been fixed by type inference or type class resolution.
-/
meta def fapply (q : parse texpr) : tactic unit :=
i_to_expr_for_apply q >>= tactic.fapply

/--
Similar to the `apply` tactic, but it only creates subgoals for non dependent premises
that have not been fixed by type inference or type class resolution.
-/
meta def eapply (q : parse texpr) : tactic unit :=
i_to_expr_for_apply q >>= tactic.eapply

/--
Similar to the `apply` tactic, but allows the user to provide a `apply_cfg` configuration object.
-/
meta def apply_with (q : parse parser.pexpr) (cfg : apply_cfg) : tactic unit :=
do e ← i_to_expr_for_apply q, tactic.apply e cfg

/--
This tactic tries to close the main goal `... |- U` using type class resolution.
It succeeds if it generates a term of type `U` using type class resolution.
-/
meta def apply_instance : tactic unit :=
tactic.apply_instance

/--
This tactic applies to any goal. It behaves like `exact` with a big difference:
the user can leave some holes `_` in the term.
`refine` will generate as many subgoals as there are holes in the term.
Note that some holes may be implicit.
The type of holes must be either synthesized by the system or declared by
an explicit type ascription like (e.g., `(_ : nat → Prop)`).
-/
meta def refine (q : parse texpr) : tactic unit :=
tactic.refine q

/--
This tactic looks in the local context for an hypothesis which type is equal to the goal target.
If it is the case, the subgoal is proved. Otherwise, it fails.
-/
meta def assumption : tactic unit :=
tactic.assumption

private meta def change_core (e : expr) : option expr → tactic unit
| none     := tactic.change e
| (some h) :=
  do num_reverted : ℕ ← revert h,
     expr.pi n bi d b ← target,
     tactic.change $ expr.pi n bi e b,
     intron num_reverted

/--
This tactic applies to any goal. `change U` replaces the main goal target `T` with `U`
providing that `U` is well-formed with respect to the main goal local context,
and `T` and `U` are definitionally equal. `change U at h` will change a local hypothesis
with `U`. `change A with B at h1 h2 ...` will replace `A` with `B` in all the supplied
hypotheses (or `*`), or in the goal if no `at` clause is specified, provided that
`A` and `B` are definitionally equal.
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
This tactic applies to any goal. It gives directly the exact proof
term of the goal. Let `T` be our goal, let `p` be a term of type `U` then
`exact p` succeeds iff `T` and `U` are definitionally equal.
-/
meta def exact (q : parse texpr) : tactic unit :=
do tgt : expr ← target,
   i_to_expr_strict ``(%%q : %%tgt) >>= tactic.exact
/--
Like `exact`, but takes a list of terms and checks that all goals
are discharged after the tactic.
-/
meta def exacts : parse pexpr_list_or_texpr → tactic unit
| [] := done
| (t :: ts) := exact t >> exacts ts

/-- A synonym for `exact` that allows writing `have/show ..., from ...` in tactic mode. -/
meta def «from» := exact

/--
`revert h₁ ... hₙ` applies to any goal with hypotheses `h₁` ... `hₙ`.
It moves the hypotheses and its dependencies to the goal target.
This tactic is the inverse of `intro`.
-/
meta def revert (ids : parse ident*) : tactic unit :=
do hs ← mmap tactic.get_local ids, revert_lst hs, skip

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

meta structure rw_rule :=
(pos  : pos)
(symm : bool)
(rule : pexpr)

meta instance rw_rule.reflect : has_reflect rw_rule :=
λ ⟨p, s, r⟩, `(_)

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
   (do e ← to_expr' r.rule, rewrite_target e {cfg with symm := r.symm})
   (eq_lemmas.mfirst $ λ n, do e ← mk_const n, rewrite_target e {cfg with symm := r.symm})
   (eq_lemmas.empty)

private meta def uses_hyp (e : expr) (h : expr) : bool :=
e.fold ff $ λ t _ r, r || to_bool (t = h)

private meta def rw_hyp (cfg : rewrite_cfg) : list rw_rule → expr → tactic unit
| []      hyp := skip
| (r::rs) hyp := do
  save_info r.pos,
  eq_lemmas ← get_rule_eqn_lemmas r,
  orelse'
    (do e ← to_expr' r.rule, when (not (uses_hyp e hyp)) $ rewrite_hyp e hyp {cfg with symm := r.symm} >>= rw_hyp rs)
    (eq_lemmas.mfirst $ λ n, do e ← mk_const n, rewrite_hyp e hyp {cfg with symm := r.symm} >>= rw_hyp rs)
    (eq_lemmas.empty)

meta def rw_rule_p (ep : parser pexpr) : parser rw_rule :=
rw_rule.mk <$> cur_pos <*> (option.is_some <$> (with_desc "←" (tk "←" <|> tk "<-"))?) <*> ep

meta structure rw_rules_t :=
(rules   : list rw_rule)
(end_pos : option pos)

meta instance rw_rules_t.reflect : has_reflect rw_rules_t :=
λ ⟨rs, p⟩, `(_)

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

meta def rewrite (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : tactic unit :=
rw_core q l cfg

meta def rw (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : tactic unit :=
rw_core q l cfg

/- rewrite followed by assumption -/
meta def rwa (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : tactic unit :=
rewrite q l cfg >> try assumption

meta def erewrite (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {md := semireducible}) : tactic unit :=
rw_core q l cfg

meta def erw (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {md := semireducible}) : tactic unit :=
rw_core q l cfg

private meta def get_type_name (e : expr) : tactic name :=
do e_type ← infer_type e >>= whnf,
   (const I ls) ← return $ get_app_fn e_type,
   return I

precedence `generalizing` : 0
meta def induction (p : parse texpr) (rec_name : parse using_ident) (ids : parse with_ident_list)
  (revert : parse $ (tk "generalizing" *> ident*)?) : tactic unit :=
do e ← i_to_expr p,

   -- generalize major premise
   e ← if e.is_local_constant then pure e
   else generalize e >> intro1,

   -- generalize major premise args
   (e, newvars, locals) ← do {
      none ← pure rec_name | pure (e, [], []),
      t ← infer_type e,
      -- TODO(Kha): `t ← whnf_ginductive t,`
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

   tactic.induction e ids rec_name,
   all_goals $ do {
     intron n,
     clear_lst (newvars.map local_pp_name),
     (e::locals).mmap' (try ∘ clear) }

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

/-- Focuses on the `induction`/`cases` subgoal corresponding to the given introduction rule,
    optionally renaming introduced locals. -/
meta def case (ctor : parse ident) (ids : parse ident_*) (tac : itactic) : tactic unit :=
do r   ← result,
   env ← get_env,
   ctor ← resolve_constant ctor
       <|> fail ("'" ++ to_string ctor ++ "' is not a constructor"),
   ty  ← (env.inductive_type_of ctor).to_monad
       <|> fail ("'" ++ to_string ctor ++ "' is not a constructor"),
   let ctors := env.constructors_of ty,
   let idx   := env.inductive_num_params ty + /- motive -/ 1 +
     list.index_of ctor ctors,
   gs        ← get_goals,
   (case, g) ← (find_case gs ty idx (env.inductive_num_indices ty) none r ).to_monad
             <|> fail "could not find open goal of given case",
   set_goals $ g :: gs.filter (≠ g),
   rename_lams case ids,
   solve1 tac

meta def destruct (p : parse texpr) : tactic unit :=
i_to_expr p >>= tactic.destruct

private meta def generalize_arg_p : pexpr → parser (pexpr × name)
| (app (app (macro _ [const `eq _ ]) h) (local_const x _ _ _)) := pure (h, x)
| _ := fail "parse error"

/-- `generalize : e = x` replaces all occurrences of `e` in the target with a new hypothesis `x` of the same type.
    `generalize h : e = x` in addition registers the hypothesis `h : e = x`. -/
meta def generalize (h : parse ident?) (p : parse $ tk ":" *> with_desc "expr = id" (parser.pexpr 0 >>= generalize_arg_p)) : tactic unit :=
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

meta def ginduction (p : parse texpr) (rec_name : parse using_ident) (ids : parse with_ident_list) : tactic unit :=
do x ← mk_fresh_name,
   let (h, hs) := (match ids with
   | []        := (`_h, [])
   | (h :: hs) := (h, hs)
   end : name × list name),
   generalize h (p, x),
   t ← get_local x,
   induction (to_pexpr t) rec_name hs ([] : list name)

private meta def cases_arg_p : parser (option name × pexpr) :=
with_desc "(id :)? expr" $ do
  t ← texpr,
  match t with
  | (local_const x _ _ _) :=
    (tk ":" *> do t ← texpr, pure (some x, t)) <|> pure (none, t)
  | _ := pure (none, t)
  end

meta def cases : parse cases_arg_p → parse with_ident_list → tactic unit
| (none,   p) ids := do
  e ← i_to_expr p,
  tactic.cases e ids
| (some h, p) ids := do
  x   ← mk_fresh_name,
  generalize h (p, x),
  hx  ← get_local x,
  tactic.cases hx ids

meta def trivial : tactic unit :=
tactic.triv <|> tactic.reflexivity <|> tactic.contradiction <|> fail "trivial tactic failed"

/-- Closes the main goal using sorry. -/
meta def admit : tactic unit := tactic.admit

/--
This tactic applies to any goal. The contradiction tactic attempts to find in the current local context an hypothesis that is equivalent to
an empty inductive type (e.g. `false`), a hypothesis of the form `c_1 ... = c_2 ...` where `c_1` and `c_2` are distinct constructors,
or two contradictory hypotheses.
-/
meta def contradiction : tactic unit :=
tactic.contradiction

meta def repeat : itactic → tactic unit :=
tactic.repeat

meta def try : itactic → tactic unit :=
tactic.try

meta def skip : tactic unit :=
tactic.skip

meta def solve1 : itactic → tactic unit :=
tactic.solve1

meta def abstract (id : parse ident?) (tac : itactic) : tactic unit :=
tactic.abstract tac id

meta def all_goals : itactic → tactic unit :=
tactic.all_goals

meta def any_goals : itactic → tactic unit :=
tactic.any_goals

meta def focus (tac : itactic) : tactic unit :=
tactic.focus [tac]

private meta def assume_core (n : name) (ty : pexpr) :=
do t ← target,
    when (not $ t.is_pi ∨ t.is_let) whnf_target,
    t ← target,
    when (not $ t.is_pi ∨ t.is_let) $
      fail "assume tactic failed, Pi/let expression expected",
    ty ← i_to_expr ty,
    unify ty t.binding_domain,
    intro_core n >> skip

meta def «assume» : parse (sum.inl <$> (tk ":" *> texpr) <|> sum.inr <$> parse_binders) → tactic unit
| (sum.inl ty)      := assume_core `this ty
| (sum.inr binders) :=
  binders.mmap' $ λ b, assume_core b.local_pp_name b.local_type

/--
This tactic applies to any goal.
- `have h : T := p` adds the hypothesis `h : T` to the current goal if `p` a term of type `T`.
If `T` is omitted, it will be inferred.
- `have h : T` adds the hypothesis `h : T` to the current goal and opens a new subgoal with target `T`.
The new subgoal becomes the main goal. If `T` is omitted, it will be replaced by a fresh meta variable.

If `h` is omitted, it defaults to `this`.
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
This tactic applies to any goal.
- `let h : T := p` adds the hypothesis `h : T := p` to the current goal if `p` a term of type `T`.
If `T` is omitted, it will be inferred.
- `let h : T` adds the hypothesis `h : T := ?M` to the current goal and opens a new subgoal `?M : T`.
The new subgoal becomes the main goal. If `T` is omitted, it will be replaced by a fresh meta variable.

If `h` is omitted, it defaults to `this`.
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
This tactic displays the current state in the tracing buffer.
-/
meta def trace_state : tactic unit :=
tactic.trace_state

/--
`trace a` displays `a` in the tracing buffer.
-/
meta def trace {α : Type} [has_to_tactic_format α] (a : α) : tactic unit :=
tactic.trace a

meta def existsi : parse pexpr_list_or_texpr → tactic unit
| []      := return ()
| (p::ps) := i_to_expr p >>= tactic.existsi >> existsi ps

/--
This tactic applies to a goal such that its conclusion is an inductive type (say `I`).
It tries to apply each constructor of `I` until it succeeds.
-/
meta def constructor : tactic unit :=
tactic.constructor

/-- Similar to `constructor`, but only non dependent premises are added as new goals. -/
meta def econstructor : tactic unit :=
tactic.econstructor

meta def left : tactic unit :=
tactic.left

meta def right : tactic unit :=
tactic.right

meta def split : tactic unit :=
tactic.split

meta def exfalso : tactic unit :=
tactic.exfalso

/--
The injection tactic is based on the fact that constructors of inductive datatypes are injections.
That means that if `c` is a constructor of an inductive datatype,
and if `(c t₁)` and `(c t₂)` are two terms that are equal then  `t₁` and `t₂` are equal too.

If `q` is a proof of a statement of conclusion `t₁ = t₂`,
then injection applies injectivity to derive the equality of all arguments of `t₁` and `t₂` placed in the same positions.
For example, from `(a::b) = (c::d)` we derive `a=c` and `b=d`.
To use this tactic `t₁` and `t₂` should be constructor applications of the same constructor.

Given `h : a::b = c::d`, the tactic `injection h` adds to new hypothesis with types `a = c` and `b = d`
to the main goal. The tactic `injection h with h₁ h₂` uses the names `h₁` an `h₂` to name the new
hypotheses.
-/
meta def injection (q : parse texpr) (hs : parse with_ident_list) : tactic unit :=
do e ← i_to_expr q, tactic.injection_with e hs, try assumption

meta def injections (hs : parse with_ident_list) : tactic unit :=
do tactic.injections_with hs, try assumption

end interactive

meta structure simp_config_ext extends simp_config :=
(discharger : tactic unit := failed)

section mk_simp_set
open expr interactive.types

meta inductive simp_arg_type : Type
| all_hyps : simp_arg_type
| except   : name  → simp_arg_type
| expr     : pexpr → simp_arg_type


meta instance : has_reflect simp_arg_type
| simp_arg_type.all_hyps   := `(_)
| (simp_arg_type.except _) := `(_)
| (simp_arg_type.expr _)   := `(_)

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
This tactic uses lemmas and hypotheses to simplify the main goal target or non-dependent hypotheses.
It has many variants.

- `simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.

- `simp [h_1, ..., h_n]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and the given `h_i`s.
   The `h_i`'s are terms. If a `h_i` is a definition `f`, then the equational lemmas associated with `f` are used.
   This is a convenient way to "unfold" `f`.

- `simp [*]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and all hypotheses.
  Remark: `simp *` is a shorthand for `simp [*]`.

- `simp only [h_1, ..., h_n]` is like `simp [h_1, ..., h_n]` but does not use `[simp]` lemmas

- `simp [-id_1, ... -id_n]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]`,
   but removes the ones named `id_i`s.

- `simp at h_1 ... h_n` simplifies the non dependent hypotheses `h_1 : T_1` ... `h_n : T : n`. The tactic fails if the target or another hypothesis depends on one of them.

- `simp at *` simplifies all the hypotheses and the target.

- `simp * at *` simplifies target and all (non-dependent propositional) hypotheses using the other hypotheses.

- `simp with attr_1 ... attr_n` simplifies the main goal target using the lemmas tagged with any of the attributes `[attr_1]`, ..., `[attr_n]` or `[simp]`.
-/
meta def simp (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
              (locat : parse location) (cfg : simp_config_ext := {}) : tactic unit :=
simp_core cfg.to_simp_config cfg.discharger no_dflt hs attr_names locat

/-- Just construct the simp set and trace it -/
meta def trace_simp_set (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list) : tactic unit :=
do (s, _) ← mk_simp_set no_dflt attr_names hs,
   s.pp >>= trace

meta def simp_intros (ids : parse ident_*) (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
                     (cfg : simp_intros_config := {}) : tactic unit :=
do (s, u) ← mk_simp_set no_dflt attr_names hs,
   when (¬u.empty) (fail (sformat! "simp_intros tactic does not support {u}")),
   tactic.simp_intros s u ids cfg,
   try triv >> try (reflexivity reducible)

private meta def to_simp_arg_list (es : list pexpr) : list simp_arg_type :=
es.map simp_arg_type.expr

meta def dsimp (no_dflt : parse only_flag) (es : parse simp_arg_list) (attr_names : parse with_ident_list)
               (l : parse location) (cfg : dsimp_config := {}) : tactic unit :=
do (s, u) ← mk_simp_set no_dflt attr_names es,
match l with
| loc.wildcard := do ls ← local_context, n ← revert_lst ls, dsimp_target s u cfg, intron n
| _            := l.apply (λ h, dsimp_hyp h s u cfg) (dsimp_target s u cfg)
end

/--
This tactic applies to a goal that has the form `t ~ u` where `~` is a reflexive relation.
That is, a relation which has a reflexivity lemma tagged with the attribute `[refl]`.
The tactic checks whether `t` and `u` are definitionally equal and then solves the goal.
-/
meta def reflexivity : tactic unit :=
tactic.reflexivity

/--
Shorter name for the tactic `reflexivity`.
-/
meta def refl : tactic unit :=
tactic.reflexivity

meta def symmetry : tactic unit :=
tactic.symmetry

meta def transitivity (q : parse texpr?) : tactic unit :=
tactic.transitivity >> match q with
| none := skip
| some q :=
  do (r, lhs, rhs) ← target_lhs_rhs,
     i_to_expr q >>= unify rhs
end

meta def ac_reflexivity : tactic unit :=
tactic.ac_refl

meta def ac_refl : tactic unit :=
tactic.ac_refl

meta def cc : tactic unit :=
tactic.cc

meta def subst (q : parse texpr) : tactic unit :=
i_to_expr q >>= tactic.subst >> try (tactic.reflexivity reducible)

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

namespace interactive
open interactive interactive.types expr

meta def unfold (cs : parse ident*) (locat : parse location) (cfg : unfold_config := {}) : tactic unit :=
do es ← ids_to_simp_arg_list "unfold" cs,
   let no_dflt := tt,
   simp_core cfg.to_simp_config failed no_dflt es [] locat

meta def unfold1 (cs : parse ident*) (locat : parse location) (cfg : unfold_config := {single_pass := tt}) : tactic unit :=
unfold cs locat cfg

meta def apply_opt_param : tactic unit :=
tactic.apply_opt_param

meta def apply_auto_param : tactic unit :=
tactic.apply_auto_param

meta def fail_if_success (tac : itactic) : tactic unit :=
tactic.fail_if_success tac

meta def success_if_fail (tac : itactic) : tactic unit :=
tactic.success_if_fail tac

meta def guard_expr_eq (t : expr) (p : parse $ tk ":=" *> texpr) : tactic unit :=
do e ← to_expr p, guard (alpha_eqv t e)

meta def guard_target (p : parse texpr) : tactic unit :=
do t ← target, guard_expr_eq t p

meta def guard_hyp (n : parse ident) (p : parse $ tk ":=" *> texpr) : tactic unit :=
do h ← get_local n >>= infer_type, guard_expr_eq h p

meta def by_cases (q : parse texpr) (n : parse (tk "with" *> ident)?): tactic unit :=
do p ← tactic.to_expr_strict q,
   tactic.by_cases p (n.get_or_else `h)

meta def by_contradiction (n : parse ident?) : tactic unit :=
tactic.by_contradiction n >> return ()

meta def by_contra (n : parse ident?) : tactic unit :=
tactic.by_contradiction n >> return ()

/-- Type check the given expression, and trace its type. -/
meta def type_check (p : parse texpr) : tactic unit :=
do e ← to_expr p, tactic.type_check e, infer_type e >>= trace

/-- Fail if there are unsolved goals. -/
meta def done : tactic unit :=
tactic.done

private meta def show_aux (p : pexpr) : list expr → list expr → tactic unit
| []      r := fail "show tactic failed"
| (g::gs) r := do
  do {set_goals [g], g_ty ← target, ty ← i_to_expr p, unify g_ty ty, set_goals (g :: r.reverse ++ gs), tactic.change ty}
  <|>
  show_aux gs (g::r)

meta def «show» (q : parse texpr) : tactic unit :=
do gs ← get_goals,
   show_aux q gs []

/--
  The tactic `specialize (h a_1 ... a_n)` works on local hypothesis `h`.
  The premises of this hypothesis (either universal quantifications or non-dependent implications)
  are instantiated by concrete terms coming either from arguments `a_1` ... `a_n`.
  It adds a new hypothesis with the same name `h := h a_1 ... a_n`, and (tries to) clear
  the previous one.
-/
meta def specialize (p : parse texpr) : tactic unit :=
do e ← i_to_expr p,
   let h := expr.get_app_fn e,
   if h.is_local_constant
   then tactic.note h.local_pp_name none e >> try (tactic.clear h)
   else tactic.fail "specialize requires a term of the form `h x_1 .. x_n` where `h` appears in the local context"

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
   Copy a list of meta definitions in the current namespace to
   tactic.interactive.

   This command is useful when we want to update tactic.interactive
   without closing the current namespace.
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

/-- Rename hypotheses with the same name. -/
meta def dedup : tactic unit :=
mwhen has_dup $ do
  ctx ← local_context,
  n   ← revert_lst ctx,
  intron n

end add_interactive
