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
/- allows metavars and report errors -/
meta def i_to_expr (q : pexpr) : tactic expr :=
to_expr q tt

/- doesn't allows metavars and report errors -/
meta def i_to_expr_strict (q : pexpr) : tactic expr :=
to_expr q ff

namespace interactive
open interactive interactive.types expr

/-
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
If it succeeds, then the tactic returns as many subgoals as the number of non-dependent premises
that have not been fixed by type inference or type class resolution.

The tactic `apply` uses higher-order pattern matching, type class resolution, and
first-order unification with dependent types.
-/
meta def apply (q : parse texpr) : tactic unit :=
i_to_expr q >>= tactic.apply

/--
Similar to the `apply` tactic, but it also creates subgoals for dependent premises
that have not been fixed by type inference or type class resolution.
-/
meta def fapply (q : parse texpr) : tactic unit :=
i_to_expr q >>= tactic.fapply

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
| none := tactic.change e
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
| none (loc.ns []) := do e ← i_to_expr q, change_core e none
| none (loc.ns [h]) := do eq ← i_to_expr q, eh ← get_local h, change_core eq (some eh)
| none _ := fail "change-at does not support multiple locations"
| (some w) l :=
  do hs ← l.get_locals,
     eq ← i_to_expr_strict q,
     ew ← i_to_expr_strict w,
     let repl := λe : expr, e.replace (λ a n, if a = eq then some ew else none),
     hs.mmap' (λh, do e ← infer_type h, change_core (repl e) (some h)),
     if l.include_goal then do g ← target, change_core (repl g) none else skip

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
meta def exacts : parse qexpr_list_or_texpr → tactic unit
| [] := done
| (t :: ts) := exact t >> exacts ts

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
private meta def to_expr' (p : pexpr) : tactic expr :=
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

private meta def rw_goal (m : transparency) (rs : list rw_rule) : tactic unit :=
rs.mfor' $ λ r, save_info r.pos >> to_expr' r.rule >>= rewrite_core m tt tt occurrences.all r.symm

private meta def rw_hyp (m : transparency) (rs : list rw_rule) (hname : name) : tactic unit :=
rs.mfor' $ λ r,
do h ← get_local hname,
    save_info r.pos,
    e ← to_expr' r.rule,
    rewrite_at_core m tt tt occurrences.all r.symm e h

private meta def rw_hyps (m : transparency) (rs : list rw_rule) (hs : list name) : tactic unit :=
hs.mfor' (rw_hyp m rs)

meta def rw_rule_p (ep : parser pexpr) : parser rw_rule :=
rw_rule.mk <$> cur_pos <*> (option.is_some <$> (tk "-")?) <*> ep

meta structure rw_rules_t :=
(rules   : list rw_rule)
(end_pos : option pos)

meta instance rw_rules_t.reflect : has_reflect rw_rules_t :=
λ ⟨rs, p⟩, `(_)

-- accepts the same content as `qexpr_list_or_texpr`, but with correct goal info pos annotations
meta def rw_rules : parser rw_rules_t :=
(tk "[" *>
 rw_rules_t.mk <$> sep_by (skip_info (tk ",")) (set_goal_info_pos $ rw_rule_p (qexpr 0))
               <*> (some <$> cur_pos <* set_goal_info_pos (tk "]")))
<|> rw_rules_t.mk <$> (list.ret <$> rw_rule_p texpr) <*> return none

private meta def rw_core (m : transparency) (rs : parse rw_rules) (loca : parse location) : tactic unit :=
match loca with
| loc.wildcard := fail "wildcard not allowed with rewrite"
| loc.ns []    := rw_goal m rs.rules
| loc.ns hs    := rw_hyps m rs.rules hs
end >> try (reflexivity reducible)
    >> (returnopt rs.end_pos >>= save_info <|> skip)

meta def rewrite : parse rw_rules → parse location → tactic unit :=
rw_core reducible

meta def rw : parse rw_rules → parse location → tactic unit :=
rewrite

/- rewrite followed by assumption -/
meta def rwa (q : parse rw_rules) (l : parse location) : tactic unit :=
rewrite q l >> try assumption

meta def erewrite : parse rw_rules → parse location → tactic unit :=
rw_core semireducible

meta def erw : parse rw_rules → parse location → tactic unit :=
erewrite

private meta def get_type_name (e : expr) : tactic name :=
do e_type ← infer_type e >>= whnf,
   (const I ls) ← return $ get_app_fn e_type,
   return I

precedence `generalizing` : 0
meta def induction (p : parse texpr) (rec_name : parse using_ident) (ids : parse with_ident_list)
  (revert : parse $ (tk "generalizing" *> ident*)?) : tactic unit :=
do e ← i_to_expr p,
   locals ← mmap tactic.get_local $ revert.get_or_else [],
   n ← revert_lst locals,
   tactic.induction e ids rec_name,
   all_goals (intron n)

meta def cases (p : parse texpr) (ids : parse with_ident_list) : tactic unit :=
do e ← i_to_expr p,
   tactic.cases e ids

private meta def find_case (goals : list expr) (ty : name) (idx : nat) (num_indices : nat) : option expr → expr → option (expr × expr)
| case e := if e.has_meta_var then match e with
  | (mvar _ _)    :=
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

meta def generalize (p : parse qexpr) (x : parse ident) : tactic unit :=
do e ← i_to_expr p,
   tactic.generalize e x

meta def generalize2 (p : parse qexpr) (x : parse ident) (h : parse ident) : tactic unit :=
do tgt ← target,
   e ← to_expr p,
   let e' := tgt.replace $ λa n, if a = e then some (var n.succ) else none,
   to_expr ``(Π x, %%e = x → %%e') >>= assert h,
   swap,
   t ← get_local h,
   exact ``(%%t %%p rfl),
   intro x,
   intro h

meta def ginduction (p : parse texpr) (rec_name : parse using_ident) (ids : parse with_ident_list) : tactic unit :=
do x ← mk_fresh_name,
   let (h, hs) := (match ids with
   | []        := (`_h, [])
   | (h :: hs) := (h, hs)
   end : name × list name),
   generalize2 p x h,
   t ← get_local x,
   induction (to_pexpr t) rec_name hs ([] : list name)

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

meta def abstract (id : parse ident? ) (tac : itactic) : tactic unit :=
tactic.abstract tac id

meta def all_goals : itactic → tactic unit :=
tactic.all_goals

meta def any_goals : itactic → tactic unit :=
tactic.any_goals

meta def focus (tac : itactic) : tactic unit :=
tactic.focus [tac]

/--
This tactic applies to any goal. `assert h : T` adds a new hypothesis of name `h` and type `T` to the current goal and opens a new subgoal with target `T`.
The new subgoal becomes the main goal.
-/
meta def assert (h : parse ident) (q : parse $ tk ":" *> texpr) : tactic unit :=
do e ← i_to_expr_strict q,
   tactic.assert h e,
   return ()

meta def define (h : parse ident) (q : parse $ tk ":" *> texpr) : tactic unit :=
do e ← i_to_expr_strict q,
   tactic.define h e,
   return ()

/--
This tactic applies to any goal. `note h : T := p` adds a new hypothesis of name `h` and type `T` to the current goal if `p` a term of type `T`.
-/
meta def note (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ tk ":=" *> texpr) : tactic unit :=
match q₁ with
| some e := do
  t ← i_to_expr_strict e,
  v ← i_to_expr_strict ``(%%q₂ : %%t),
  tactic.assertv (h.get_or_else `this) t v,
  return ()
| none := do
  p ← i_to_expr_strict q₂,
  tactic.note (h.get_or_else `this) none p,
  return ()
end

meta def pose (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ tk ":=" *> texpr) : tactic unit :=
match q₁ with
| some e := do
  t ← i_to_expr_strict e,
  v ← i_to_expr_strict ``(%%q₂ : %%t),
  tactic.definev (h.get_or_else `this) t v,
  return ()
| none := do
  p ← i_to_expr_strict q₂,
  tactic.pose (h.get_or_else `this) none p,
  return ()
end

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

meta def existsi : parse qexpr_list_or_texpr → tactic unit
| []      := return ()
| (p::ps) := i_to_expr p >>= tactic.existsi >> existsi ps

/--
This tactic applies to a goal such that its conclusion is an inductive type (say `I`).
It tries to apply each constructor of `I` until it succeeds.
-/
meta def constructor : tactic unit :=
tactic.constructor

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

section mk_simp_set
open expr

private meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

private meta def report_invalid_simp_lemma {α : Type} (n : name): tactic α :=
fail ("invalid simplification lemma '" ++ to_string n ++ "' (use command 'set_option trace.simp_lemmas true' for more details)")

private meta def simp_lemmas.resolve_and_add (s : simp_lemmas) (n : name) (ref : pexpr) : tactic simp_lemmas :=
do
  p ← resolve_name n,
  -- unpack local refs
  let e := p.erase_annotations.get_app_fn.erase_annotations,
  match e with
  | const n _           :=
    (do b ← is_valid_simp_lemma_cnst reducible n, guard b, save_const_type_info n ref, s.add_simp n)
    <|>
    (do eqns ← get_eqn_lemmas_for tt n, guard (eqns.length > 0), save_const_type_info n ref, add_simps s eqns)
    <|>
    report_invalid_simp_lemma n
  | _ :=
    (do e ← i_to_expr p, b ← is_valid_simp_lemma reducible e, guard b, try (save_type_info e ref), s.add e)
    <|>
    report_invalid_simp_lemma n
  end

private meta def simp_lemmas.add_pexpr (s : simp_lemmas) (p : pexpr) : tactic simp_lemmas :=
match p with
| (const c [])          := simp_lemmas.resolve_and_add s c p
| (local_const c _ _ _) := simp_lemmas.resolve_and_add s c p
| _                     := do new_e ← i_to_expr p, s.add new_e
end

private meta def simp_lemmas.append_pexprs : simp_lemmas → list pexpr → tactic simp_lemmas
| s []      := return s
| s (l::ls) := do new_s ← simp_lemmas.add_pexpr s l, simp_lemmas.append_pexprs new_s ls

meta def mk_simp_set (no_dflt : bool) (attr_names : list name) (hs : list pexpr) (ex : list name) : tactic simp_lemmas :=
do s₀ ← join_user_simp_lemmas no_dflt attr_names,
   s₁ ← simp_lemmas.append_pexprs s₀ hs,
   -- add equational lemmas, if any
   ex ← ex.mfor (λ n, list.cons n <$> get_eqn_lemmas_for tt n),
   return $ simp_lemmas.erase s₁ $ ex.join

end mk_simp_set

namespace interactive
open interactive interactive.types expr

private meta def simp_goal (cfg : simp_config) : simp_lemmas → tactic unit
| s := do
   (new_target, pr) ← target >>= simplify_core cfg s `eq,
   replace_target new_target pr

private meta def simp_hyp (cfg : simp_config) (s : simp_lemmas) (h_name : name) : tactic unit :=
do h      ← get_local h_name,
   h_type ← infer_type h,
   (h_new_type, pr) ← simplify_core cfg s `eq h_type,
   replace_hyp h h_new_type pr,
   return ()

private meta def simp_hyps (cfg : simp_config) : simp_lemmas → list name → tactic unit
| s []      := skip
| s (h::hs) := simp_hyp cfg s h >> simp_hyps s hs

private meta def simp_core (cfg : simp_config) (no_dflt : bool) (ctx : list expr) (hs : list pexpr) (attr_names : list name) (ids : list name) (locat : loc) : tactic unit :=
do s ← mk_simp_set no_dflt attr_names hs ids,
   s ← s.append ctx,
   match locat : _ → tactic unit with
   | loc.wildcard :=
     do ls ← local_context,
        let loc_names := ls.map expr.local_pp_name,
        revert_lst ls,
        simp_intro_aux cfg ff s ff loc_names,
        return ()
   | (loc.ns []) := simp_goal cfg s
   | (loc.ns hs) := simp_hyps cfg s hs
   end,
   try tactic.triv, try (tactic.reflexivity reducible)

/--
This tactic uses lemmas and hypotheses to simplify the main goal target or non-dependent hypotheses.
It has many variants.

- `simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.

- `simp [h_1, ..., h_n]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and the given `h_i`s.
   The `h_i`'s are terms. If a `h_i` is a definition `f`, then the equational lemmas associated with `f` are used.
   This is a convenient way to "unfold" `f`.

- `simp only [h_1, ..., h_n]` is like `simp [h_1, ..., h_n]` but does not use `[simp]` lemmas

- `simp without id_1 ... id_n` simplifies the main goal target using the lemmas tagged with the attribute `[simp]`,
   but removes the ones named `id_i`s.

- `simp at h_1 ... h_n` simplifies the non dependent hypotheses `h_1 : T_1` ... `h_n : T : n`. The tactic fails if the target or another hypothesis depends on one of them.

- `simp at *` simplifies all the hypotheses and the goal.

- `simp with attr_1 ... attr_n` simplifies the main goal target using the lemmas tagged with any of the attributes `[attr_1]`, ..., `[attr_n]` or `[simp]`.
-/
meta def simp (no_dflt : parse only_flag) (hs : parse opt_qexpr_list) (attr_names : parse with_ident_list) (ids : parse without_ident_list) (locat : parse location)
              (cfg : simp_config := {}) : tactic unit :=
simp_core cfg no_dflt [] hs attr_names ids locat

/--
Similar to the `simp` tactic, but adds all applicable hypotheses as simplification rules.
-/
meta def simp_using_hs (no_dflt : parse only_flag) (hs : parse opt_qexpr_list) (attr_names : parse with_ident_list) (ids : parse without_ident_list)
                       (cfg : simp_config := {}) : tactic unit :=
do ctx ← collect_ctx_simps,
   simp_core cfg no_dflt ctx hs attr_names ids (loc.ns [])

meta def simph (no_dflt : parse only_flag) (hs : parse opt_qexpr_list) (attr_names : parse with_ident_list) (ids : parse without_ident_list)
               (cfg : simp_config := {}) : tactic unit :=
simp_using_hs no_dflt hs attr_names ids cfg

meta def simp_intros (ids : parse ident_*) (no_dflt : parse only_flag) (hs : parse opt_qexpr_list) (attr_names : parse with_ident_list)
                     (wo_ids : parse without_ident_list) (cfg : simp_config := {}) : tactic unit :=
do s ← mk_simp_set no_dflt attr_names hs wo_ids,
   match ids with
   | [] := simp_intros_using s cfg
   | ns := simp_intro_lst_using ns s cfg
   end,
   try triv >> try (reflexivity reducible)

meta def simph_intros (ids : parse ident_*) (no_dflt : parse only_flag) (hs : parse opt_qexpr_list) (attr_names : parse with_ident_list)
                     (wo_ids : parse without_ident_list) (cfg : simp_config := {}) : tactic unit :=
do s ← mk_simp_set no_dflt attr_names hs wo_ids,
   match ids with
   | [] := simph_intros_using s cfg
   | ns := simph_intro_lst_using ns s cfg
   end,
   try triv >> try (reflexivity reducible)

private meta def dsimp_hyps (s : simp_lemmas) : list name → tactic unit
| []      := skip
| (h::hs) := get_local h >>= dsimp_at_core s

meta def dsimp (no_dflt : parse only_flag) (es : parse opt_qexpr_list) (attr_names : parse with_ident_list) (ids : parse without_ident_list) : parse location → tactic unit
| (loc.ns [])    := do s ← mk_simp_set no_dflt attr_names es ids, tactic.dsimp_core s
| (loc.ns hs)    := do s ← mk_simp_set no_dflt attr_names es ids, dsimp_hyps s hs
| (loc.wildcard) := do ls ← local_context,
                       n ← revert_lst ls,
                       s ← mk_simp_set no_dflt attr_names es ids,
                       tactic.dsimp_core s,
                       intron n

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

private meta def dunfold_hyps : list name → list name → tactic unit
| cs []      := skip
| cs (h::hs) := get_local h >>= dunfold_at cs >> dunfold_hyps cs hs

meta def dunfold : parse ident* → parse location → tactic unit
| cs (loc.ns [])    := do new_cs ← to_qualified_names cs, tactic.dunfold new_cs
| cs (loc.ns hs)    := do new_cs ← to_qualified_names cs, dunfold_hyps new_cs hs
| cs (loc.wildcard) := do ls ← tactic.local_context,
                          n ← revert_lst ls,
                          new_cs ← to_qualified_names cs,
                          tactic.dunfold new_cs,
                          intron n

/- TODO(Leo): add support for non-refl lemmas -/
meta def unfold : parse ident* → parse location → tactic unit :=
dunfold

private meta def dunfold_hyps_occs : name → occurrences → list name → tactic unit
| c occs []  := skip
| c occs (h::hs) := get_local h >>= dunfold_core_at occs [c] >> dunfold_hyps_occs c occs hs

meta def dunfold_occs : parse ident → parse location → list nat → tactic unit
| c (loc.ns []) ps    := do new_c ← to_qualified_name c, tactic.dunfold_occs_of ps new_c
| c (loc.ns hs) ps    := do new_c ← to_qualified_name c, dunfold_hyps_occs new_c (occurrences.pos ps) hs
| c (loc.wildcard) ps := fail "wildcard not allowed when unfolding occurences"

/- TODO(Leo): add support for non-refl lemmas -/
meta def unfold_occs : parse ident → parse location → list nat → tactic unit :=
dunfold_occs

private meta def delta_hyps : list name → list name → tactic unit
| cs []      := skip
| cs (h::hs) := get_local h >>= delta_at cs >> dunfold_hyps cs hs

meta def delta : parse ident* → parse location → tactic unit
| cs (loc.ns [])    := do new_cs ← to_qualified_names cs, tactic.delta new_cs
| cs (loc.ns hs)    := do new_cs ← to_qualified_names cs, delta_hyps new_cs hs
| cs (loc.wildcard) := do ls ← tactic.local_context,
                          n ← revert_lst ls,
                          new_cs ← to_qualified_names cs,
                          tactic.delta new_cs,
                          intron n

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

meta def by_cases (q : parse texpr) (n : parse (tk "with" *> ident)?): tactic unit :=
do p ← tactic.to_expr_strict q,
   tactic.by_cases p (n.get_or_else `h)

meta def by_contradiction : tactic unit :=
tactic.by_contradiction >> return ()

meta def by_contra : tactic unit :=
tactic.by_contradiction >> return ()

/-- Fail if there are unsolved goals. -/
meta def done : tactic unit :=
tactic.done

private meta def show_goal_aux (p : pexpr) : list expr → list expr → tactic unit
| []      r := fail "show_goal tactic failed"
| (g::gs) r := do
  do {set_goals [g], g_ty ← target, ty ← i_to_expr p, unify g_ty ty, set_goals (g :: r.reverse ++ gs), tactic.change ty}
  <|>
  show_goal_aux gs (g::r)

meta def show_goal (q : parse texpr) : tactic unit :=
do gs ← get_goals,
   show_goal_aux q gs []

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

end add_interactive
