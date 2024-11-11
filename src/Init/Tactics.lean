/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Notation
set_option linter.missingDocs true -- keep it documented

namespace Lean.Parser.Tactic
/--
`with_annotate_state stx t` annotates the lexical range of `stx : Syntax` with
the initial and final state of running tactic `t`.
-/
scoped syntax (name := withAnnotateState)
  "with_annotate_state " rawStx ppSpace tactic : tactic

/--
Introduces one or more hypotheses, optionally naming and/or pattern-matching them.
For each hypothesis to be introduced, the remaining main goal's target type must
be a `let` or function type.

* `intro` by itself introduces one anonymous hypothesis, which can be accessed
  by e.g. `assumption`.
* `intro x y` introduces two hypotheses and names them. Individual hypotheses
  can be anonymized via `_`, or matched against a pattern:
  ```lean
  -- ... ⊢ α × β → ...
  intro (a, b)
  -- ..., a : α, b : β ⊢ ...
  ```
* Alternatively, `intro` can be combined with pattern matching much like `fun`:
  ```lean
  intro
  | n + 1, 0 => tac
  | ...
  ```
-/
syntax (name := intro) "intro" notFollowedBy("|") (ppSpace colGt term:max)* : tactic

/--
Introduces zero or more hypotheses, optionally naming them.

- `intros` is equivalent to repeatedly applying `intro`
  until the goal is not an obvious candidate for `intro`, which is to say
  that so long as the goal is a `let` or a pi type (e.g. an implication, function, or universal quantifier),
  the `intros` tactic will introduce an anonymous hypothesis.
  This tactic does not unfold definitions.

- `intros x y ...` is equivalent to `intro x y ...`,
  introducing hypotheses for each supplied argument and unfolding definitions as necessary.
  Each argument can be either an identifier or a `_`.
  An identifier indicates a name to use for the corresponding introduced hypothesis,
  and a `_` indicates that the hypotheses should be introduced anonymously.

## Examples

Basic properties:
```lean
def AllEven (f : Nat → Nat) := ∀ n, f n % 2 = 0

-- Introduces the two obvious hypotheses automatically
example : ∀ (f : Nat → Nat), AllEven f → AllEven (fun k => f (k + 1)) := by
  intros
  /- Tactic state
     f✝ : Nat → Nat
     a✝ : AllEven f✝
     ⊢ AllEven fun k => f✝ (k + 1) -/
  sorry

-- Introduces exactly two hypotheses, naming only the first
example : ∀ (f : Nat → Nat), AllEven f → AllEven (fun k => f (k + 1)) := by
  intros g _
  /- Tactic state
     g : Nat → Nat
     a✝ : AllEven g
     ⊢ AllEven fun k => g (k + 1) -/
  sorry

-- Introduces exactly three hypotheses, which requires unfolding `AllEven`
example : ∀ (f : Nat → Nat), AllEven f → AllEven (fun k => f (k + 1)) := by
  intros f h n
  /- Tactic state
     f : Nat → Nat
     h : AllEven f
     n : Nat
     ⊢ (fun k => f (k + 1)) n % 2 = 0 -/
  apply h
```

Implications:
```lean
example (p q : Prop) : p → q → p := by
  intros
  /- Tactic state
     a✝¹ : p
     a✝ : q
     ⊢ p      -/
  assumption
```

Let bindings:
```lean
example : let n := 1; let k := 2; n + k = 3 := by
  intros
  /- n✝ : Nat := 1
     k✝ : Nat := 2
     ⊢ n✝ + k✝ = 3 -/
  rfl
```
-/
syntax (name := intros) "intros" (ppSpace colGt (ident <|> hole))* : tactic

/--
`rename t => x` renames the most recent hypothesis whose type matches `t`
(which may contain placeholders) to `x`, or fails if no such hypothesis could be found.
-/
syntax (name := rename) "rename " term " => " ident : tactic

/--
`revert x...` is the inverse of `intro x...`: it moves the given hypotheses
into the main goal's target type.
-/
syntax (name := revert) "revert" (ppSpace colGt term:max)+ : tactic

/--
`clear x...` removes the given hypotheses, or fails if there are remaining
references to a hypothesis.
-/
syntax (name := clear) "clear" (ppSpace colGt term:max)+ : tactic

/--
`subst x...` substitutes each `x` with `e` in the goal if there is a hypothesis
of type `x = e` or `e = x`.
If `x` is itself a hypothesis of type `y = e` or `e = y`, `y` is substituted instead.
-/
syntax (name := subst) "subst" (ppSpace colGt term:max)+ : tactic

/--
Applies `subst` to all hypotheses of the form `h : x = t` or `h : t = x`.
-/
syntax (name := substVars) "subst_vars" : tactic

/--
`assumption` tries to solve the main goal using a hypothesis of compatible type, or else fails.
Note also the `‹t›` term notation, which is a shorthand for `show t by assumption`.
-/
syntax (name := assumption) "assumption" : tactic

/--
`contradiction` closes the main goal if its hypotheses are "trivially contradictory".

- Inductive type/family with no applicable constructors
  ```lean
  example (h : False) : p := by contradiction
  ```
- Injectivity of constructors
  ```lean
  example (h : none = some true) : p := by contradiction  --
  ```
- Decidable false proposition
  ```lean
  example (h : 2 + 2 = 3) : p := by contradiction
  ```
- Contradictory hypotheses
  ```lean
  example (h : p) (h' : ¬ p) : q := by contradiction
  ```
- Other simple contradictions such as
  ```lean
  example (x : Nat) (h : x ≠ x) : p := by contradiction
  ```
-/
syntax (name := contradiction) "contradiction" : tactic

/--
Changes the goal to `False`, retaining as much information as possible:

* If the goal is `False`, do nothing.
* If the goal is an implication or a function type, introduce the argument and restart.
  (In particular, if the goal is `x ≠ y`, introduce `x = y`.)
* Otherwise, for a propositional goal `P`, replace it with `¬ ¬ P`
  (attempting to find a `Decidable` instance, but otherwise falling back to working classically)
  and introduce `¬ P`.
* For a non-propositional goal use `False.elim`.
-/
syntax (name := falseOrByContra) "false_or_by_contra" : tactic

/--
`apply e` tries to match the current goal against the conclusion of `e`'s type.
If it succeeds, then the tactic returns as many subgoals as the number of premises that
have not been fixed by type inference or type class resolution.
Non-dependent premises are added before dependent ones.

The `apply` tactic uses higher-order pattern matching, type class resolution,
and first-order unification with dependent types.
-/
syntax (name := apply) "apply " term : tactic

/--
`exact e` closes the main goal if its target type matches that of `e`.
-/
syntax (name := exact) "exact " term : tactic

/--
`refine e` behaves like `exact e`, except that named (`?x`) or unnamed (`?_`)
holes in `e` that are not solved by unification with the main goal's target type
are converted into new goals, using the hole's name, if any, as the goal case name.
-/
syntax (name := refine) "refine " term : tactic

/--
`refine' e` behaves like `refine e`, except that unsolved placeholders (`_`)
and implicit parameters are also converted into new goals.
-/
syntax (name := refine') "refine' " term : tactic

/-- `exfalso` converts a goal `⊢ tgt` into `⊢ False` by applying `False.elim`. -/
macro "exfalso" : tactic => `(tactic| refine False.elim ?_)

/--
If the main goal's target type is an inductive type, `constructor` solves it with
the first matching constructor, or else fails.
-/
syntax (name := constructor) "constructor" : tactic

/--
Applies the first constructor when
the goal is an inductive type with exactly two constructors, or fails otherwise.
```
example : True ∨ False := by
  left
  trivial
```
-/
syntax (name := left) "left" : tactic

/--
Applies the second constructor when
the goal is an inductive type with exactly two constructors, or fails otherwise.
```
example {p q : Prop} (h : q) : p ∨ q := by
  right
  exact h
```
-/
syntax (name := right) "right" : tactic

/--
* `case tag => tac` focuses on the goal with case name `tag` and solves it using `tac`,
  or else fails.
* `case tag x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses
  with inaccessible names to the given names.
* `case tag₁ | tag₂ => tac` is equivalent to `(case tag₁ => tac); (case tag₂ => tac)`.
-/
syntax (name := case) "case " sepBy1(caseArg, " | ") " => " tacticSeq : tactic

/--
`case'` is similar to the `case tag => tac` tactic, but does not ensure the goal
has been solved after applying `tac`, nor admits the goal if `tac` failed.
Recall that `case` closes the goal using `sorry` when `tac` fails, and
the tactic execution is not interrupted.
-/
syntax (name := case') "case' " sepBy1(caseArg, " | ") " => " tacticSeq : tactic

/--
`next => tac` focuses on the next goal and solves it using `tac`, or else fails.
`next x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses with
inaccessible names to the given names.
-/
macro nextTk:"next " args:binderIdent* arrowTk:" => " tac:tacticSeq : tactic =>
  -- Limit ref variability for incrementality; see Note [Incremental Macros]
  withRef arrowTk `(tactic| case%$nextTk _ $args* =>%$arrowTk $tac)

/--
`all_goals tac` runs `tac` on each goal, concatenating the resulting goals.
If the tactic fails on any goal, the entire `all_goals` tactic fails.

See also `any_goals tac`.
-/
syntax (name := allGoals) "all_goals " tacticSeq : tactic

/--
`any_goals tac` applies the tactic `tac` to every goal,
concating the resulting goals for successful tactic applications.
If the tactic fails on all of the goals, the entire `any_goals` tactic fails.

This tactic is like `all_goals try tac` except that it fails if none of the applications of `tac` succeeds.
-/
syntax (name := anyGoals) "any_goals " tacticSeq : tactic

/--
`focus tac` focuses on the main goal, suppressing all other goals, and runs `tac` on it.
Usually `· tac`, which enforces that the goal is closed by `tac`, should be preferred.
-/
syntax (name := focus) "focus " tacticSeq : tactic

/-- `skip` does nothing. -/
syntax (name := skip) "skip" : tactic

/-- `done` succeeds iff there are no remaining goals. -/
syntax (name := done) "done" : tactic

/-- `trace_state` displays the current state in the info view. -/
syntax (name := traceState) "trace_state" : tactic

/-- `trace msg` displays `msg` in the info view. -/
syntax (name := traceMessage) "trace " str : tactic

/-- `fail_if_success t` fails if the tactic `t` succeeds. -/
syntax (name := failIfSuccess) "fail_if_success " tacticSeq : tactic

/--
`(tacs)` executes a list of tactics in sequence, without requiring that
the goal be closed at the end like `· tacs`. Like `by` itself, the tactics
can be either separated by newlines or `;`.
-/
syntax (name := paren) "(" withoutPosition(tacticSeq) ")" : tactic

/--
`with_reducible tacs` executes `tacs` using the reducible transparency setting.
In this setting only definitions tagged as `[reducible]` are unfolded.
-/
syntax (name := withReducible) "with_reducible " tacticSeq : tactic

/--
`with_reducible_and_instances tacs` executes `tacs` using the `.instances` transparency setting.
In this setting only definitions tagged as `[reducible]` or type class instances are unfolded.
-/
syntax (name := withReducibleAndInstances) "with_reducible_and_instances " tacticSeq : tactic

/--
`with_unfolding_all tacs` executes `tacs` using the `.all` transparency setting.
In this setting all definitions that are not opaque are unfolded.
-/
syntax (name := withUnfoldingAll) "with_unfolding_all " tacticSeq : tactic

/-- `first | tac | ...` runs each `tac` until one succeeds, or else fails. -/
syntax (name := first) "first " withPosition((ppDedent(ppLine) colGe "| " tacticSeq)+) : tactic

/--
`rotate_left n` rotates goals to the left by `n`. That is, `rotate_left 1`
takes the main goal and puts it to the back of the subgoal list.
If `n` is omitted, it defaults to `1`.
-/
syntax (name := rotateLeft) "rotate_left" (ppSpace num)? : tactic

/--
Rotate the goals to the right by `n`. That is, take the goal at the back
and push it to the front `n` times. If `n` is omitted, it defaults to `1`.
-/
syntax (name := rotateRight) "rotate_right" (ppSpace num)? : tactic

/-- `try tac` runs `tac` and succeeds even if `tac` failed. -/
macro "try " t:tacticSeq : tactic => `(tactic| first | $t | skip)

/--
`tac <;> tac'` runs `tac` on the main goal and `tac'` on each produced goal,
concatenating all goals produced by `tac'`.
-/
macro:1 x:tactic tk:" <;> " y:tactic:2 : tactic => `(tactic|
  focus
    $x:tactic
    -- annotate token with state after executing `x`
    with_annotate_state $tk skip
    all_goals $y:tactic)

/-- `fail msg` is a tactic that always fails, and produces an error using the given message. -/
syntax (name := fail) "fail" (ppSpace str)? : tactic

/-- `eq_refl` is equivalent to `exact rfl`, but has a few optimizations. -/
syntax (name := eqRefl) "eq_refl" : tactic

/--
This tactic applies to a goal whose target has the form `x ~ x`,
where `~` is equality, heterogeneous equality or any relation that
has a reflexivity lemma tagged with the attribute @[refl].
-/
syntax "rfl" : tactic

/--
The same as `rfl`, but without trying `eq_refl` at the end.
-/
syntax (name := applyRfl) "apply_rfl" : tactic

-- We try `apply_rfl` first, because it produces a nice error message
macro_rules | `(tactic| rfl) => `(tactic| apply_rfl)

-- But, mostly for backward compatibility, we try `eq_refl` too (reduces more aggressively)
macro_rules | `(tactic| rfl) => `(tactic| eq_refl)
-- Also for backward compatibility, because `exact` can trigger the implicit lambda feature (see #5366)
macro_rules | `(tactic| rfl) => `(tactic| exact HEq.rfl)
/--
`rfl'` is similar to `rfl`, but disables smart unfolding and unfolds all kinds of definitions,
theorems included (relevant for declarations defined by well-founded recursion).
-/
macro "rfl'" : tactic => `(tactic| set_option smartUnfolding false in with_unfolding_all rfl)

/--
`ac_rfl` proves equalities up to application of an associative and commutative operator.
```
instance : Associative (α := Nat) (.+.) := ⟨Nat.add_assoc⟩
instance : Commutative (α := Nat) (.+.) := ⟨Nat.add_comm⟩

example (a b c d : Nat) : a + b + c + d = d + (b + c) + a := by ac_rfl
```
-/
syntax (name := acRfl) "ac_rfl" : tactic

/--
The `sorry` tactic closes the goal using `sorryAx`. This is intended for stubbing out incomplete
parts of a proof while still having a syntactically correct proof skeleton. Lean will give
a warning whenever a proof uses `sorry`, so you aren't likely to miss it, but
you can double check if a theorem depends on `sorry` by using
`#print axioms my_thm` and looking for `sorryAx` in the axiom list.
-/
macro "sorry" : tactic => `(tactic| exact @sorryAx _ false)

/-- `admit` is a shorthand for `exact sorry`. -/
macro "admit" : tactic => `(tactic| exact @sorryAx _ false)

/--
`infer_instance` is an abbreviation for `exact inferInstance`.
It synthesizes a value of any target type by typeclass inference.
-/
macro "infer_instance" : tactic => `(tactic| exact inferInstance)

/--
`+opt` is short for `(opt := true)`. It sets the `opt` configuration option to `true`.
-/
syntax posConfigItem := "+" noWs ident
/--
`-opt` is short for `(opt := false)`. It sets the `opt` configuration option to `false`.
-/
syntax negConfigItem := "-" noWs ident
/--
`(opt := val)` sets the `opt` configuration option to `val`.

As a special case, `(config := ...)` sets the entire configuration.
-/
syntax valConfigItem := atomic(" (" notFollowedBy(&"discharger" <|> &"disch") (ident <|> &"config")) " := " withoutPosition(term) ")"
/-- A configuration item for a tactic configuration. -/
syntax configItem := posConfigItem <|> negConfigItem <|> valConfigItem

/-- Configuration options for tactics. -/
syntax optConfig := (colGt configItem)*

/-- Optional configuration option for tactics. (Deprecated. Replace `(config)?` with `optConfig`.) -/
syntax config := atomic(" (" &"config") " := " withoutPosition(term) ")"

/-- The `*` location refers to all hypotheses and the goal. -/
syntax locationWildcard := " *"

/--
A hypothesis location specification consists of 1 or more hypothesis references
and optionally `⊢` denoting the goal.
-/
syntax locationHyp := (ppSpace colGt term:max)+ patternIgnore(ppSpace (atomic("|" noWs "-") <|> "⊢"))?

/--
Location specifications are used by many tactics that can operate on either the
hypotheses or the goal. It can have one of the forms:
* 'empty' is not actually present in this syntax, but most tactics use
  `(location)?` matchers. It means to target the goal only.
* `at h₁ ... hₙ`: target the hypotheses `h₁`, ..., `hₙ`
* `at h₁ h₂ ⊢`: target the hypotheses `h₁` and `h₂`, and the goal
* `at *`: target all hypotheses and the goal
-/
syntax location := withPosition(" at" (locationWildcard <|> locationHyp))

/--
* `change tgt'` will change the goal from `tgt` to `tgt'`,
  assuming these are definitionally equal.
* `change t' at h` will change hypothesis `h : t` to have type `t'`, assuming
  assuming `t` and `t'` are definitionally equal.
-/
syntax (name := change) "change " term (location)? : tactic

/--
* `change a with b` will change occurrences of `a` to `b` in the goal,
  assuming `a` and `b` are definitionally equal.
* `change a with b at h` similarly changes `a` to `b` in the type of hypothesis `h`.
-/
syntax (name := changeWith) "change " term " with " term (location)? : tactic

/--
If `thm` is a theorem `a = b`, then as a rewrite rule,
* `thm` means to replace `a` with `b`, and
* `← thm` means to replace `b` with `a`.
-/
syntax rwRule    := patternIgnore("← " <|> "<- ")? term
/-- A `rwRuleSeq` is a list of `rwRule` in brackets. -/
syntax rwRuleSeq := " [" withoutPosition(rwRule,*,?) "]"

/--
`rewrite [e]` applies identity `e` as a rewrite rule to the target of the main goal.
If `e` is preceded by left arrow (`←` or `<-`), the rewrite is applied in the reverse direction.
If `e` is a defined constant, then the equational theorems associated with `e` are used.
This provides a convenient way to unfold `e`.
- `rewrite [e₁, ..., eₙ]` applies the given rules sequentially.
- `rewrite [e] at l` rewrites `e` at location(s) `l`, where `l` is either `*` or a
  list of hypotheses in the local context. In the latter case, a turnstile `⊢` or `|-`
  can also be used, to signify the target of the goal.

Using `rw (occs := .pos L) [e]`,
where `L : List Nat`, you can control which "occurrences" are rewritten.
(This option applies to each rule, so usually this will only be used with a single rule.)
Occurrences count from `1`.
At each allowed occurrence, arguments of the rewrite rule `e` may be instantiated,
restricting which later rewrites can be found.
(Disallowed occurrences do not result in instantiation.)
`(occs := .neg L)` allows skipping specified occurrences.
-/
syntax (name := rewriteSeq) "rewrite" optConfig rwRuleSeq (location)? : tactic

/--
`rw` is like `rewrite`, but also tries to close the goal by "cheap" (reducible) `rfl` afterwards.
-/
macro (name := rwSeq) "rw " c:optConfig s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (rewrite $c [$rs,*] $(l)?; with_annotate_state $rbrak (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported

/-- `rwa` is short-hand for `rw; assumption`. -/
macro "rwa " rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $[$loc:location]?; assumption))

/--
The `injection` tactic is based on the fact that constructors of inductive data
types are injections.
That means that if `c` is a constructor of an inductive datatype, and if `(c t₁)`
and `(c t₂)` are two terms that are equal then  `t₁` and `t₂` are equal too.
If `q` is a proof of a statement of conclusion `t₁ = t₂`, then injection applies
injectivity to derive the equality of all arguments of `t₁` and `t₂` placed in
the same positions. For example, from `(a::b) = (c::d)` we derive `a=c` and `b=d`.
To use this tactic `t₁` and `t₂` should be constructor applications of the same constructor.
Given `h : a::b = c::d`, the tactic `injection h` adds two new hypothesis with types
`a = c` and `b = d` to the main goal.
The tactic `injection h with h₁ h₂` uses the names `h₁` and `h₂` to name the new hypotheses.
-/
syntax (name := injection) "injection " term (" with" (ppSpace colGt (ident <|> hole))+)? : tactic

/-- `injections` applies `injection` to all hypotheses recursively
(since `injection` can produce new hypotheses). Useful for destructing nested
constructor equalities like `(a::b::c) = (d::e::f)`. -/
-- TODO: add with
syntax (name := injections) "injections" (ppSpace colGt (ident <|> hole))* : tactic

/--
The discharger clause of `simp` and related tactics.
This is a tactic used to discharge the side conditions on conditional rewrite rules.
-/
syntax discharger := atomic(" (" patternIgnore(&"discharger" <|> &"disch")) " := " withoutPosition(tacticSeq) ")"

/-- Use this rewrite rule before entering the subterms -/
syntax simpPre   := "↓"
/-- Use this rewrite rule after entering the subterms -/
syntax simpPost  := "↑"
/--
A simp lemma specification is:
* optional `↑` or `↓` to specify use before or after entering the subterm
* optional `←` to use the lemma backward
* `thm` for the theorem to rewrite with
-/
syntax simpLemma := (simpPre <|> simpPost)? patternIgnore("← " <|> "<- ")? term
/-- An erasure specification `-thm` says to remove `thm` from the simp set -/
syntax simpErase := "-" term:max
/-- The simp lemma specification `*` means to rewrite with all hypotheses -/
syntax simpStar  := "*"
/--
The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or
non-dependent hypotheses. It has many variants:
- `simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.
- `simp [h₁, h₂, ..., hₙ]` simplifies the main goal target using the lemmas tagged
  with the attribute `[simp]` and the given `hᵢ`'s, where the `hᵢ`'s are expressions.-
- If an `hᵢ` is a defined constant `f`, then `f` is unfolded. If `f` has equational lemmas associated
  with it (and is not a projection or a `reducible` definition), these are used to rewrite with `f`.
- `simp [*]` simplifies the main goal target using the lemmas tagged with the
  attribute `[simp]` and all hypotheses.
- `simp only [h₁, h₂, ..., hₙ]` is like `simp [h₁, h₂, ..., hₙ]` but does not use `[simp]` lemmas.
- `simp [-id₁, ..., -idₙ]` simplifies the main goal target using the lemmas tagged
  with the attribute `[simp]`, but removes the ones named `idᵢ`.
- `simp at h₁ h₂ ... hₙ` simplifies the hypotheses `h₁ : T₁` ... `hₙ : Tₙ`. If
  the target or another hypothesis depends on `hᵢ`, a new simplified hypothesis
  `hᵢ` is introduced, but the old one remains in the local context.
- `simp at *` simplifies all the hypotheses and the target.
- `simp [*] at *` simplifies target and all (propositional) hypotheses using the
  other hypotheses.
-/
syntax (name := simp) "simp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic
/--
`simp_all` is a stronger version of `simp [*] at *` where the hypotheses and target
are simplified multiple times until no simplification is applicable.
Only non-dependent propositional hypotheses are considered.
-/
syntax (name := simpAll) "simp_all" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")? : tactic

/--
The `dsimp` tactic is the definitional simplifier. It is similar to `simp` but only
applies theorems that hold by reflexivity. Thus, the result is guaranteed to be
definitionally equal to the input.
-/
syntax (name := dsimp) "dsimp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

/--
A `simpArg` is either a `*`, `-lemma` or a simp lemma specification
(which includes the `↑` `↓` `←` specifications for pre, post, reverse rewriting).
-/
def simpArg := simpStar.binary `orelse (simpErase.binary `orelse simpLemma)

/-- A simp args list is a list of `simpArg`. This is the main argument to `simp`. -/
syntax simpArgs := " [" simpArg,* "]"

/--
A `dsimpArg` is similar to `simpArg`, but it does not have the `simpStar` form
because it does not make sense to use hypotheses in `dsimp`.
-/
def dsimpArg := simpErase.binary `orelse simpLemma

/-- A dsimp args list is a list of `dsimpArg`. This is the main argument to `dsimp`. -/
syntax dsimpArgs := " [" dsimpArg,* "]"

/-- The common arguments of `simp?` and `simp?!`. -/
syntax simpTraceArgsRest := optConfig (discharger)? (&" only")? (simpArgs)? (ppSpace location)?

/--
`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.
-/
syntax (name := simpTrace) "simp?" "!"? simpTraceArgsRest : tactic

@[inherit_doc simpTrace]
macro tk:"simp?!" rest:simpTraceArgsRest : tactic => `(tactic| simp?%$tk ! $rest)

/-- The common arguments of `simp_all?` and `simp_all?!`. -/
syntax simpAllTraceArgsRest := optConfig (discharger)? (&" only")? (dsimpArgs)?

@[inherit_doc simpTrace]
syntax (name := simpAllTrace) "simp_all?" "!"? simpAllTraceArgsRest : tactic

@[inherit_doc simpTrace]
macro tk:"simp_all?!" rest:simpAllTraceArgsRest : tactic => `(tactic| simp_all?%$tk ! $rest)

/-- The common arguments of `dsimp?` and `dsimp?!`. -/
syntax dsimpTraceArgsRest := optConfig (&" only")? (dsimpArgs)? (ppSpace location)?

@[inherit_doc simpTrace]
syntax (name := dsimpTrace) "dsimp?" "!"? dsimpTraceArgsRest : tactic

@[inherit_doc simpTrace]
macro tk:"dsimp?!" rest:dsimpTraceArgsRest : tactic => `(tactic| dsimp?%$tk ! $rest)

/-- The arguments to the `simpa` family tactics. -/
syntax simpaArgsRest := optConfig (discharger)? &" only "? (simpArgs)? (" using " term)?

/--
This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ⋯] using e` will simplify the goal and the type of
  `e` using `rules`, then try to close the goal using `e`.

  Simplifying the type of `e` makes it more likely to match the goal
  (which has also been simplified). This construction also tends to be
  more robust under changes to the simp lemma set.

* `simpa [rules, ⋯]` will simplify the goal and the type of a
  hypothesis `this` if present in the context, then try to close the goal using
  the `assumption` tactic.
-/
syntax (name := simpa) "simpa" "?"? "!"? simpaArgsRest : tactic

@[inherit_doc simpa] macro "simpa!" rest:simpaArgsRest : tactic =>
  `(tactic| simpa ! $rest:simpaArgsRest)

@[inherit_doc simpa] macro "simpa?" rest:simpaArgsRest : tactic =>
  `(tactic| simpa ? $rest:simpaArgsRest)

@[inherit_doc simpa] macro "simpa?!" rest:simpaArgsRest : tactic =>
  `(tactic| simpa ?! $rest:simpaArgsRest)

/--
`delta id1 id2 ...` delta-expands the definitions `id1`, `id2`, ....
This is a low-level tactic, it will expose how recursive definitions have been
compiled by Lean.
-/
syntax (name := delta) "delta" (ppSpace colGt ident)+ (location)? : tactic

/--
* `unfold id` unfolds all occurrences of definition `id` in the target.
* `unfold id1 id2 ...` is equivalent to `unfold id1; unfold id2; ...`.
* `unfold id at h` unfolds at the hypothesis `h`.

Definitions can be either global or local definitions.

For non-recursive global definitions, this tactic is identical to `delta`.
For recursive global definitions, it uses the "unfolding lemma" `id.eq_def`,
which is generated for each recursive definition, to unfold according to the recursive definition given by the user.
Only one level of unfolding is performed, in contrast to `simp only [id]`, which unfolds definition `id` recursively.
-/
syntax (name := unfold) "unfold" (ppSpace colGt ident)+ (location)? : tactic

/--
Auxiliary macro for lifting have/suffices/let/...
It makes sure the "continuation" `?_` is the main goal after refining.
-/
macro "refine_lift " e:term : tactic => `(tactic| focus (refine no_implicit_lambda% $e; rotate_right))

/--
The `have` tactic is for adding hypotheses to the local context of the main goal.
* `have h : t := e` adds the hypothesis `h : t` if `e` is a term of type `t`.
* `have h := e` uses the type of `e` for `t`.
* `have : t := e` and `have := e` use `this` for the name of the hypothesis.
* `have pat := e` for a pattern `pat` is equivalent to `match e with | pat => _`,
  where `_` stands for the tactics that follow this one.
  It is convenient for types that have only one applicable constructor.
  For example, given `h : p ∧ q ∧ r`, `have ⟨h₁, h₂, h₃⟩ := h` produces the
  hypotheses `h₁ : p`, `h₂ : q`, and `h₃ : r`.
-/
syntax "have " haveDecl : tactic
macro_rules
  -- special case: when given a nested `by` block, move it outside of the `refine` to enable
  -- incrementality
  | `(tactic| have%$haveTk $id:haveId $bs* : $type := by%$byTk $tacs*) => do
    /-
    We want to create the syntax
    ```
    focus
      refine no_implicit_lambda% (have $id:haveId $bs* : $type := ?body; ?_)
      case body => $tacs*
    ```
    However, we need to be very careful with the syntax infos involved:
    * We want most infos up to `tacs` to be independent of changes inside it so that incrementality
      is not prematurely disabled; we use the `have` and then the `by` token as the reference for
      this. Note that if we did nothing, the reference would be the entire `have` input and so any
      change to `tacs` would change every token synthesized below.
    * For the single node of the `case` body, we *should not* change the ref as this makes sure the
      entire tactic block is included in any "unsaved goals" message (which is emitted after
      execution of all nested tactics so it is indeed safe for `evalCase` to ignore it for
      incrementality).
    * Even after setting the ref, we still need a `with_annotate_state` to show the correct tactic
      state on `by` as the synthetic info derived from the ref is ignored for this purpose.
    -/
    let tac ← Lean.withRef byTk `(tactic| with_annotate_state $byTk ($tacs*))
    let tac ← `(tacticSeq| $tac:tactic)
    let tac ← Lean.withRef byTk `(tactic| case body => $(.mk tac):tacticSeq)
    Lean.withRef haveTk `(tactic| focus
      refine no_implicit_lambda% (have $id:haveId $bs* : $type := ?body; ?_)
      $tac)
  | `(tactic| have $d:haveDecl) => `(tactic| refine_lift have $d:haveDecl; ?_)

/--
Given a main goal `ctx ⊢ t`, `suffices h : t' from e` replaces the main goal with `ctx ⊢ t'`,
`e` must have type `t` in the context `ctx, h : t'`.

The variant `suffices h : t' by tac` is a shorthand for `suffices h : t' from by tac`.
If `h :` is omitted, the name `this` is used.
 -/
macro "suffices " d:sufficesDecl : tactic => `(tactic| refine_lift suffices $d; ?_)
/--
The `let` tactic is for adding definitions to the local context of the main goal.
* `let x : t := e` adds the definition `x : t := e` if `e` is a term of type `t`.
* `let x := e` uses the type of `e` for `t`.
* `let : t := e` and `let := e` use `this` for the name of the hypothesis.
* `let pat := e` for a pattern `pat` is equivalent to `match e with | pat => _`,
  where `_` stands for the tactics that follow this one.
  It is convenient for types that let only one applicable constructor.
  For example, given `p : α × β × γ`, `let ⟨x, y, z⟩ := p` produces the
  local variables `x : α`, `y : β`, and `z : γ`.
-/
macro "let " d:letDecl : tactic => `(tactic| refine_lift let $d:letDecl; ?_)
/--
`show t` finds the first goal whose target unifies with `t`. It makes that the main goal,
 performs the unification, and replaces the target with the unified version of `t`.
-/
macro "show " e:term : tactic => `(tactic| refine_lift show $e from ?_) -- TODO: fix, see comment
/-- `let rec f : t := e` adds a recursive definition `f` to the current goal.
The syntax is the same as term-mode `let rec`. -/
syntax (name := letrec) withPosition(atomic("let " &"rec ") letRecDecls) : tactic
macro_rules
  | `(tactic| let rec $d) => `(tactic| refine_lift let rec $d; ?_)

/-- Similar to `refine_lift`, but using `refine'` -/
macro "refine_lift' " e:term : tactic => `(tactic| focus (refine' no_implicit_lambda% $e; rotate_right))
/-- Similar to `have`, but using `refine'` -/
macro "have' " d:haveDecl : tactic => `(tactic| refine_lift' have $d:haveDecl; ?_)
set_option linter.missingDocs false in -- OK, because `tactic_alt` causes inheritance of docs
macro (priority := high) "have'" x:ident " := " p:term : tactic => `(tactic| have' $x:ident : _ := $p)
attribute [tactic_alt tacticHave'_] «tacticHave'_:=_»
/-- Similar to `let`, but using `refine'` -/
macro "let' " d:letDecl : tactic => `(tactic| refine_lift' let $d:letDecl; ?_)

/--
The left hand side of an induction arm, `| foo a b c` or `| @foo a b c`
where `foo` is a constructor of the inductive type and `a b c` are the arguments
to the constructor.
-/
syntax inductionAltLHS := "| " (("@"? ident) <|> hole) (ident <|> hole)*
/--
In induction alternative, which can have 1 or more cases on the left
and `_`, `?_`, or a tactic sequence after the `=>`.
-/
syntax inductionAlt  := ppDedent(ppLine) inductionAltLHS+ " => " (hole <|> syntheticHole <|> tacticSeq)
/--
After `with`, there is an optional tactic that runs on all branches, and
then a list of alternatives.
-/
syntax inductionAlts := " with" (ppSpace colGt tactic)? withPosition((colGe inductionAlt)+)

/--
Assuming `x` is a variable in the local context with an inductive type,
`induction x` applies induction on `x` to the main goal,
producing one goal for each constructor of the inductive type,
in which the target is replaced by a general instance of that constructor
and an inductive hypothesis is added for each recursive argument to the constructor.
If the type of an element in the local context depends on `x`,
that element is reverted and reintroduced afterward,
so that the inductive hypothesis incorporates that hypothesis as well.

For example, given `n : Nat` and a goal with a hypothesis `h : P n` and target `Q n`,
`induction n` produces one goal with hypothesis `h : P 0` and target `Q 0`,
and one goal with hypotheses `h : P (Nat.succ a)` and `ih₁ : P a → Q a` and target `Q (Nat.succ a)`.
Here the names `a` and `ih₁` are chosen automatically and are not accessible.
You can use `with` to provide the variables names for each constructor.
- `induction e`, where `e` is an expression instead of a variable,
  generalizes `e` in the goal, and then performs induction on the resulting variable.
- `induction e using r` allows the user to specify the principle of induction that should be used.
  Here `r` should be a term whose result type must be of the form `C t`,
  where `C` is a bound variable and `t` is a (possibly empty) sequence of bound variables
- `induction e generalizing z₁ ... zₙ`, where `z₁ ... zₙ` are variables in the local context,
  generalizes over `z₁ ... zₙ` before applying the induction but then introduces them in each goal.
  In other words, the net effect is that each inductive hypothesis is generalized.
- Given `x : Nat`, `induction x with | zero => tac₁ | succ x' ih => tac₂`
  uses tactic `tac₁` for the `zero` case, and `tac₂` for the `succ` case.
-/
syntax (name := induction) "induction " term,+ (" using " term)?
  (" generalizing" (ppSpace colGt term:max)+)? (inductionAlts)? : tactic

/-- A `generalize` argument, of the form `term = x` or `h : term = x`. -/
syntax generalizeArg := atomic(ident " : ")? term:51 " = " ident

/--
* `generalize ([h :] e = x),+` replaces all occurrences `e`s in the main goal
  with a fresh hypothesis `x`s. If `h` is given, `h : e = x` is introduced as well.
* `generalize e = x at h₁ ... hₙ` also generalizes occurrences of `e`
  inside `h₁`, ..., `hₙ`.
* `generalize e = x at *` will generalize occurrences of `e` everywhere.
-/
syntax (name := generalize) "generalize " generalizeArg,+ (location)? : tactic

/--
A `cases` argument, of the form `e` or `h : e` (where `h` asserts that
`e = cᵢ a b` for each constructor `cᵢ` of the inductive).
-/
syntax casesTarget := atomic(ident " : ")? term
/--
Assuming `x` is a variable in the local context with an inductive type,
`cases x` splits the main goal, producing one goal for each constructor of the
inductive type, in which the target is replaced by a general instance of that constructor.
If the type of an element in the local context depends on `x`,
that element is reverted and reintroduced afterward,
so that the case split affects that hypothesis as well.
`cases` detects unreachable cases and closes them automatically.

For example, given `n : Nat` and a goal with a hypothesis `h : P n` and target `Q n`,
`cases n` produces one goal with hypothesis `h : P 0` and target `Q 0`,
and one goal with hypothesis `h : P (Nat.succ a)` and target `Q (Nat.succ a)`.
Here the name `a` is chosen automatically and is not accessible.
You can use `with` to provide the variables names for each constructor.
- `cases e`, where `e` is an expression instead of a variable, generalizes `e` in the goal,
  and then cases on the resulting variable.
- Given `as : List α`, `cases as with | nil => tac₁ | cons a as' => tac₂`,
  uses tactic `tac₁` for the `nil` case, and `tac₂` for the `cons` case,
  and `a` and `as'` are used as names for the new variables introduced.
- `cases h : e`, where `e` is a variable or an expression,
  performs cases on `e` as above, but also adds a hypothesis `h : e = ...` to each hypothesis,
  where `...` is the constructor instance for that particular case.
-/
syntax (name := cases) "cases " casesTarget,+ (" using " term)? (inductionAlts)? : tactic

/-- `rename_i x_1 ... x_n` renames the last `n` inaccessible names using the given names. -/
syntax (name := renameI) "rename_i" (ppSpace colGt binderIdent)+ : tactic

/--
`repeat tac` repeatedly applies `tac` so long as it succeeds.
The tactic `tac` may be a tactic sequence, and if `tac` fails at any point in its execution,
`repeat` will revert any partial changes that `tac` made to the tactic state.

The tactic `tac` should eventually fail, otherwise `repeat tac` will run indefinitely.

See also:
* `try tac` is like `repeat tac` but will apply `tac` at most once.
* `repeat' tac` recursively applies `tac` to each goal.
* `first | tac1 | tac2` implements the backtracking used by `repeat`
-/
syntax "repeat " tacticSeq : tactic
macro_rules
  | `(tactic| repeat $seq) => `(tactic| first | ($seq); repeat $seq | skip)

/--
`repeat' tac` recursively applies `tac` on all of the goals so long as it succeeds.
That is to say, if `tac` produces multiple subgoals, then `repeat' tac` is applied to each of them.

See also:
* `repeat tac` simply repeatedly applies `tac`.
* `repeat1' tac` is `repeat' tac` but requires that `tac` succeed for some goal at least once.
-/
syntax (name := repeat') "repeat' " tacticSeq : tactic

/--
`repeat1' tac` recursively applies to `tac` on all of the goals so long as it succeeds,
but `repeat1' tac` fails if `tac` succeeds on none of the initial goals.

See also:
* `repeat tac` simply applies `tac` repeatedly.
* `repeat' tac` is like `repeat1' tac` but it does not require that `tac` succeed at least once.
-/
syntax (name := repeat1') "repeat1' " tacticSeq : tactic

/--
`trivial` tries different simple tactics (e.g., `rfl`, `contradiction`, ...)
to close the current goal.
You can use the command `macro_rules` to extend the set of tactics used. Example:
```
macro_rules | `(tactic| trivial) => `(tactic| simp)
```
-/
syntax "trivial" : tactic

/--
`classical tacs` runs `tacs` in a scope where `Classical.propDecidable` is a low priority
local instance.

Note that `classical` is a scoping tactic: it adds the instance only within the
scope of the tactic.
-/
syntax (name := classical) "classical" ppDedent(tacticSeq) : tactic

/--
The `split` tactic is useful for breaking nested if-then-else and `match` expressions into separate cases.
For a `match` expression with `n` cases, the `split` tactic generates at most `n` subgoals.

For example, given `n : Nat`, and a target `if n = 0 then Q else R`, `split` will generate
one goal with hypothesis `n = 0` and target `Q`, and a second goal with hypothesis
`¬n = 0` and target `R`.  Note that the introduced hypothesis is unnamed, and is commonly
renamed used the `case` or `next` tactics.

- `split` will split the goal (target).
- `split at h` will split the hypothesis `h`.
-/
syntax (name := split) "split" (ppSpace colGt term)? (location)? : tactic

/-- `dbg_trace "foo"` prints `foo` when elaborated.
Useful for debugging tactic control flow:
```
example : False ∨ True := by
  first
  | apply Or.inl; trivial; dbg_trace "left"
  | apply Or.inr; trivial; dbg_trace "right"
```
-/
syntax (name := dbgTrace) "dbg_trace " str : tactic

/--
`stop` is a helper tactic for "discarding" the rest of a proof:
it is defined as `repeat sorry`.
It is useful when working on the middle of a complex proofs,
and less messy than commenting the remainder of the proof.
-/
macro "stop" tacticSeq : tactic => `(tactic| repeat sorry)

/--
The tactic `specialize h a₁ ... aₙ` works on local hypothesis `h`.
The premises of this hypothesis, either universal quantifications or
non-dependent implications, are instantiated by concrete terms coming
from arguments `a₁` ... `aₙ`.
The tactic adds a new hypothesis with the same name `h := h a₁ ... aₙ`
and tries to clear the previous one.
-/
syntax (name := specialize) "specialize " term : tactic

/--
`unhygienic tacs` runs `tacs` with name hygiene disabled.
This means that tactics that would normally create inaccessible names will instead
make regular variables. **Warning**: Tactics may change their variable naming
strategies at any time, so code that depends on autogenerated names is brittle.
Users should try not to use `unhygienic` if possible.
```
example : ∀ x : Nat, x = x := by unhygienic
  intro            -- x would normally be intro'd as inaccessible
  exact Eq.refl x  -- refer to x
```
-/
macro "unhygienic " t:tacticSeq : tactic => `(tactic| set_option tactic.hygienic false in $t)

/--
`checkpoint tac` acts the same as `tac`, but it caches the input and output of `tac`,
and if the file is re-elaborated and the input matches, the tactic is not re-run and
its effects are reapplied to the state. This is useful for improving responsiveness
when working on a long tactic proof, by wrapping expensive tactics with `checkpoint`.

See the `save` tactic, which may be more convenient to use.

(TODO: do this automatically and transparently so that users don't have to use
this combinator explicitly.)
-/
syntax (name := checkpoint) "checkpoint " tacticSeq : tactic

/--
`save` is defined to be the same as `skip`, but the elaborator has
special handling for occurrences of `save` in tactic scripts and will transform
`by tac1; save; tac2` to `by (checkpoint tac1); tac2`, meaning that the effect of `tac1`
will be cached and replayed. This is useful for improving responsiveness
when working on a long tactic proof, by using `save` after expensive tactics.

(TODO: do this automatically and transparently so that users don't have to use
this combinator explicitly.)
-/
macro (name := save) "save" : tactic => `(tactic| skip)

/--
The tactic `sleep ms` sleeps for `ms` milliseconds and does nothing.
It is used for debugging purposes only.
-/
syntax (name := sleep) "sleep " num : tactic

/--
`exists e₁, e₂, ...` is shorthand for `refine ⟨e₁, e₂, ...⟩; try trivial`.
It is useful for existential goals.
-/
macro "exists " es:term,+ : tactic =>
  `(tactic| (refine ⟨$es,*, ?_⟩; try trivial))

/--
Apply congruence (recursively) to goals of the form `⊢ f as = f bs` and `⊢ HEq (f as) (f bs)`.
The optional parameter is the depth of the recursive applications.
This is useful when `congr` is too aggressive in breaking down the goal.
For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
`congr` produces the goals `⊢ x = y` and `⊢ y = x`,
while `congr 2` produces the intended `⊢ x + y = y + x`.
-/
syntax (name := congr) "congr" (ppSpace num)? : tactic


/--
In tactic mode, `if h : t then tac1 else tac2` can be used as alternative syntax for:
```
by_cases h : t
· tac1
· tac2
```
It performs case distinction on `h : t` or `h : ¬t` and `tac1` and `tac2` are the subproofs.

You can use `?_` or `_` for either subproof to delay the goal to after the tactic, but
if a tactic sequence is provided for `tac1` or `tac2` then it will require the goal to be closed
by the end of the block.
-/
syntax (name := tacDepIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("if " binderIdent " : " term " then") ppSpace matchRhsTacticSeq)
    ppDedent(ppSpace) ppRealFill("else " matchRhsTacticSeq)) : tactic

/--
In tactic mode, `if t then tac1 else tac2` is alternative syntax for:
```
by_cases t
· tac1
· tac2
```
It performs case distinction on `h† : t` or `h† : ¬t`, where `h†` is an anonymous
hypothesis, and `tac1` and `tac2` are the subproofs. (It doesn't actually use
nondependent `if`, since this wouldn't add anything to the context and hence would be
useless for proving theorems. To actually insert an `ite` application use
`refine if t then ?_ else ?_`.)
-/
syntax (name := tacIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("if " term " then") ppSpace matchRhsTacticSeq)
    ppDedent(ppSpace) ppRealFill("else " matchRhsTacticSeq)) : tactic

/--
The tactic `nofun` is shorthand for `exact nofun`: it introduces the assumptions, then performs an
empty pattern match, closing the goal if the introduced pattern is impossible.
-/
macro "nofun" : tactic => `(tactic| exact nofun)

/--
The tactic `nomatch h` is shorthand for `exact nomatch h`.
-/
macro "nomatch " es:term,+ : tactic =>
  `(tactic| exact nomatch $es:term,*)

/--
Acts like `have`, but removes a hypothesis with the same name as
this one if possible. For example, if the state is:

```lean
f : α → β
h : α
⊢ goal
```

Then after `replace h := f h` the state will be:

```lean
f : α → β
h : β
⊢ goal
```

whereas `have h := f h` would result in:

```lean
f : α → β
h† : α
h : β
⊢ goal
```

This can be used to simulate the `specialize` and `apply at` tactics of Coq.
-/
syntax (name := replace) "replace" haveDecl : tactic

/-- `and_intros` applies `And.intro` until it does not make progress. -/
syntax "and_intros" : tactic
macro_rules | `(tactic| and_intros) => `(tactic| repeat' refine And.intro ?_ ?_)

/--
`subst_eq` repeatedly substitutes according to the equality proof hypotheses in the context,
replacing the left side of the equality with the right, until no more progress can be made.
-/
syntax (name := substEqs) "subst_eqs" : tactic

/-- The `run_tac doSeq` tactic executes code in `TacticM Unit`. -/
syntax (name := runTac) "run_tac " doSeq : tactic

/-- `haveI` behaves like `have`, but inlines the value instead of producing a `let_fun` term. -/
macro "haveI" d:haveDecl : tactic => `(tactic| refine_lift haveI $d:haveDecl; ?_)

/-- `letI` behaves like `let`, but inlines the value instead of producing a `let_fun` term. -/
macro "letI" d:haveDecl : tactic => `(tactic| refine_lift letI $d:haveDecl; ?_)

/--
Configuration for the `decide` tactic family.
-/
structure DecideConfig where
  /-- If true (default: false), then use only kernel reduction when reducing the `Decidable` instance.
  This is more efficient, since the default mode reduces twice (once in the elaborator and again in the kernel),
  however kernel reduction ignores transparency settings. The `decide!` tactic is a synonym for `decide +kernel`. -/
  kernel : Bool := false
  /-- If true (default: false), then uses the native code compiler to evaluate the `Decidable` instance,
  admitting the result via the axiom `Lean.ofReduceBool`.  This can be significantly more efficient,
  but it is at the cost of increasing the trusted code base, namely the Lean compiler
  and all definitions with an `@[implemented_by]` attribute.
  The instance is only evaluated once. The `native_decide` tactic is a synonym for `decide +native`. -/
  native : Bool := false
  /-- If true (default: true), then when preprocessing the goal, do zeta reduction to attempt to eliminate free variables. -/
  zetaReduce : Bool := true
  /-- If true (default: false), then when preprocessing reverts free variables. -/
  revert : Bool := false

/--
`decide` attempts to prove the main goal (with target type `p`) by synthesizing an instance of `Decidable p`
and then reducing that instance to evaluate the truth value of `p`.
If it reduces to `isTrue h`, then `h` is a proof of `p` that closes the goal.

The target is not allowed to contain local variables or metavariables.
If there are local variables, you can first try using the `revert` tactic with these local variables to move them into the target,
or you can use the `+revert` option, described below.

Options:
- `decide +revert` begins by reverting local variables that the target depends on,
  after cleaning up the local context of irrelevant variables.
  A variable is *relevant* if it appears in the target, if it appears in a relevant variable,
  or if it is a proposition that refers to a relevant variable.
- `decide +kernel` uses kernel for reduction instead of the elaborator.
  It has two key properties: (1) since it uses the kernel, it ignores transparency and can unfold everything,
  and (2) it reduces the `Decidable` instance only once instead of twice.
- `decide +native` uses the native code compiler (`#eval`) to evaluate the `Decidable` instance,
  admitting the result via the `Lean.ofReduceBool` axiom.
  This can be significantly more efficient than using reduction, but it is at the cost of increasing the size
  of the trusted code base.
  Namely, it depends on the correctness of the Lean compiler and all definitions with an `@[implemented_by]` attribute.
  Like with `+kernel`, the `Decidable` instance is evaluated only once.

Limitation: In the default mode or `+kernel` mode, since `decide` uses reduction to evaluate the term,
`Decidable` instances defined by well-founded recursion might not work because evaluating them requires reducing proofs.
Reduction can also get stuck on `Decidable` instances with `Eq.rec` terms.
These can appear in instances defined using tactics (such as `rw` and `simp`).
To avoid this, create such instances using definitions such as `decidable_of_iff` instead.

## Examples

Proving inequalities:
```lean
example : 2 + 2 ≠ 5 := by decide
```

Trying to prove a false proposition:
```lean
example : 1 ≠ 1 := by decide
/-
tactic 'decide' proved that the proposition
  1 ≠ 1
is false
-/
```

Trying to prove a proposition whose `Decidable` instance fails to reduce
```lean
opaque unknownProp : Prop

open scoped Classical in
example : unknownProp := by decide
/-
tactic 'decide' failed for proposition
  unknownProp
since its 'Decidable' instance reduced to
  Classical.choice ⋯
rather than to the 'isTrue' constructor.
-/
```

## Properties and relations

For equality goals for types with decidable equality, usually `rfl` can be used in place of `decide`.
```lean
example : 1 + 1 = 2 := by decide
example : 1 + 1 = 2 := by rfl
```
-/
syntax (name := decide) "decide" optConfig : tactic

/--
`decide!` is a variant of the `decide` tactic that uses kernel reduction to prove the goal.
It has the following properties:
- Since it uses kernel reduction instead of elaborator reduction, it ignores transparency and can unfold everything.
- While `decide` needs to reduce the `Decidable` instance twice (once during elaboration to verify whether the tactic succeeds,
  and once during kernel type checking), the `decide!` tactic reduces it exactly once.

The `decide!` syntax is short for `decide +kernel`.
-/
syntax (name := decideBang) "decide!" optConfig : tactic

/--
`native_decide` is a synonym for `decide +native`.
It will attempt to prove a goal of type `p` by synthesizing an instance
of `Decidable p` and then evaluating it to `isTrue ..`. Unlike `decide`, this
uses `#eval` to evaluate the decidability instance.

This should be used with care because it adds the entire lean compiler to the trusted
part, and the axiom `Lean.ofReduceBool` will show up in `#print axioms` for theorems using
this method or anything that transitively depends on them. Nevertheless, because it is
compiled, this can be significantly more efficient than using `decide`, and for very
large computations this is one way to run external programs and trust the result.
```lean
example : (List.range 1000).length = 1000 := by native_decide
```
-/
syntax (name := nativeDecide) "native_decide" optConfig : tactic

macro_rules | `(tactic| trivial) => `(tactic| assumption)
macro_rules | `(tactic| trivial) => `(tactic| rfl)
macro_rules | `(tactic| trivial) => `(tactic| contradiction)
macro_rules | `(tactic| trivial) => `(tactic| decide)
macro_rules | `(tactic| trivial) => `(tactic| apply True.intro)
macro_rules | `(tactic| trivial) => `(tactic| apply And.intro <;> trivial)

/--
The `omega` tactic, for resolving integer and natural linear arithmetic problems.

It is not yet a full decision procedure (no "dark" or "grey" shadows),
but should be effective on many problems.

We handle hypotheses of the form `x = y`, `x < y`, `x ≤ y`, and `k ∣ x` for `x y` in `Nat` or `Int`
(and `k` a literal), along with negations of these statements.

We decompose the sides of the inequalities as linear combinations of atoms.

If we encounter `x / k` or `x % k` for literal integers `k` we introduce new auxiliary variables
and the relevant inequalities.

On the first pass, we do not perform case splits on natural subtraction.
If `omega` fails, we recursively perform a case split on
a natural subtraction appearing in a hypothesis, and try again.

The options
```
omega +splitDisjunctions +splitNatSub +splitNatAbs +splitMinMax
```
can be used to:
* `splitDisjunctions`: split any disjunctions found in the context,
  if the problem is not otherwise solvable.
* `splitNatSub`: for each appearance of `((a - b : Nat) : Int)`, split on `a ≤ b` if necessary.
* `splitNatAbs`: for each appearance of `Int.natAbs a`, split on `0 ≤ a` if necessary.
* `splitMinMax`: for each occurrence of `min a b`, split on `min a b = a ∨ min a b = b`
Currently, all of these are on by default.
-/
syntax (name := omega) "omega" optConfig : tactic

/--
`bv_omega` is `omega` with an additional preprocessor that turns statements about `BitVec` into statements about `Nat`.
Currently the preprocessor is implemented as `try simp only [bv_toNat] at *`.
`bv_toNat` is a `@[simp]` attribute that you can (cautiously) add to more theorems.
-/
macro "bv_omega" : tactic => `(tactic| (try simp only [bv_toNat] at *) <;> omega)

/-- Implementation of `ac_nf` (the full `ac_nf` calls `trivial` afterwards). -/
syntax (name := acNf0) "ac_nf0" (location)? : tactic

/-- Implementation of `norm_cast` (the full `norm_cast` calls `trivial` afterwards). -/
syntax (name := normCast0) "norm_cast0" (location)? : tactic

/-- `assumption_mod_cast` is a variant of `assumption` that solves the goal
using a hypothesis. Unlike `assumption`, it first pre-processes the goal and
each hypothesis to move casts as far outwards as possible, so it can be used
in more situations.

Concretely, it runs `norm_cast` on the goal. For each local hypothesis `h`, it also
normalizes `h` with `norm_cast` and tries to use that to close the goal. -/
macro "assumption_mod_cast" : tactic => `(tactic| norm_cast0 at * <;> assumption)

/--
The `norm_cast` family of tactics is used to normalize certain coercions (*casts*) in expressions.
- `norm_cast` normalizes casts in the target.
- `norm_cast at h` normalizes casts in hypothesis `h`.

The tactic is basically a version of `simp` with a specific set of lemmas to move casts
upwards in the expression.
Therefore even in situations where non-terminal `simp` calls are discouraged (because of fragility),
`norm_cast` is considered to be safe.
It also has special handling of numerals.

For instance, given an assumption
```lean
a b : ℤ
h : ↑a + ↑b < (10 : ℚ)
```
writing `norm_cast at h` will turn `h` into
```lean
h : a + b < 10
```

There are also variants of basic tactics that use `norm_cast` to normalize expressions during
their operation, to make them more flexible about the expressions they accept
(we say that it is a tactic *modulo* the effects of `norm_cast`):
- `exact_mod_cast` for `exact` and `apply_mod_cast` for `apply`.
  Writing `exact_mod_cast h` and `apply_mod_cast h` will normalize casts
  in the goal and `h` before using `exact h` or `apply h`.
- `rw_mod_cast` for `rw`. It applies `norm_cast` between rewrites.
- `assumption_mod_cast` for `assumption`.
  This is effectively `norm_cast at *; assumption`, but more efficient.
  It normalizes casts in the goal and, for every hypothesis `h` in the context,
  it will try to normalize casts in `h` and use `exact h`.

See also `push_cast`, which moves casts inwards rather than lifting them outwards.
-/
macro "norm_cast" loc:(location)? : tactic =>
  `(tactic| norm_cast0 $[$loc]? <;> try trivial)

/--
`ac_nf` normalizes equalities up to application of an associative and commutative operator.
- `ac_nf` normalizes all hypotheses and the goal target of the goal.
- `ac_nf at l` normalizes at location(s) `l`, where `l` is either `*` or a
  list of hypotheses in the local context. In the latter case, a turnstile `⊢` or `|-`
  can also be used, to signify the target of the goal.
```
instance : Associative (α := Nat) (.+.) := ⟨Nat.add_assoc⟩
instance : Commutative (α := Nat) (.+.) := ⟨Nat.add_comm⟩

example (a b c d : Nat) : a + b + c + d = d + (b + c) + a := by
 ac_nf
 -- goal: a + (b + (c + d)) = a + (b + (c + d))
```
-/
macro "ac_nf" loc:(location)? : tactic =>
  `(tactic| ac_nf0 $[$loc]? <;> try trivial)

/--
`push_cast` rewrites the goal to move certain coercions (*casts*) inward, toward the leaf nodes.
This uses `norm_cast` lemmas in the forward direction.
For example, `↑(a + b)` will be written to `↑a + ↑b`.
- `push_cast` moves casts inward in the goal.
- `push_cast at h` moves casts inward in the hypothesis `h`.
It can be used with extra simp lemmas with, for example, `push_cast [Int.add_zero]`.

Example:
```lean
example (a b : Nat)
    (h1 : ((a + b : Nat) : Int) = 10)
    (h2 : ((a + b + 0 : Nat) : Int) = 10) :
    ((a + b : Nat) : Int) = 10 := by
  /-
  h1 : ↑(a + b) = 10
  h2 : ↑(a + b + 0) = 10
  ⊢ ↑(a + b) = 10
  -/
  push_cast
  /- Now
  ⊢ ↑a + ↑b = 10
  -/
  push_cast at h1
  push_cast [Int.add_zero] at h2
  /- Now
  h1 h2 : ↑a + ↑b = 10
  -/
  exact h1
```

See also `norm_cast`.
-/
syntax (name := pushCast) "push_cast" optConfig (discharger)? (&" only")?
  (" [" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic

/--
`norm_cast_add_elim foo` registers `foo` as an elim-lemma in `norm_cast`.
-/
syntax (name := normCastAddElim) "norm_cast_add_elim" ident : command

/--
* `symm` applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation,
  that is, a relation which has a symmetry lemma tagged with the attribute [symm].
  It replaces the target with `u ~ t`.
* `symm at h` will rewrite a hypothesis `h : t ~ u` to `h : u ~ t`.
-/
syntax (name := symm) "symm" (location)? : tactic

/-- For every hypothesis `h : a ~ b` where a `@[symm]` lemma is available,
add a hypothesis `h_symm : b ~ a`. -/
syntax (name := symmSaturate) "symm_saturate" : tactic

namespace SolveByElim

/-- Syntax for omitting a local hypothesis in `solve_by_elim`. -/
syntax erase := "-" term:max
/-- Syntax for including all local hypotheses in `solve_by_elim`. -/
syntax star := "*"
/-- Syntax for adding or removing a term, or `*`, in `solve_by_elim`. -/
syntax arg := star <|> erase <|> term
/-- Syntax for adding and removing terms in `solve_by_elim`. -/
syntax args := " [" SolveByElim.arg,* "]"
/-- Syntax for using all lemmas labelled with an attribute in `solve_by_elim`. -/
syntax using_ := " using " ident,*

end SolveByElim

section SolveByElim
open SolveByElim (args using_)

/--
`solve_by_elim` calls `apply` on the main goal to find an assumption whose head matches
and then repeatedly calls `apply` on the generated subgoals until no subgoals remain,
performing at most `maxDepth` (defaults to 6) recursive steps.

`solve_by_elim` discharges the current goal or fails.

`solve_by_elim` performs backtracking if subgoals can not be solved.

By default, the assumptions passed to `apply` are the local context, `rfl`, `trivial`,
`congrFun` and `congrArg`.

The assumptions can be modified with similar syntax as for `simp`:
* `solve_by_elim [h₁, h₂, ..., hᵣ]` also applies the given expressions.
* `solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context,
  `rfl`, `trivial`, `congrFun`, or `congrArg` unless they are explicitly included.
* `solve_by_elim [-h₁, ... -hₙ]` removes the given local hypotheses.
* `solve_by_elim using [a₁, ...]` uses all lemmas which have been labelled
  with the attributes `aᵢ` (these attributes must be created using `register_label_attr`).

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.
(Adding or removing local hypotheses may not be well-behaved when starting with multiple goals.)

Optional arguments passed via a configuration argument as `solve_by_elim (config := { ... })`
- `maxDepth`: number of attempts at discharging generated subgoals
- `symm`: adds all hypotheses derived by `symm` (defaults to `true`).
- `exfalso`: allow calling `exfalso` and trying again if `solve_by_elim` fails
  (defaults to `true`).
- `transparency`: change the transparency mode when calling `apply`. Defaults to `.default`,
  but it is often useful to change to `.reducible`,
  so semireducible definitions will not be unfolded when trying to apply a lemma.

See also the doc-comment for `Lean.Meta.Tactic.Backtrack.BacktrackConfig` for the options
`proc`, `suspend`, and `discharge` which allow further customization of `solve_by_elim`.
Both `apply_assumption` and `apply_rules` are implemented via these hooks.
-/
syntax (name := solveByElim)
  "solve_by_elim" "*"? optConfig (&" only")? (args)? (using_)? : tactic

/--
`apply_assumption` looks for an assumption of the form `... → ∀ _, ... → head`
where `head` matches the current goal.

You can specify additional rules to apply using `apply_assumption [...]`.
By default `apply_assumption` will also try `rfl`, `trivial`, `congrFun`, and `congrArg`.
If you don't want these, or don't want to use all hypotheses, use `apply_assumption only [...]`.
You can use `apply_assumption [-h]` to omit a local hypothesis.
You can use `apply_assumption using [a₁, ...]` to use all lemmas which have been labelled
with the attributes `aᵢ` (these attributes must be created using `register_label_attr`).

`apply_assumption` will use consequences of local hypotheses obtained via `symm`.

If `apply_assumption` fails, it will call `exfalso` and try again.
Thus if there is an assumption of the form `P → ¬ Q`, the new tactic state
will have two goals, `P` and `Q`.

You can pass a further configuration via the syntax `apply_rules (config := {...}) lemmas`.
The options supported are the same as for `solve_by_elim` (and include all the options for `apply`).
-/
syntax (name := applyAssumption)
  "apply_assumption" optConfig (&" only")? (args)? (using_)? : tactic

/--
`apply_rules [l₁, l₂, ...]` tries to solve the main goal by iteratively
applying the list of lemmas `[l₁, l₂, ...]` or by applying a local hypothesis.
If `apply` generates new goals, `apply_rules` iteratively tries to solve those goals.
You can use `apply_rules [-h]` to omit a local hypothesis.

`apply_rules` will also use `rfl`, `trivial`, `congrFun` and `congrArg`.
These can be disabled, as can local hypotheses, by using `apply_rules only [...]`.

You can use `apply_rules using [a₁, ...]` to use all lemmas which have been labelled
with the attributes `aᵢ` (these attributes must be created using `register_label_attr`).

You can pass a further configuration via the syntax `apply_rules (config := {...})`.
The options supported are the same as for `solve_by_elim` (and include all the options for `apply`).

`apply_rules` will try calling `symm` on hypotheses and `exfalso` on the goal as needed.
This can be disabled with `apply_rules (config := {symm := false, exfalso := false})`.

You can bound the iteration depth using the syntax `apply_rules (config := {maxDepth := n})`.

Unlike `solve_by_elim`, `apply_rules` does not perform backtracking, and greedily applies
a lemma from the list until it gets stuck.
-/
syntax (name := applyRules) "apply_rules" optConfig (&" only")? (args)? (using_)? : tactic
end SolveByElim

/--
Searches environment for definitions or theorems that can solve the goal using `exact`
with conditions resolved by `solve_by_elim`.

The optional `using` clause provides identifiers in the local context that must be
used by `exact?` when closing the goal.  This is most useful if there are multiple
ways to resolve the goal, and one wants to guide which lemma is used.
-/
syntax (name := exact?) "exact?" (" using " (colGt ident),+)? : tactic

/--
Searches environment for definitions or theorems that can refine the goal using `apply`
with conditions resolved when possible with `solve_by_elim`.

The optional `using` clause provides identifiers in the local context that must be
used when closing the goal.
-/
syntax (name := apply?) "apply?" (" using " (colGt term),+)? : tactic

/--
Syntax for excluding some names, e.g. `[-my_lemma, -my_theorem]`.
-/
syntax rewrites_forbidden := " [" (("-" ident),*,?) "]"

/--
`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [← h]`.

You can use `rw? [-my_lemma, -my_theorem]` to prevent `rw?` using the named lemmas.
-/
syntax (name := rewrites?) "rw?" (ppSpace location)? (rewrites_forbidden)? : tactic

/--
`show_term tac` runs `tac`, then prints the generated term in the form
"exact X Y Z" or "refine X ?_ Z" if there are remaining subgoals.

(For some tactics, the printed term will not be human readable.)
-/
syntax (name := showTerm) "show_term " tacticSeq : tactic

/--
`show_term e` elaborates `e`, then prints the generated term.
-/
macro (name := showTermElab) tk:"show_term " t:term : term =>
  `(term| no_implicit_lambda% (show_term_elab%$tk $t))

/--
The command `by?` will print a suggestion for replacing the proof block with a proof term
using `show_term`.
-/
macro (name := by?) tk:"by?" t:tacticSeq : term => `(show_term%$tk by%$tk $t)

end Tactic

namespace Attr
/--
Theorems tagged with the `simp` attribute are used by the simplifier
(i.e., the `simp` tactic, and its variants) to simplify expressions occurring in your goals.
We call theorems tagged with the `simp` attribute "simp theorems" or "simp lemmas".
Lean maintains a database/index containing all active simp theorems.
Here is an example of a simp theorem.
```lean
@[simp] theorem ne_eq (a b : α) : (a ≠ b) = Not (a = b) := rfl
```
This simp theorem instructs the simplifier to replace instances of the term
`a ≠ b` (e.g. `x + 0 ≠ y`) with `Not (a = b)` (e.g., `Not (x + 0 = y)`).
The simplifier applies simp theorems in one direction only:
if `A = B` is a simp theorem, then `simp` replaces `A`s with `B`s,
but it doesn't replace `B`s with `A`s. Hence a simp theorem should have the
property that its right-hand side is "simpler" than its left-hand side.
In particular, `=` and `↔` should not be viewed as symmetric operators in this situation.
The following would be a terrible simp theorem (if it were even allowed):
```lean
@[simp] lemma mul_right_inv_bad (a : G) : 1 = a * a⁻¹ := ...
```
Replacing 1 with a * a⁻¹ is not a sensible default direction to travel.
Even worse would be a theorem that causes expressions to grow without bound,
causing simp to loop forever.

By default the simplifier applies `simp` theorems to an expression `e`
after its sub-expressions have been simplified.
We say it performs a bottom-up simplification.
You can instruct the simplifier to apply a theorem before its sub-expressions
have been simplified by using the modifier `↓`. Here is an example
```lean
@[simp↓] theorem not_and_eq (p q : Prop) : (¬ (p ∧ q)) = (¬p ∨ ¬q) :=
```

You can instruct the simplifier to rewrite the lemma from right-to-left:
```lean
attribute @[simp ←] and_assoc
```

When multiple simp theorems are applicable, the simplifier uses the one with highest priority.
The equational theorems of function are applied at very low priority (100 and below).
If there are several with the same priority, it is uses the "most recent one". Example:
```lean
@[simp high] theorem cond_true (a b : α) : cond true a b = a := rfl
@[simp low+1] theorem or_true (p : Prop) : (p ∨ True) = True :=
  propext <| Iff.intro (fun _ => trivial) (fun _ => Or.inr trivial)
@[simp 100] theorem ite_self {d : Decidable c} (a : α) : ite c a a = a := by
  cases d <;> rfl
```
-/
syntax (name := simp) "simp" (Tactic.simpPre <|> Tactic.simpPost)? patternIgnore("← " <|> "<- ")? (ppSpace prio)? : attr

/--
Theorems tagged with the `grind_norm` attribute are used by the `grind` tactic normalizer/pre-processor.
-/
syntax (name := grind_norm) "grind_norm" (Tactic.simpPre <|> Tactic.simpPost)? (ppSpace prio)? : attr

/--
Simplification procedures tagged with the `grind_norm_proc` attribute are used by the `grind` tactic normalizer/pre-processor.
-/
syntax (name := grind_norm_proc) "grind_norm_proc" (Tactic.simpPre <|> Tactic.simpPost)? : attr


/-- The possible `norm_cast` kinds: `elim`, `move`, or `squash`. -/
syntax normCastLabel := &"elim" <|> &"move" <|> &"squash"

/--
The `norm_cast` attribute should be given to lemmas that describe the
behaviour of a coercion with respect to an operator, a relation, or a particular
function.

It only concerns equality or iff lemmas involving `↑`, `⇑` and `↥`, describing the behavior of
the coercion functions.
It does not apply to the explicit functions that define the coercions.

Examples:
```lean
@[norm_cast] theorem coe_nat_inj' {m n : ℕ} : (↑m : ℤ) = ↑n ↔ m = n

@[norm_cast] theorem coe_int_denom (n : ℤ) : (n : ℚ).denom = 1

@[norm_cast] theorem cast_id : ∀ n : ℚ, ↑n = n

@[norm_cast] theorem coe_nat_add (m n : ℕ) : (↑(m + n) : ℤ) = ↑m + ↑n

@[norm_cast] theorem cast_coe_nat (n : ℕ) : ((n : ℤ) : α) = n

@[norm_cast] theorem cast_one : ((1 : ℚ) : α) = 1
```

Lemmas tagged with `@[norm_cast]` are classified into three categories: `move`, `elim`, and
`squash`. They are classified roughly as follows:

* elim lemma:   LHS has 0 head coes and ≥ 1 internal coe
* move lemma:   LHS has 1 head coe and 0 internal coes,    RHS has 0 head coes and ≥ 1 internal coes
* squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes

`norm_cast` uses `move` and `elim` lemmas to factor coercions toward the root of an expression
and to cancel them from both sides of an equation or relation. It uses `squash` lemmas to clean
up the result.

It is typically not necessary to specify these categories, as `norm_cast` lemmas are
automatically classified by default. The automatic classification can be overridden by
giving an optional `elim`, `move`, or `squash` parameter to the attribute.

```lean
@[simp, norm_cast elim] lemma nat_cast_re (n : ℕ) : (n : ℂ).re = n := by
  rw [← of_real_nat_cast, of_real_re]
```

Don't do this unless you understand what you are doing.
-/
syntax (name := norm_cast) "norm_cast" (ppSpace normCastLabel)? (ppSpace num)? : attr

end Attr

end Parser
end Lean

/--
`‹t›` resolves to an (arbitrary) hypothesis of type `t`.
It is useful for referring to hypotheses without accessible names.
`t` may contain holes that are solved by unification with the expected type;
in particular, `‹_›` is a shortcut for `by assumption`.
-/
syntax "‹" withoutPosition(term) "›" : term
macro_rules | `(‹$type›) => `((by assumption : $type))

/--
`get_elem_tactic_trivial` is an extensible tactic automatically called
by the notation `arr[i]` to prove any side conditions that arise when
constructing the term (e.g. the index is in bounds of the array).
The default behavior is to just try `trivial` (which handles the case
where `i < arr.size` is in the context) and `simp_arith` and `omega`
(for doing linear arithmetic in the index).
-/
syntax "get_elem_tactic_trivial" : tactic

macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| omega)
macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| simp +arith; done)
macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| trivial)

/--
`get_elem_tactic` is the tactic automatically called by the notation `arr[i]`
to prove any side conditions that arise when constructing the term
(e.g. the index is in bounds of the array). It just delegates to
`get_elem_tactic_trivial` and gives a diagnostic error message otherwise;
users are encouraged to extend `get_elem_tactic_trivial` instead of this tactic.
-/
macro "get_elem_tactic" : tactic =>
  `(tactic| first
      /-
      Recall that `macro_rules` are tried in reverse order.
      We want `assumption` to be tried first.
      This is important for theorems such as
      ```
      [simp] theorem getElem_pop (a : Array α) (i : Nat) (hi : i < a.pop.size) :
      a.pop[i] = a[i]'(Nat.lt_of_lt_of_le (a.size_pop ▸ hi) (Nat.sub_le _ _)) :=
      ```
      There is a proof embedded in the right-hand-side, and we want it to be just `hi`.
      If `omega` is used to "fill" this proof, we will have a more complex proof term that
      cannot be inferred by unification.
      We hardcoded `assumption` here to ensure users cannot accidentally break this IF
      they add new `macro_rules` for `get_elem_tactic_trivial`.

      TODO: Implement priorities for `macro_rules`.
      TODO: Ensure we have a **high-priority** macro_rules for `get_elem_tactic_trivial` which is just `assumption`.
      -/
    | assumption
    | get_elem_tactic_trivial
    | fail "failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid"
   )

/--
Searches environment for definitions or theorems that can be substituted in
for `exact?%` to solve the goal.
 -/
syntax (name := Lean.Parser.Syntax.exact?) "exact?%" : term

set_option linter.unusedVariables.funArgs false in
/--
  Gadget for automatic parameter support. This is similar to the `optParam` gadget, but it uses
  the given tactic.
  Like `optParam`, this gadget only affects elaboration.
  For example, the tactic will *not* be invoked during type class resolution. -/
abbrev autoParam.{u} (α : Sort u) (tactic : Lean.Syntax) : Sort u := α
