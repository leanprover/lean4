/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Notation

namespace Lean

syntax binderIdent := ident <|> "_"

namespace Parser.Tactic
/-- `with_annotate_state stx t` annotates the lexical range of `stx : Syntax` with the initial and final state of running tactic `t`. -/
scoped syntax (name := withAnnotateState) "with_annotate_state " rawStx ppSpace tactic : tactic

/--
Introduce one or more hypotheses, optionally naming and/or pattern-matching them.
For each hypothesis to be introduced, the remaining main goal's target type must be a `let` or function type.
* `intro` by itself introduces one anonymous hypothesis, which can be accessed by e.g. `assumption`.
* `intro x y` introduces two hypotheses and names them. Individual hypotheses can be anonymized via `_`,
  or matched against a pattern:
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
syntax (name := intro) "intro " notFollowedBy("|") (colGt term:max)* : tactic
/-- `intros x...` behaves like `intro x...`, but then keeps introducing (anonymous) hypotheses until goal is not of a function type. -/
syntax (name := intros) "intros " (colGt (ident <|> "_"))* : tactic
/--
`rename t => x` renames the most recent hypothesis whose type matches `t` (which may contain placeholders) to `x`,
or fails if no such hypothesis could be found. -/
syntax (name := rename) "rename " term " => " ident : tactic
/-- `revert x...` is the inverse of `intro x...`: it moves the given hypotheses into the main goal's target type. -/
syntax (name := revert) "revert " (colGt term:max)+ : tactic
/-- `clear x...` removes the given hypotheses, or fails if there are remaining references to a hypothesis. -/
syntax (name := clear) "clear " (colGt term:max)+ : tactic
/--
`subst x...` substitutes each `x` with `e` in the goal if there is a hypothesis of type `x = e` or `e = x`.
If `x` is itself a hypothesis of type `y = e` or `e = y`, `y` is substituted instead. -/
syntax (name := subst) "subst " (colGt term:max)+ : tactic
/--
Apply `subst` to all hypotheses of the form `h : x = t` or `h : t = x`.
-/
syntax (name := substVars) "subst_vars" : tactic

/--
`assumption` tries to solve the main goal using a hypothesis of compatible type, or else fails.
Note also the `‹t›` term notation, which is a shorthand for `show t by assumption`. -/
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
`apply e` tries to match the current goal against the conclusion of `e`'s type.
If it succeeds, then the tactic returns as many subgoals as the number of premises that
have not been fixed by type inference or type class resolution.
Non-dependent premises are added before dependent ones.

The `apply` tactic uses higher-order pattern matching, type class resolution, and first-order unification with dependent types.
-/
syntax (name := apply) "apply " term : tactic
/--
`exact e` closes the main goal if its target type matches that of `e`.
-/
syntax (name := exact) "exact " term : tactic
/--
`refine e` behaves like `exact e`, except that named (`?x`) or unnamed (`?_`) holes in `e` that are not solved
by unification with the main goal's target type are converted into new goals, using the hole's name, if any, as the goal case name.
-/
syntax (name := refine) "refine " term : tactic
/-- `refine' e` behaves like `refine e`, except that unsolved placeholders (`_`) and implicit parameters are also converted into new goals. -/
syntax (name := refine') "refine' " term : tactic
/-- If the main goal's target type is an inductive type, `constructor` solves it with the first matching constructor, or else fails. -/
syntax (name := constructor) "constructor" : tactic
/--
`case tag => tac` focuses on the goal with case name `tag` and solves it using `tac`, or else fails.
`case tag x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses with inaccessible names to the given names. -/
syntax (name := case) "case " binderIdent binderIdent* " => " tacticSeq : tactic
/--
`case'` is similar to the `case tag => tac` tactic, but does not ensure the goal has been solved after applying `tac`, nor
admits the goal if `tac` failed. Recall that `case` closes the goal using `sorry` when `tac` fails, and
the tactic execution is not interrupted.
-/
syntax (name := case') "case' " binderIdent binderIdent* " => " tacticSeq : tactic

/--
`next => tac` focuses on the next goal solves it using `tac`, or else fails.
`next x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses with inaccessible names to the given names. -/
macro "next " args:binderIdent* " => " tac:tacticSeq : tactic => `(tactic| case _ $args* => $tac)

/-- `all_goals tac` runs `tac` on each goal, concatenating the resulting goals, if any. -/
syntax (name := allGoals) "all_goals " tacticSeq : tactic
/-- `any_goals tac` applies the tactic `tac` to every goal, and succeeds if at least one application succeeds.  -/
syntax (name := anyGoals) "any_goals " tacticSeq : tactic
/--
`focus tac` focuses on the main goal, suppressing all other goals, and runs `tac` on it.
Usually `· tac`, which enforces that the goal is closed by `tac`, should be preferred. -/
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
/-- `(tacs)` executes a list of tactics in sequence, without requiring that
the goal be closed at the end like `· tacs`. Like `by` itself, the tactics
can be either separated by newlines or `;`. -/
syntax (name := paren) "(" tacticSeq ")" : tactic
/-- `with_reducible tacs` excutes `tacs` using the reducible transparency setting.
In this setting only definitions tagged as `[reducible]` are unfolded. -/
syntax (name := withReducible) "with_reducible " tacticSeq : tactic
/-- `with_reducible_and_instances tacs` excutes `tacs` using the `.instances` transparency setting.
In this setting only definitions tagged as `[reducible]` or type class instances are unfolded. -/
syntax (name := withReducibleAndInstances) "with_reducible_and_instances " tacticSeq : tactic
/-- `with_unfolding_all tacs` excutes `tacs` using the `.all` transparency setting.
In this setting all definitions that are not opaque are unfolded. -/
syntax (name := withUnfoldingAll) "with_unfolding_all " tacticSeq : tactic
/-- `first | tac | ...` runs each `tac` until one succeeds, or else fails. -/
syntax (name := first) "first " withPosition((colGe "|" tacticSeq)+) : tactic
/-- `rotate_left n` rotates goals to the left by `n`. That is, `rotate_left 1`
takes the main goal and puts it to the back of the subgoal list.
If `n` is omitted, it defaults to `1`. -/
syntax (name := rotateLeft) "rotate_left" (num)? : tactic
/-- Rotate the goals to the right by `n`. That is, take the goal at the back
and push it to the front `n` times. If `n` is omitted, it defaults to `1`. -/
syntax (name := rotateRight) "rotate_right" (num)? : tactic
/-- `try tac` runs `tac` and succeeds even if `tac` failed. -/
macro "try " t:tacticSeq : tactic => `(first | $t | skip)
/-- `tac <;> tac'` runs `tac` on the main goal and `tac'` on each produced goal, concatenating all goals produced by `tac'`. -/
macro:1 x:tactic tk:" <;> " y:tactic:0 : tactic => `(tactic|
  focus
    $x:tactic
    -- annotate token with state after executing `x`
    with_annotate_state $tk skip
    all_goals $y:tactic)

/-- `eq_refl` is equivalent to `exact rfl`, but has a few optimizations. -/
syntax (name := refl) "eq_refl" : tactic

/--
`rfl` tries to close the current goal using reflexivity.
This is supposed to be an extensible tactic and users can add their own support
for new reflexive relations.
-/
macro "rfl" : tactic => `(eq_refl)

/--
  `rfl'` is similar to `rfl`, but disables smart unfolding and unfolds all kinds of definitions,
  theorems included (relevant for declarations defined by well-founded recursion). -/
macro "rfl'" : tactic => `(set_option smartUnfolding false in with_unfolding_all rfl)

/-- `ac_rfl` proves equalities up to application of an associative and commutative operator.
```
instance : IsAssociative (α := Nat) (.+.) := ⟨Nat.add_assoc⟩
instance : IsCommutative (α := Nat) (.+.) := ⟨Nat.add_comm⟩

example (a b c d : Nat) : a + b + c + d = d + (b + c) + a := by ac_rfl
```
-/
syntax (name := acRfl) "ac_rfl" : tactic

/-- `admit` is a shorthand for `exact sorry`. -/
macro "admit" : tactic => `(exact @sorryAx _ false)
/-- The `sorry` tactic is a shorthand for `exact sorry`. -/
macro "sorry" : tactic => `(exact @sorryAx _ false)
/-- `infer_instance` is an abbreviation for `exact inferInstance` -/
macro "infer_instance" : tactic => `(exact inferInstance)

/-- Optional configuration option for tactics -/
syntax config := atomic("(" &"config") " := " term ")"

syntax locationWildcard := "*"
syntax locationHyp      := (colGt term:max)+ ("⊢" <|> "|-")?
syntax location         := withPosition(" at " (locationWildcard <|> locationHyp))

/--
* `change tgt'` will change the goal from `tgt` to `tgt'`,
  assuming these are definitionally equal.
* `change t' at h` will change hypothesis `h : t` to have type `t'`, assuming
  assuming `t` and `t'` are definitionally equal.
-/
syntax (name := change) "change " term (location)? : tactic

/--
* `change a with b` will change occurrences of `a` to `b` in the goal,
  assuming `a` and `b` are are definitionally equal.
* `change a with b at h` similarly changes `a` to `b` in the type of hypothesis `h`.
-/
syntax (name := changeWith) "change " term " with " term (location)? : tactic

syntax rwRule    := ("← " <|> "<- ")? term
syntax rwRuleSeq := "[" rwRule,*,? "]"

/--
`rewrite [e]` applies identity `e` as a rewrite rule to the target of the main goal.
If `e` is preceded by left arrow (`←` or `<-`), the rewrite is applied in the reverse direction.
If `e` is a defined constant, then the equational theorems associated with `e` are used. This provides a convenient way to unfold `e`.
- `rewrite [e₁, ..., eₙ]` applies the given rules sequentially.
- `rewrite [e] at l` rewrites `e` at location(s) `l`, where `l` is either `*` or a list of hypotheses in the local context. In the latter case, a turnstile `⊢` or `|-` can also be used, to signify the target of the goal.
-/
syntax (name := rewriteSeq) "rewrite " (config)? rwRuleSeq (location)? : tactic

/--
`rw` is like `rewrite`, but also tries to close the goal by "cheap" (reducible) `rfl` afterwards.
-/
macro (name := rwSeq) rw:"rw " c:(config)? s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [%$lbrak $rs,* ]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| rewrite%$rw $(c)? [%$lbrak $rs,*] $(l)?; try (with_reducible rfl%$rbrak))
  | _ => Macro.throwUnsupported

/--
The `injection` tactic is based on the fact that constructors of inductive data types are injections.
That means that if `c` is a constructor of an inductive datatype, and if `(c t₁)` and `(c t₂)` are two terms that are equal then  `t₁` and `t₂` are equal too.
If `q` is a proof of a statement of conclusion `t₁ = t₂`, then injection applies injectivity to derive the equality of all arguments of `t₁` and `t₂`
placed in the same positions. For example, from `(a::b) = (c::d)` we derive `a=c` and `b=d`. To use this tactic `t₁` and `t₂`
should be constructor applications of the same constructor.
Given `h : a::b = c::d`, the tactic `injection h` adds two new hypothesis with types `a = c` and `b = d` to the main goal.
The tactic `injection h with h₁ h₂` uses the names `h₁` and `h₂` to name the new hypotheses.
-/
syntax (name := injection) "injection " term (" with " (colGt (ident <|> "_"))+)? : tactic

/-- `injections` applies `injection` to all hypotheses recursively
(since `injection` can produce new hypotheses). Useful for destructing nested
constructor equalities like `(a::b::c) = (d::e::f)`. -/
-- TODO: add with
syntax (name := injections) "injections" : tactic

syntax discharger := atomic("(" (&"discharger" <|> &"disch")) " := " tacticSeq ")"

syntax simpPre   := "↓"
syntax simpPost  := "↑"
syntax simpLemma := (simpPre <|> simpPost)? ("← " <|> "<- ")? term
syntax simpErase := "-" term:max
syntax simpStar  := "*"
/--
The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or non-dependent hypotheses. It has many variants.
- `simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.
- `simp [h₁, h₂, ..., hₙ]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and the given `hᵢ`'s, where the `hᵢ`'s are expressions. If an `hᵢ` is a defined constant `f`, then the equational lemmas associated with `f` are used. This provides a convenient way to unfold `f`.
- `simp [*]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and all hypotheses.
- `simp only [h₁, h₂, ..., hₙ]` is like `simp [h₁, h₂, ..., hₙ]` but does not use `[simp]` lemmas
- `simp [-id₁, ..., -idₙ]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]`, but removes the ones named `idᵢ`.
- `simp at h₁ h₂ ... hₙ` simplifies the hypotheses `h₁ : T₁` ... `hₙ : Tₙ`. If the target or another hypothesis depends on `hᵢ`, a new simplified hypothesis `hᵢ` is introduced, but the old one remains in the local context.
- `simp at *` simplifies all the hypotheses and the target.
- `simp [*] at *` simplifies target and all (propositional) hypotheses using the other hypotheses.
-/
syntax (name := simp) "simp " (config)? (discharger)? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic
/--
`simp_all` is a stronger version of `simp [*] at *` where the hypotheses and target are simplified
multiple times until no simplication is applicable.
Only non-dependent propositional hypotheses are considered.
-/
syntax (name := simpAll) "simp_all " (config)? (discharger)? (&"only ")? ("[" (simpErase <|> simpLemma),* "]")? : tactic

/--
The `dsimp` tactic is the definitional simplifier. It is similar to `simp` but only applies theorems that hold by
reflexivity. Thus, the result is guaranteed to be definitionally equal to the input.
-/
syntax (name := dsimp) "dsimp " (config)? (discharger)? (&"only ")? ("[" (simpErase <|> simpLemma),* "]")? (location)? : tactic

/--
  `delta id` delta-expands the definition `id`.
  This is a low-level tactic, it will expose how recursive definitions have been compiled by Lean. -/
syntax (name := delta) "delta " ident (location)? : tactic
/--
  `unfold id,+` unfolds definition `id`. For non-recursive definitions, this tactic is identical to `delta`.
  For recursive definitions, it hides the encoding tricks used by the Lean frontend to convince the
  kernel that the definition terminates. -/
syntax (name := unfold) "unfold " ident,+ (location)? : tactic

/-- Auxiliary macro for lifting have/suffices/let/...
  It makes sure the "continuation" `?_` is the main goal after refining. -/
macro "refine_lift " e:term : tactic => `(focus (refine no_implicit_lambda% $e; rotate_right))

/--
`have h : t := e` adds the hypothesis `h : t` to the current goal if `e` a term of type `t`. If `t` is omitted, it will be inferred.
If `h` is omitted, the name `this` is used.
The variant `have pattern := e` is equivalent to `match e with | pattern => _`, and it is convenient for types that have only applicable constructor.
Example: given `h : p ∧ q ∧ r`, `have ⟨h₁, h₂, h₃⟩ := h` produces the hypotheses `h₁ : p`, `h₂ : q`, and `h₃ : r`.
-/
macro "have " d:haveDecl : tactic => `(refine_lift have $d:haveDecl; ?_)

/--
`have h := e` adds the hypothesis `h : t` if `e : t`.
-/
macro (priority := high) "have" x:ident " := " p:term : tactic => `(have $x : _ := $p)
/--
Given a main goal `ctx |- t`, `suffices h : t' from e` replaces the main goal with `ctx |- t'`,
`e` must have type `t` in the context `ctx, h : t'`.

The variant `suffices h : t' by tac` is a shorthand for `suffices h : t' from by tac`.
If `h :` is omitted, the name `this` is used.
 -/
macro "suffices " d:sufficesDecl : tactic => `(refine_lift suffices $d; ?_)
/--
`let h : t := e` adds the hypothesis `h : t := e` to the current goal if `e` a term of type `t`.
If `t` is omitted, it will be inferred.
The variant `let pattern := e` is equivalent to `match e with | pattern => _`, and it is convenient for types that have only applicable constructor.
Example: given `h : p ∧ q ∧ r`, `let ⟨h₁, h₂, h₃⟩ := h` produces the hypotheses `h₁ : p`, `h₂ : q`, and `h₃ : r`.
-/
macro "let " d:letDecl : tactic => `(refine_lift let $d:letDecl; ?_)
/--
`show t` finds the first goal whose target unifies with `t`. It makes that the main goal,
 performs the unification, and replaces the target with the unified version of `t`.
-/
macro "show " e:term : tactic => `(refine_lift show $e from ?_) -- TODO: fix, see comment
/-- `let rec f : t := e` adds a recursive definition `f` to the current goal.
The syntax is the same as term-mode `let rec`. -/
syntax (name := letrec) withPosition(atomic("let " &"rec ") letRecDecls) : tactic
macro_rules
  | `(tactic| let rec $d) => `(tactic| refine_lift let rec $d; ?_)

/-- Similar to `refine_lift`, but using `refine'` -/
macro "refine_lift' " e:term : tactic => `(focus (refine' no_implicit_lambda% $e; rotate_right))
/-- Similar to `have`, but using `refine'` -/
macro "have' " d:haveDecl : tactic => `(refine_lift' have $d:haveDecl; ?_)
/-- Similar to `have`, but using `refine'` -/
macro (priority := high) "have'" x:ident " := " p:term : tactic => `(have' $x : _ := $p)
/-- Similar to `let`, but using `refine'` -/
macro "let' " d:letDecl : tactic => `(refine_lift' let $d:letDecl; ?_)

syntax inductionAltLHS := "| " (("@"? ident) <|> "_") (ident <|> "_")*
syntax inductionAlt  := ppDedent(ppLine) inductionAltLHS+ " => " (hole <|> syntheticHole <|> tacticSeq)
syntax inductionAlts := "with " (tactic)? withPosition( (colGe inductionAlt)+)
/--
Assuming `x` is a variable in the local context with an inductive type, `induction x` applies induction on `x` to the main goal,
producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor
and an inductive hypothesis is added for each recursive argument to the constructor.
If the type of an element in the local context depends on `x`, that element is reverted and reintroduced afterward,
so that the inductive hypothesis incorporates that hypothesis as well.
For example, given `n : Nat` and a goal with a hypothesis `h : P n` and target `Q n`, `induction n` produces one goal
with hypothesis `h : P 0` and target `Q 0`, and one goal with hypotheses `h : P (Nat.succ a)` and `ih₁ : P a → Q a` and target `Q (Nat.succ a)`.
Here the names `a` and `ih₁` are chosen automatically and are not accessible. You can use `with` to provide the variables names for each constructor.
- `induction e`, where `e` is an expression instead of a variable, generalizes `e` in the goal, and then performs induction on the resulting variable.
- `induction e using r` allows the user to specify the principle of induction that should be used. Here `r` should be a theorem whose result type must be of the form `C t`, where `C` is a bound variable and `t` is a (possibly empty) sequence of bound variables
- `induction e generalizing z₁ ... zₙ`, where `z₁ ... zₙ` are variables in the local context, generalizes over `z₁ ... zₙ` before applying the induction but then introduces them in each goal. In other words, the net effect is that each inductive hypothesis is generalized.
- Given `x : Nat`, `induction x with | zero => tac₁ | succ x' ih => tac₂` uses tactic `tac₁` for the `zero` case, and `tac₂` for the `succ` case.
-/
syntax (name := induction) "induction " term,+ (" using " ident)?  ("generalizing " (colGt term:max)+)? (inductionAlts)? : tactic

syntax generalizeArg := atomic(ident " : ")? term:51 " = " ident
/--
`generalize ([h :] e = x),+` replaces all occurrences `e`s in the main goal with a fresh hypothesis `x`s.
If `h` is given, `h : e = x` is introduced as well. -/
syntax (name := generalize) "generalize " generalizeArg,+ : tactic

syntax casesTarget := atomic(ident " : ")? term
/--
Assuming `x` is a variable in the local context with an inductive type, `cases x` splits the main goal,
producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor.
If the type of an element in the local context depends on `x`, that element is reverted and reintroduced afterward,
so that the case split affects that hypothesis as well. `cases` detects unreachable cases and closes them automatically.
For example, given `n : Nat` and a goal with a hypothesis `h : P n` and target `Q n`, `cases n` produces one goal with hypothesis `h : P 0` and target `Q 0`,
and one goal with hypothesis `h : P (Nat.succ a)` and target `Q (Nat.succ a)`. Here the name `a` is chosen automatically and are not accessible. You can use `with` to provide the variables names for each constructor.
- `cases e`, where `e` is an expression instead of a variable, generalizes `e` in the goal, and then cases on the resulting variable.
- Given `as : List α`, `cases as with | nil => tac₁ | cons a as' => tac₂`, uses tactic `tac₁` for the `nil` case, and `tac₂` for the `cons` case, and `a` and `as'` are used as names for the new variables introduced.
- `cases h : e`, where `e` is a variable or an expression, performs cases on `e` as above, but also adds a hypothesis `h : e = ...` to each hypothesis, where `...` is the constructor instance for that particular case.
-/
syntax (name := cases) "cases " casesTarget,+ (" using " ident)? (inductionAlts)? : tactic

/-- `rename_i x_1 ... x_n` renames the last `n` inaccessible names using the given names. -/
syntax (name := renameI) "rename_i " (colGt binderIdent)+ : tactic

/--
`repeat tac` applies `tac` to main goal. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.
-/
syntax "repeat " tacticSeq : tactic
macro_rules
  | `(tactic| repeat $seq) => `(tactic| first | ($seq); repeat $seq | skip)

/--
`trivial` tries different simple tactics (e.g., `rfl`, `contradiction`, ...) to close the current goal.
You can use the command `macro_rules` to extend the set of tactics used. Example:
```
macro_rules | `(tactic| trivial) => `(tactic| simp)
```
-/
syntax "trivial" : tactic

/--
The `split` tactic is useful for breaking nested if-then-else and match expressions in cases.
For a `match` expression with `n` cases, the `split` tactic generates at most `n` subgoals
-/
syntax (name := split) "split " (colGt term)? (location)? : tactic

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

/-- `stop` is a helper tactic for "discarding" the rest of a proof. It is useful when working on the middle of a complex proofs,
    and less messy than commenting the remainder of the proof. -/
macro "stop" tacticSeq : tactic => `(repeat sorry)

/--
The tactic `specialize h a₁ ... aₙ` works on local hypothesis `h`.
The premises of this hypothesis, either universal quantifications or non-dependent implications,
are instantiated by concrete terms coming either from arguments `a₁` ... `aₙ`.
The tactic adds a new hypothesis with the same name `h := h a₁ ... aₙ` and tries to clear the previous one.
-/
syntax (name := specialize) "specialize " term : tactic

macro_rules | `(tactic| trivial) => `(tactic| assumption)
macro_rules | `(tactic| trivial) => `(tactic| rfl)
macro_rules | `(tactic| trivial) => `(tactic| contradiction)
macro_rules | `(tactic| trivial) => `(tactic| decide)
macro_rules | `(tactic| trivial) => `(tactic| apply True.intro)
macro_rules | `(tactic| trivial) => `(tactic| apply And.intro <;> trivial)

/-- `unhygienic tacs` runs `tacs` with name hygiene disabled.
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
macro "unhygienic " t:tacticSeq : tactic => `(set_option tactic.hygienic false in $t)

/-- `fail msg` is a tactic that always fail and produces an error using the given message. -/
syntax (name := fail) "fail " (str)? : tactic

/-- `checkpoint tac` acts the same as `tac`, but it caches the input and output of `tac`,
and if the file is re-elaborated and the input matches, the tactic is not re-run and
its effects are reapplied to the state. This is useful for improving responsiveness
when working on a long tactic proof, by wrapping expensive tactics with `checkpoint`.

See the `save` tactic, which may be more convenient to use.

(TODO: do this automatically and transparently so that users don't have to use
this combinator explicitly.) -/
syntax (name := checkpoint) "checkpoint " tacticSeq : tactic

/-- `save` is defined to be the same as `skip`, but the elaborator has
special handling for occurrences of `save` in tactic scripts and will transform
`by tac1; save; tac2` to `by (checkpoint tac1); tac2`, meaning that the effect of `tac1`
will be cached and replayed. This is useful for improving responsiveness
when working on a long tactic proof, by using `save` after expensive tactics.

(TODO: do this automatically and transparently so that users don't have to use
this combinator explicitly.) -/
macro (name := save) "save" : tactic => `(skip)

/-- The tactic `sleep ms` sleeps for `ms` milliseconds and does nothing. It is used for debugging purposes only. -/
syntax (name := sleep) "sleep" num : tactic

/-- `exists e₁, e₂, ...` is shorthand for `refine ⟨e₁, e₂, ...⟩; try trivial`. It is useful for existential goals. -/
macro "exists " es:term,+ : tactic =>
  `(tactic| (refine ⟨$es,*, ?_⟩; try trivial))

end Tactic

namespace Attr
/--
Theorems tagged with the `simp` attribute are by the simplifier (i.e., the `simp` tactic, and its variants) to simplify
expressions occurring in your goals.
We call theorems tagged with the `simp` attribute "simp theorems" or "simp lemmas".
Lean maintains a database/index containing all active simp theorems.
Here is an example of a simp theorem.
```lean
@[simp] theorem ne_eq (a b : α) : (a ≠ b) = Not (a = b) := rfl
```
This simp theorem instructs the simplifier to replace instances of the term `a ≠ b` (e.g. `x + 0 ≠ y`) with `Not (a = b)`
(e.g., `Not (x + 0 = y)`).
The simplifier applies simp theorems in one direction only: if `A = B` is a simp theorem, then `simp`
replaces `A`s with `B`s, but it doesn't replace `B`s with `A`s. Hence a simp theorem should have the
property that its right-hand side is "simpler" than its left-hand side.
In particular, `=` and `↔` should not be viewed as symmetric operators in this situation.
The following would be a terrible simp theorem (if it were even allowed):
```lean
@[simp] lemma mul_right_inv_bad (a : G) : 1 = a * a⁻¹ := ...
```
Replacing 1 with a * a⁻¹ is not a sensible default direction to travel. Even worse would be a theorem
that causes expressions to grow without bound, causing simp to loop forever.

By default the simplifier applies `simp` theorems to an expression `e` after its sub-expressions have been simplified.
We say it performs a bottom-up simplification. You can instruct the simplifier to apply a theorem before its sub-expressions
have been simplified by using the modifier `↓`. Here is an example
```lean
@[simp↓] theorem not_and_eq (p q : Prop) : (¬ (p ∧ q)) = (¬p ∨ ¬q) :=
```

When multiple simp theorems are applicable, the simplifier uses the one with highest priority. If there are several with
the same priority, it is uses the "most recent one". Example:
```lean
@[simp high] theorem cond_true (a b : α) : cond true a b = a := rfl
@[simp low+1] theorem or_true (p : Prop) : (p ∨ True) = True := propext <| Iff.intro (fun _ => trivial) (fun _ => Or.inr trivial)
@[simp 100] theorem ite_self {d : Decidable c} (a : α) : ite c a a = a := by cases d  <;> rfl
```
-/
syntax (name := simp) "simp" (Tactic.simpPre <|> Tactic.simpPost)? (prio)? : attr
end Attr

end Parser
end Lean

/--
`‹t›` resolves to an (arbitrary) hypothesis of type `t`. It is useful for referring to hypotheses without accessible names.
`t` may contain holes that are solved by unification with the expected type; in particular, `‹_›` is a shortcut for `by assumption`. -/
macro "‹" type:term "›" : term => `((by assumption : $type))

/-- `get_elem_tactic_trivial` is an extensible tactic automatically called
by the notation `arr[i]` to prove any side conditions that arise when
constructing the term (e.g. the index is in bounds of the array).
The default behavior is to just try `trivial` (which handles the case
where `i < arr.size` is in the context) and `simp_arith`
(for doing linear arithmetic in the index). -/
syntax "get_elem_tactic_trivial" : tactic

macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| trivial)
macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| simp (config := { arith := true }); done)

/-- `get_elem_tactic` is the tactic automatically called by the notation `arr[i]`
to prove any side conditions that arise when constructing the term
(e.g. the index is in bounds of the array). It just delegates to
`get_elem_tactic_trivial` and gives a diagnostic error message otherwise;
users are encouraged to extend `get_elem_tactic_trivial` instead of this tactic. -/
macro "get_elem_tactic" : tactic =>
  `(first
    | get_elem_tactic_trivial
    | fail "failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is perfomed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid"
   )

macro:max x:term noWs "[" i:term "]" : term => `(getElem $x $i (by get_elem_tactic))

/-- Helper declaration for the unexpander -/
@[inline] def getElem' [GetElem cont idx elem dom] (xs : cont) (i : idx) (h : dom xs i) : elem :=
  getElem xs i h

macro x:term noWs "[" i:term "]'" h:term:max : term => `(getElem' $x $i $h)
