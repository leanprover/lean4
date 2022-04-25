/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Notation for operators defined at Prelude.lean
-/
prelude
import Init.Prelude

-- DSL for specifying parser precedences and priorities

namespace Lean.Parser.Syntax

syntax:65 (name := addPrec) prec " + " prec:66 : prec
syntax:65 (name := subPrec) prec " - " prec:66 : prec

syntax:65 (name := addPrio) prio " + " prio:66 : prio
syntax:65 (name := subPrio) prio " - " prio:66 : prio

end Lean.Parser.Syntax

macro "max"  : prec => `(1024) -- maximum precedence used in term parsers, in particular for terms in function position (`ident`, `paren`, ...)
macro "arg"  : prec => `(1023) -- precedence used for application arguments (`do`, `by`, ...)
macro "lead" : prec => `(1022) -- precedence used for terms not supposed to be used as arguments (`let`, `have`, ...)
macro "(" p:prec ")" : prec => return p
macro "min"  : prec => `(10)   -- minimum precedence used in term parsers
macro "min1" : prec => `(11)   -- `(min+1) we can only `min+1` after `Meta.lean`
/-
  `max:prec` as a term. It is equivalent to `eval_prec max` for `eval_prec` defined at `Meta.lean`.
  We use `max_prec` to workaround bootstrapping issues. -/
macro "max_prec" : term => `(1024)

macro "default" : prio => `(1000)
macro "low"     : prio => `(100)
macro "mid"     : prio => `(1000)
macro "high"    : prio => `(10000)
macro "(" p:prio ")" : prio => return p

-- Basic notation for defining parsers
-- NOTE: precedence must be at least `arg` to be used in `macro` without parentheses
syntax:arg stx:max "+" : stx
syntax:arg stx:max "*" : stx
syntax:arg stx:max "?" : stx
syntax:2 stx:2 " <|> " stx:1 : stx

macro_rules
  | `(stx| $p +) => `(stx| many1($p))
  | `(stx| $p *) => `(stx| many($p))
  | `(stx| $p ?) => `(stx| optional($p))
  | `(stx| $p₁ <|> $p₂) => `(stx| orelse($p₁, $p₂))

/- Comma-separated sequence. -/
macro:arg x:stx:max ",*"   : stx => `(stx| sepBy($x, ",", ", "))
macro:arg x:stx:max ",+"   : stx => `(stx| sepBy1($x, ",", ", "))
/- Comma-separated sequence with optional trailing comma. -/
macro:arg x:stx:max ",*,?" : stx => `(stx| sepBy($x, ",", ", ", allowTrailingSep))
macro:arg x:stx:max ",+,?" : stx => `(stx| sepBy1($x, ",", ", ", allowTrailingSep))

macro:arg "!" x:stx:max : stx => `(stx| notFollowedBy($x))

syntax (name := rawNatLit) "nat_lit " num : term

infixr:90 " ∘ "  => Function.comp
infixr:35 " × "  => Prod

infixl:55 " ||| " => HOr.hOr
infixl:58 " ^^^ " => HXor.hXor
infixl:60 " &&& " => HAnd.hAnd
infixl:65 " + "   => HAdd.hAdd
infixl:65 " - "   => HSub.hSub
infixl:70 " * "   => HMul.hMul
infixl:70 " / "   => HDiv.hDiv
infixl:70 " % "   => HMod.hMod
infixl:75 " <<< " => HShiftLeft.hShiftLeft
infixl:75 " >>> " => HShiftRight.hShiftRight
infixr:80 " ^ "   => HPow.hPow
infixl:65 " ++ "  => HAppend.hAppend
prefix:100 "-"    => Neg.neg
prefix:100 "~~~"  => Complement.complement
/-
  Remark: the infix commands above ensure a delaborator is generated for each relations.
  We redefine the macros below to be able to use the auxiliary `binop%` elaboration helper for binary operators.
  It addresses issue #382. -/
macro_rules | `($x ||| $y) => `(binop% HOr.hOr $x $y)
macro_rules | `($x ^^^ $y) => `(binop% HXor.hXor $x $y)
macro_rules | `($x &&& $y) => `(binop% HAnd.hAnd $x $y)
macro_rules | `($x + $y)   => `(binop% HAdd.hAdd $x $y)
macro_rules | `($x - $y)   => `(binop% HSub.hSub $x $y)
macro_rules | `($x * $y)   => `(binop% HMul.hMul $x $y)
macro_rules | `($x / $y)   => `(binop% HDiv.hDiv $x $y)
macro_rules | `($x ++ $y)  => `(binop% HAppend.hAppend $x $y)

-- declare ASCII alternatives first so that the latter Unicode unexpander wins
infix:50 " <= " => LE.le
infix:50 " ≤ "  => LE.le
infix:50 " < "  => LT.lt
infix:50 " >= " => GE.ge
infix:50 " ≥ "  => GE.ge
infix:50 " > "  => GT.gt
infix:50 " = "  => Eq
infix:50 " == " => BEq.beq
/-
  Remark: the infix commands above ensure a delaborator is generated for each relations.
  We redefine the macros below to be able to use the auxiliary `binrel%` elaboration helper for binary relations.
  It has better support for applying coercions. For example, suppose we have `binrel% Eq n i` where `n : Nat` and
  `i : Int`. The default elaborator fails because we don't have a coercion from `Int` to `Nat`, but
  `binrel%` succeeds because it also tries a coercion from `Nat` to `Int` even when the nat occurs before the int. -/
macro_rules | `($x <= $y) => `(binrel% LE.le $x $y)
macro_rules | `($x ≤ $y)  => `(binrel% LE.le $x $y)
macro_rules | `($x < $y)  => `(binrel% LT.lt $x $y)
macro_rules | `($x > $y)  => `(binrel% GT.gt $x $y)
macro_rules | `($x >= $y) => `(binrel% GE.ge $x $y)
macro_rules | `($x ≥ $y)  => `(binrel% GE.ge $x $y)
macro_rules | `($x = $y)  => `(binrel% Eq $x $y)
macro_rules | `($x == $y) => `(binrel_no_prop% BEq.beq $x $y)

infixr:35 " /\\ " => And
infixr:35 " ∧ "   => And
infixr:30 " \\/ " => Or
infixr:30 " ∨  "  => Or
notation:max "¬" p:40 => Not p

infixl:35 " && " => and
infixl:30 " || " => or
notation:max "!" b:40 => not b

infix:50 " ∈ " => Membership.mem
notation:50 a:50 " ∉ " b:50 => ¬ (a ∈ b)

infixr:67 " :: " => List.cons
syntax:20 term:21 " <|> " term:20 : term
syntax:60 term:61 " >> " term:60 : term
infixl:55  " >>= " => Bind.bind
notation:60 a:60 " <*> " b:61 => Seq.seq a fun _ : Unit => b
notation:60 a:60 " <* " b:61 => SeqLeft.seqLeft a fun _ : Unit => b
notation:60 a:60 " *> " b:61 => SeqRight.seqRight a fun _ : Unit => b
infixr:100 " <$> " => Functor.map

macro_rules | `($x <|> $y) => `(binop_lazy% HOrElse.hOrElse $x $y)
macro_rules | `($x >> $y)  => `(binop_lazy% HAndThen.hAndThen $x $y)

syntax (name := termDepIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("if " ident " : " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(if $h:ident : $c then $t:term else $e:term) => `(let_mvar% ?m := $c; wait_if_type_mvar% ?m; dite ?m (fun $h:ident => $t) (fun $h:ident => $e))

syntax (name := termIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("if " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(if $c then $t:term else $e:term) => `(let_mvar% ?m := $c; wait_if_type_mvar% ?m; ite ?m $t $e)

macro "if " "let " pat:term " := " d:term " then " t:term " else " e:term : term =>
  `(match $d:term with | $pat:term => $t | _ => $e)

syntax (name := boolIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("bif " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(bif $c then $t:term else $e:term) => `(cond $c $t $e)

syntax:min term " <| " term:min : term

macro_rules
  | `($f $args* <| $a) => let args := args.push a; `($f $args*)
  | `($f <| $a) => `($f $a)

syntax:min term " |> " term:min1 : term

macro_rules
  | `($a |> $f $args*) => let args := args.push a; `($f $args*)
  | `($a |> $f)        => `($f $a)

-- Haskell-like pipe <|
-- Note that we have a whitespace after `$` to avoid an ambiguity with the antiquotations.
syntax:min term atomic(" $" ws) term:min : term

macro_rules
  | `($f $args* $ $a) => let args := args.push a; `($f $args*)
  | `($f $ $a) => `($f $a)

syntax "{ " ident (" : " term)? " // " term " }" : term

macro_rules
  | `({ $x : $type // $p }) => ``(Subtype (fun ($x:ident : $type) => $p))
  | `({ $x // $p })         => ``(Subtype (fun ($x:ident : _) => $p))

/-
  `without_expected_type t` instructs Lean to elaborate `t` without an expected type.
  Recall that terms such as `match ... with ...` and `⟨...⟩` will postpone elaboration until
  expected type is known. So, `without_expected_type` is not effective in this case. -/
macro "without_expected_type " x:term : term => `(let aux := $x; aux)

syntax "[" term,* "]"  : term
syntax "%[" term,* "|" term "]" : term -- auxiliary notation for creating big list literals

namespace Lean

macro_rules
  | `([ $elems,* ]) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : Syntax) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← ``(List.cons $(elems.elemsAndSeps[i]) $result))
    if elems.elemsAndSeps.size < 64 then
      expandListLit elems.elemsAndSeps.size false (← ``(List.nil))
    else
      `(%[ $elems,* | List.nil ])

-- Declare `this` as a keyword that unhygienically binds to a scope-less `this` assumption (or other binding).
-- The keyword prevents declaring a `this` binding except through metapgrogramming, as is done by `have`/`show`.
/-- Special identifier introduced by "anonymous" `have : ...`, `suffices p ...` etc. -/
macro tk:"this" : term => return Syntax.ident tk.getHeadInfo "this".toSubstring `this []

namespace Parser.Tactic
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
syntax (name := case) "case " (ident <|> "_") (ident <|> "_")* " => " tacticSeq : tactic
/--
Similar to the `case tag => tac` tactic but for writing macros. Recall that `case` closes the goal using `sorry` when it fails,
and the tactic execution is not interrupted.
-/
syntax (name := case') "case' " (ident <|> "_") (ident <|> "_")* " => " tacticSeq : tactic

/--
`next => tac` focuses on the next goal solves it using `tac`, or else fails.
`next x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses with inaccessible names to the given names. -/
macro "next " args:(ident <|> "_")* " => " tac:tacticSeq : tactic => `(tactic| case _ $args* => $tac)

/-- `allGoals tac` runs `tac` on each goal, concatenating the resulting goals, if any. -/
syntax (name := allGoals) "all_goals " tacticSeq : tactic
/-- `anyGoals tac` applies the tactic `tac` to every goal, and succeeds if at least one application succeeds.  -/
syntax (name := anyGoals) "any_goals " tacticSeq : tactic
/--
`focus tac` focuses on the main goal, suppressing all other goals, and runs `tac` on it.
Usually `· tac`, which enforces that the goal is closed by `tac`, should be preferred. -/
syntax (name := focus) "focus " tacticSeq : tactic
/-- `skip` does nothing. -/
syntax (name := skip) "skip" : tactic
/-- `done` succeeds iff there are no remaining goals. -/
syntax (name := done) "done" : tactic
/-- This tactic displays the current state in the info view. -/
syntax (name := traceState) "trace_state" : tactic
/-- `trace msg` displays `msg` in the info view. -/
syntax (name := traceMessage) "trace " str : tactic
/-- Fails if the given tactic succeeds. -/
syntax (name := failIfSuccess) "fail_if_success " tacticSeq : tactic
syntax (name := paren) "(" tacticSeq ")" : tactic
syntax (name := withReducible) "with_reducible " tacticSeq : tactic
syntax (name := withReducibleAndInstances) "with_reducible_and_instances " tacticSeq : tactic
syntax (name := withUnfoldingAll) "with_unfolding_all " tacticSeq : tactic
/-- `first | tac | ...` runs each `tac` until one succeeds, or else fails. -/
syntax (name := first) "first " withPosition((group(colGe "|" tacticSeq))+) : tactic
syntax (name := rotateLeft) "rotate_left" (num)? : tactic
syntax (name := rotateRight) "rotate_right" (num)? : tactic
/-- `try tac` runs `tac` and succeeds even if `tac` failed. -/
macro "try " t:tacticSeq : tactic => `(first | $t | skip)
/-- `tac <;> tac'` runs `tac` on the main goal and `tac'` on each produced goal, concatenating all goals produced by `tac'`. -/
macro:1 x:tactic " <;> " y:tactic:0 : tactic => `(tactic| focus ($x:tactic; all_goals $y:tactic))

/-- `eq_refl` is equivalent to `exact rfl`, but has a few optimizatons. -/
syntax (name := refl) "eq_refl" : tactic

/--
This tactic tries to close the current goal using reflexivity.
This is supposed to be an extensible tactic and users can add their own support
to new reflexive relations.
-/
macro "rfl" : tactic => `(eq_refl)

/--
  Similar to `rfl`, but disables smart unfolding and unfolds all kinds of definitions,
  theorems included (relevant for declarations defined by well-founded recursion). -/
macro "rfl'" : tactic => `(set_option smartUnfolding false in with_unfolding_all rfl)

syntax (name := ac_refl) "ac_refl " : tactic

/-- `admit` is a shorthand for `exact sorry`. -/
macro "admit" : tactic => `(exact sorry)
/-- The `sorry` tactic is a shorthand for `exact sorry`. -/
macro "sorry" : tactic => `(exact sorry)
/-- `infer_instance` is an abbreviation for `exact inferInstance` -/
macro "infer_instance" : tactic => `(exact inferInstance)

/-- Optional configuration option for tactics -/
syntax config := atomic("(" &"config") " := " term ")"

syntax locationWildcard := "*"
syntax locationHyp      := (colGt term:max)+ ("⊢" <|> "|-")?
syntax location         := withPosition(" at " (locationWildcard <|> locationHyp))

syntax (name := change) "change " term (location)? : tactic
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
An abbreviation for `rewrite`.
-/
syntax (name := rwSeq) "rw " (config)? rwRuleSeq (location)? : tactic

def rwWithRfl (kind : SyntaxNodeKind) (atom : String) (stx : Syntax) : MacroM Syntax := do
  -- We show the `rfl` state on `]`
  let seq   := stx[2]
  let rbrak := seq[2]
  -- Replace `]` token with one without position information in the expanded tactic
  let seq   := seq.setArg 2 (mkAtom "]")
  let tac   := stx.setKind kind |>.setArg 0 (mkAtomFrom stx atom) |>.setArg 2 seq
  `(tactic| $tac; try (with_reducible rfl%$rbrak))

@[macro rwSeq] def expandRwSeq : Macro :=
  rwWithRfl ``Lean.Parser.Tactic.rewriteSeq "rewrite"

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
A stronger version of `simp [*] at *` where the hypotheses and target are simplified
multiple times until no simplication is applicable.
Only non-dependent propositional hypotheses are considered.
-/
syntax (name := simpAll) "simp_all " (config)? (discharger)? (&"only ")? ("[" (simpErase <|> simpLemma),* "]")? : tactic

/--
The `dsimp` tactic is the definitional simplifier. It is similar to `simp` but only applies theorems that hold by
reflexivity. Thus, the result is guaranteed to be definitionally equal to the input.
-/
syntax (name := dsimp) "dsimp " (config)? (discharger)? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic

/--
  Delta expand the given definition.
  This is a low-level tactic, it will expose how recursive definitions have been compiled by Lean. -/
syntax (name := delta) "delta " ident (location)? : tactic
/--
  Unfold definition. For non-recursive definitions, this tactic is identical to `delta`.
  For recursive definitions, it hides the encoding tricks used by the Lean frontend to convince the
  kernel that the definition terminates. -/
syntax (name := unfold) "unfold " ident (location)? : tactic

-- Auxiliary macro for lifting have/suffices/let/...
-- It makes sure the "continuation" `?_` is the main goal after refining
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
macro (priority := high) "have" x:ident " := " p:term : tactic => `(have $x:ident : _ := $p)
/--
Given a main goal `ctx |- t`, `suffices h : t' from e` replaces the main goal with `ctx |- t'`,
`e` must have type `t` in the context `ctx, h : t'`.

The variant `suffices h : t' by tac` is a shorthand for `suffices h : t' from by tac`.
If `h :` is omitted, the name `this` is used.
 -/
macro "suffices " d:sufficesDecl : tactic => `(refine_lift suffices $d:sufficesDecl; ?_)
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
macro "show " e:term : tactic => `(refine_lift show $e:term from ?_) -- TODO: fix, see comment
syntax (name := letrec) withPosition(atomic(group("let " &"rec ")) letRecDecls) : tactic
macro_rules
  | `(tactic| let rec $d:letRecDecls) => `(tactic| refine_lift let rec $d:letRecDecls; ?_)

-- Similar to `refineLift`, but using `refine'`
macro "refine_lift' " e:term : tactic => `(focus (refine' no_implicit_lambda% $e; rotate_right))
macro "have' " d:haveDecl : tactic => `(refine_lift' have $d:haveDecl; ?_)
macro (priority := high) "have'" x:ident " := " p:term : tactic => `(have' $x:ident : _ := $p)
macro "let' " d:letDecl : tactic => `(refine_lift' let $d:letDecl; ?_)

syntax inductionAlt  := ppDedent(ppLine) "| " (group("@"? ident) <|> "_") (ident <|> "_")* " => " (hole <|> syntheticHole <|> tacticSeq)
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
syntax (name := renameI) "rename_i " (colGt (ident <|> "_"))+ : tactic

/--
`repeat tac` applies `tac` to main goal. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.
-/
syntax "repeat " tacticSeq : tactic
macro_rules
  | `(tactic| repeat $seq) => `(tactic| first | ($seq); repeat $seq | skip)

/--
Tries different simple tactics (e.g., `rfl`, `contradiction`, ...) to close the current goal.
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

syntax (name := dbgTrace) "dbg_trace " str : tactic

/-- Helper tactic for "discarding" the rest of a proof. It is useful when working on the middle of a complex proofs,
    and less messy than commenting the remainder of the proof. -/
macro "stop" s:tacticSeq : tactic => `(repeat sorry)

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

macro "unhygienic " t:tacticSeq : tactic => `(set_option tactic.hygienic false in $t:tacticSeq)

/-- `fail msg` is a tactic that always fail and produces an error using the given message. -/
syntax (name := fail) "fail " (str)? : tactic

syntax (name := checkpoint) "checkpoint " tacticSeq : tactic

macro (name := save) "save" : tactic => `(skip)

/-- The tactic `sleep ms` sleeps for `ms` milliseconds and does nothing. It is used for debugging purposes only. -/
syntax (name := sleep) "sleep" num : tactic

/-- `exists e₁, e₂, ...` is shorthand for `refine ⟨e₁, e₂, ...⟩; try trivial`. It is useful for existential goals. -/
macro "exists " es:term,+ : tactic =>
  `(tactic| (refine ⟨$es,*, ?_⟩; try trivial))

end Tactic

namespace Attr
-- simp attribute syntax
syntax (name := simp) "simp" (Tactic.simpPre <|> Tactic.simpPost)? (prio)? : attr
end Attr

end Parser
end Lean

macro "‹" type:term "›" : term => `((by assumption : $type))
