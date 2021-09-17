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
macro "(" p:prec ")" : prec => p
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
macro "(" p:prio ")" : prio => p

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
macro_rules | `($x == $y) => `(binrel% BEq.beq $x $y)

infixr:35 " /\\ " => And
infixr:35 " ∧ "   => And
infixr:30 " \\/ " => Or
infixr:30 " ∨  "  => Or
notation:max "¬" p:40 => Not p

infixl:35 " && " => and
infixl:30 " || " => or
notation:max "!" b:40 => not b

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

syntax (name := termDepIfThenElse) ppGroup(ppDedent("if " ident " : " term " then" ppSpace term ppDedent(ppSpace "else") ppSpace term)) : term

macro_rules
  | `(if $h:ident : $c then $t:term else $e:term) => ``(dite $c (fun $h:ident => $t) (fun $h:ident => $e))

syntax (name := termIfThenElse) ppGroup(ppDedent("if " term " then" ppSpace term ppDedent(ppSpace "else") ppSpace term)) : term

macro_rules
  | `(if $c then $t:term else $e:term) => ``(ite $c $t $e)

macro "if " "let " pat:term " := " d:term " then " t:term " else " e:term : term =>
  `(match $d:term with | $pat:term => $t | _ => $e)

syntax:min term "<|" term:min : term

macro_rules
  | `($f $args* <| $a) => let args := args.push a; `($f $args*)
  | `($f <| $a) => `($f $a)

syntax:min term "|>" term:min1 : term

macro_rules
  | `($a |> $f $args*) => let args := args.push a; `($f $args*)
  | `($a |> $f)        => `($f $a)

-- Haskell-like pipe <|
-- Note that we have a whitespace after `$` to avoid an ambiguity with the antiquotations.
syntax:min term atomic("$" ws) term:min : term

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

notation:50 e:51 " matches " p:51 => match e with | p => true | _ => false

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
syntax (name := revert) "revert " (colGt ident)+ : tactic
/-- `clear x...` removes the given hypotheses, or fails if there are remaining references to a hypothesis. -/
syntax (name := clear) "clear " (colGt ident)+ : tactic
/--
`subst x...` substitutes each `x` with `e` in the goal if there is a hypothesis of type `x = e` or `e = x`.
If `x` is itself a hypothesis of type `y = e` or `e = y`, `y` is substituted instead. -/
syntax (name := subst) "subst " (colGt ident)+ : tactic
/--
`assumption` tries to solve the main goal using a hypothesis of compatible type, or else fails.
Note also the `‹t›` term notation, which is a shorthand for `show t by assumption`. -/
syntax (name := assumption) "assumption" : tactic
/--
`contradiction` closes the main goal if its hypotheses are "trivially contradictory".
```lean
example (h : False) : p := by contradiction  -- inductive type/family with no applicable constructors
example (h : none = some true) : p := by contradiction  -- injectivity of constructors
example (h : 2 + 2 = 3) : p := by contradiction  -- decidable false proposition
example (h : p) (h' : ¬ p) : q := by contradiction
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
`next => tac` focuses on the next goal solves it using `tac`, or else fails.
`next x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses with inaccessible names to the given names. -/
macro "next " args:(ident <|> "_")* " => " tac:tacticSeq : tactic => `(tactic| case _ $(args.getArgs)* => $tac)

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
syntax (name := traceState) "trace_state" : tactic
syntax (name := failIfSuccess) "fail_if_success " tacticSeq : tactic
syntax (name := paren) "(" tacticSeq ")" : tactic
syntax (name := withReducible) "with_reducible " tacticSeq : tactic
syntax (name := withReducibleAndInstances) "with_reducible_and_instances " tacticSeq : tactic
/-- `first | tac | ...` runs each `tac` until one succeeds, or else fails. -/
syntax (name := first) "first " withPosition((group(colGe "|" tacticSeq))+) : tactic
syntax (name := rotateLeft) "rotate_left" (num)? : tactic
syntax (name := rotateRight) "rotate_right" (num)? : tactic
/-- `try tac` runs `tac` and succeeds even if `tac` failed. -/
macro "try " t:tacticSeq : tactic => `(first | $t | skip)
/-- `tac <;> tac'` runs `tac` on the main goal and `tac'` on each produced goal, concatenating all goals produced by `tac'`. -/
macro:1 x:tactic " <;> " y:tactic:0 : tactic => `(tactic| focus ($x:tactic; all_goals $y:tactic))

/-- `· tac` focuses on the main goal and tries to solve it using `tac`, or else fails. -/
macro dot:("·" <|> ".") ts:tacticSeq : tactic => `(tactic| {%$dot ($ts:tacticSeq) })

/-- `rfl` is a shorthand for `exact rfl`. -/
macro "rfl" : tactic => `(exact rfl)
/-- `admit` is a shorthand for `exact sorry`. -/
macro "admit" : tactic => `(exact sorry)
/-- The `sorry` tactic isnxo a shorthand for `exact sorry`. -/
macro "sorry" : tactic => `(exact sorry)
macro "infer_instance" : tactic => `(exact inferInstance)

/-- Optional configuration option for tactics -/
syntax config := atomic("(" &"config") " := " term ")"

syntax locationWildcard := "*"
syntax locationHyp      := (colGt ident)+ ("⊢" <|> "|-")? -- TODO: delete
syntax locationTargets  := (colGt ident)+ ("⊢" <|> "|-")?
syntax location         := withPosition(" at " (locationWildcard <|> locationHyp))

syntax (name := change) "change " term (location)? : tactic
syntax (name := changeWith) "change " term " with " term (location)? : tactic

syntax rwRule    := ("←" <|> "<-")? term
syntax rwRuleSeq := "[" rwRule,+,? "]"

syntax (name := rewriteSeq) "rewrite " (config)? rwRuleSeq (location)? : tactic

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

syntax (name := injection) "injection " term (" with " (colGt (ident <|> "_"))+)? : tactic

syntax (name := injections) "injections" : tactic

syntax discharger := atomic("(" (&"discharger" <|> &"disch")) " := " tacticSeq ")"

syntax simpPre   := "↓"
syntax simpPost  := "↑"
syntax simpLemma := (simpPre <|> simpPost)? ("←" <|> "<-")? term
syntax simpErase := "-" ident
syntax simpStar  := "*"
syntax (name := simp) "simp " (config)? (discharger)? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic
syntax (name := simpAll) "simp_all " (config)? (discharger)? (&"only ")? ("[" (simpErase <|> simpLemma),* "]")? : tactic

/--
  Delta expand the given definition.
  This is a low-level tactic, it will expose how recursive definitions have been compiled by Lean. -/
syntax (name := delta) "delta " ident (location)? : tactic

-- Auxiliary macro for lifting have/suffices/let/...
-- It makes sure the "continuation" `?_` is the main goal after refining
macro "refine_lift " e:term : tactic => `(focus (refine noImplicitLambda% $e; rotate_right))

macro "have " d:haveDecl : tactic => `(refine_lift have $d:haveDecl; ?_)
/- We use a priority > default, to avoid ambiguity with previous `have` notation -/
macro (priority := high) "have" x:ident " := " p:term : tactic => `(have $x:ident : _ := $p)
macro "suffices " d:sufficesDecl : tactic => `(refine_lift suffices $d:sufficesDecl; ?_)
macro "let " d:letDecl : tactic => `(refine_lift let $d:letDecl; ?_)
macro "show " e:term : tactic => `(refine_lift show $e:term from ?_)
syntax (name := letrec) withPosition(atomic(group("let " &"rec ")) letRecDecls) : tactic
macro_rules
  | `(tactic| let rec $d:letRecDecls) => `(tactic| refine_lift let rec $d:letRecDecls; ?_)

-- Similar to `refineLift`, but using `refine'`
macro "refine_lift' " e:term : tactic => `(focus (refine' noImplicitLambda% $e; rotate_right))
macro "have' " d:haveDecl : tactic => `(refine_lift' have $d:haveDecl; ?_)
macro (priority := high) "have'" x:ident " := " p:term : tactic => `(have' $x:ident : _ := $p)
macro "let' " d:letDecl : tactic => `(refine_lift' let $d:letDecl; ?_)

syntax inductionAlt  := "| " (group("@"? ident) <|> "_") (ident <|> "_")* " => " (hole <|> syntheticHole <|> tacticSeq)
syntax inductionAlts := "with " (tactic)? withPosition( (colGe inductionAlt)+)
syntax (name := induction) "induction " term,+ (" using " ident)?  ("generalizing " ident+)? (inductionAlts)? : tactic

syntax generalizeArg := atomic(ident " : ")? term:51 " = " ident
/--
`generalize ([h :] e = x),+` replaces all occurrences `e`s in the main goal with a fresh hypothesis `x`s.
If `h` is given, `h : e = x` is introduced as well. -/
syntax (name := generalize) "generalize " generalizeArg,+ : tactic

syntax casesTarget := atomic(ident " : ")? term
syntax (name := cases) "cases " casesTarget,+ (" using " ident)? (inductionAlts)? : tactic

syntax (name := existsIntro) "exists " term : tactic

/-- `rename_i x_1 ... x_n` renames the last `n` inaccessible names using the given names. -/
syntax (name := renameI) "rename_i " (colGt (ident <|> "_"))+ : tactic

syntax "repeat " tacticSeq : tactic
macro_rules
  | `(tactic| repeat $seq) => `(tactic| first | ($seq); repeat $seq | skip)

syntax "trivial" : tactic

syntax (name := split) "split " (colGt term)? (location)? : tactic

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
macro_rules | `(tactic| trivial) => `(tactic| apply True.intro)
macro_rules | `(tactic| trivial) => `(tactic| apply And.intro <;> trivial)

macro "unhygienic " t:tacticSeq : tactic => `(set_option tactic.hygienic false in $t:tacticSeq)

end Tactic

namespace Attr
-- simp attribute syntax
syntax (name := simp) "simp" (Tactic.simpPre <|> Tactic.simpPost)? (prio)? : attr
end Attr

end Parser
end Lean

macro "‹" type:term "›" : term => `((by assumption : $type))
