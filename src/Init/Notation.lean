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

macro "max"  : prec => `(1024) -- maximum precedence used in term parsers
macro "lead" : prec => `(1023)
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
syntax   stx "+" : stx
syntax   stx "*" : stx
syntax   stx "?" : stx
syntax:2 stx " <|> " stx:1 : stx

macro_rules
  | `(stx| $p +) => `(stx| many1($p))
  | `(stx| $p *) => `(stx| many($p))
  | `(stx| $p ?) => `(stx| optional($p))
  | `(stx| $p₁ <|> $p₂) => `(stx| orelse($p₁, $p₂))

/- Comma-separated sequence. -/
macro:max x:stx ",*"   : stx => `(stx| sepBy($x, ",", ", "))
macro:max x:stx ",+"   : stx => `(stx| sepBy1($x, ",", ", "))
/- Comma-separated sequence with optional trailing comma. -/
macro:max x:stx ",*,?" : stx => `(stx| sepBy($x, ",", ", ", allowTrailingSep))
macro:max x:stx ",+,?" : stx => `(stx| sepBy1($x, ",", ", ", allowTrailingSep))

macro "!" x:stx : stx => `(stx| notFollowedBy($x))

syntax (name := rawNatLit) "nat_lit " num : term

infixr:90 " ∘ "  => Function.comp
infixr:35 " × "  => Prod

infixl:55 " ||| "  => HOr.hOr
infixl:58 " ^^^ "  => HXor.hXor
infixl:60 " &&& "  => HAnd.hAnd
infixl:65 " + "  => HAdd.hAdd
infixl:65 " - "  => HSub.hSub
infixl:70 " * "  => HMul.hMul
infixl:70 " / "  => HDiv.hDiv
infixl:70 " % "  => HMod.hMod
infixl:75 " <<< "  => HShiftLeft.hShiftLeft
infixl:75 " >>> "  => HShiftRight.hShiftRight
infixr:80 " ^ "  => HPow.hPow
prefix:100 "-"   => Neg.neg
prefix:100 "~~~"   => Complement.complement

-- declare ASCII alternatives first so that the latter Unicode unexpander wins
infix:50 " <= " => HasLessEq.LessEq
infix:50 " ≤ "  => HasLessEq.LessEq
infix:50 " < "  => HasLess.Less
infix:50 " >= " => GreaterEq
infix:50 " ≥ "  => GreaterEq
infix:50 " > "  => Greater
infix:50 " = "  => Eq
infix:50 " == " => BEq.beq
infix:50 " ~= " => HEq
infix:50 " ≅ "  => HEq
/-
  Remark: the infix commands above ensure a delaborator is generated for each relations.
  We redefine the macros below to be able to use the auxiliary `binrel%` elaboration helper for binary relations.
  It has better support for applying coercions. For example, suppose we have `binrel% Eq n i` where `n : Nat` and
  `i : Int`. The default elaborator fails because we don't have a coercion from `Int` to `Nat`, but
  `binrel%` succeeds because it also tries a coercion from `Nat` to `Int` even when the nat occurs before the int. -/
macro_rules | `($x <= $y) => `(binrel% HasLessEq.LessEq $x $y)
macro_rules | `($x ≤ $y)  => `(binrel% HasLessEq.LessEq $x $y)
macro_rules | `($x < $y)  => `(binrel% HasLess.Less $x $y)
macro_rules | `($x > $y)  => `(binrel% Greater $x $y)
macro_rules | `($x >= $y) => `(binrel% GreaterEq $x $y)
macro_rules | `($x ≥ $y)  => `(binrel% GreaterEq $x $y)
macro_rules | `($x = $y)  => `(binrel% Eq $x $y)
macro_rules | `($x == $y) => `(binrel% BEq.beq $x $y)

infixr:35 " /\\ " => And
infixr:35 " ∧ "   => And
infixr:30 " \\/ " => Or
infixr:30 " ∨   " => Or
notation:max "¬" p:40 => Not p

infixl:35 " && " => and
infixl:30 " || " => or
notation:max "!" b:40 => not b

infixl:65 " ++ " => HAppend.hAppend
infixr:67 " :: " => List.cons

infixr:20  " <|> " => HOrElse.hOrElse
infixr:60  " >> "  => HAndThen.hAndThen
infixl:55  " >>= " => Bind.bind
infixl:60  " <*> " => Seq.seq
infixl:60  " <* "  => SeqLeft.seqLeft
infixr:60  " *> "  => SeqRight.seqRight
infixr:100 " <$> " => Functor.map

syntax (name := termDepIfThenElse) ppGroup(ppDedent("if " ident " : " term " then" ppSpace term ppDedent(ppSpace "else") ppSpace term)) : term

macro_rules
  | `(if $h:ident : $c then $t:term else $e:term) => `(dite $c (fun $h:ident => $t) (fun $h:ident => $e))

syntax (name := termIfThenElse) ppGroup(ppDedent("if " term " then" ppSpace term ppDedent(ppSpace "else") ppSpace term)) : term

macro_rules
  | `(if $c then $t:term else $e:term) => `(ite $c $t $e)

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
  | `({ $x : $type // $p }) => `(Subtype (fun ($x:ident : $type) => $p))
  | `({ $x // $p })         => `(Subtype (fun ($x:ident : _) => $p))

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
      | i+1, false => expandListLit i true  (← `(List.cons $(elems.elemsAndSeps[i]) $result))
    if elems.elemsAndSeps.size < 64 then
      expandListLit elems.elemsAndSeps.size false (← `(List.nil))
    else
      `(%[ $elems,* | List.nil ])

namespace Parser.Tactic
syntax (name := intro) "intro " notFollowedBy("|") (colGt term:max)* : tactic
syntax (name := intros) "intros " (colGt (ident <|> "_"))* : tactic
syntax (name := rename) "rename " term " => " ident : tactic
syntax (name := revert) "revert " (colGt ident)+ : tactic
syntax (name := clear) "clear " (colGt ident)+ : tactic
syntax (name := subst) "subst " (colGt ident)+ : tactic
syntax (name := assumption) "assumption" : tactic
syntax (name := contradiction) "contradiction" : tactic
syntax (name := apply) "apply " term : tactic
syntax (name := exact) "exact " term : tactic
syntax (name := refine) "refine " term : tactic
syntax (name := refine') "refine' " term : tactic
syntax (name := case) "case " ident " => " tacticSeq : tactic
syntax (name := allGoals) "allGoals " tacticSeq : tactic
syntax (name := focus) "focus " tacticSeq : tactic
syntax (name := skip) "skip" : tactic
syntax (name := done) "done" : tactic
syntax (name := traceState) "traceState" : tactic
syntax (name := failIfSuccess) "failIfSuccess " tacticSeq : tactic
syntax (name := generalize) "generalize " atomic(ident " : ")? term:51 " = " ident : tactic
syntax (name := paren) "(" tacticSeq ")" : tactic
syntax (name := withReducible) "withReducible " tacticSeq : tactic
syntax (name := withReducibleAndInstances) "withReducibleAndInstances " tacticSeq : tactic
syntax (name := first) "first " "|"? sepBy1(tacticSeq, "|") : tactic
syntax (name := rotateLeft) "rotateLeft" (num)? : tactic
syntax (name := rotateRight) "rotateRight" (num)? : tactic
macro "try " t:tacticSeq : tactic => `(first $t | skip)
macro:1 x:tactic " <;> " y:tactic:0 : tactic => `(tactic| focus ($x:tactic; allGoals $y:tactic))

macro "rfl" : tactic => `(exact rfl)
macro "admit" : tactic => `(exact sorry)
macro "inferInstance" : tactic => `(exact inferInstance)

syntax locationWildcard := "*"
syntax locationHyp      := (colGt ident)+ ("⊢" <|> "|-")? -- TODO: delete
syntax locationTargets  := (colGt ident)+ ("⊢" <|> "|-")?
syntax location         := withPosition("at " locationWildcard <|> locationHyp)

syntax (name := change) "change " term (location)? : tactic
syntax (name := changeWith) "change " term " with " term (location)? : tactic

syntax rwRule    := ("←" <|> "<-")? term
syntax rwRuleSeq := "[" rwRule,+,? "]"

syntax (name := rewrite) "rewrite " rwRule (location)? : tactic
syntax (name := rewriteSeq) (priority := high) "rewrite " rwRuleSeq (location)? : tactic
syntax (name := erewrite) "erewrite " rwRule (location)? : tactic
syntax (name := erewriteSeq) (priority := high) "erewrite " rwRuleSeq (location)? : tactic

syntax (name := rw) "rw " rwRule (location)? : tactic
syntax (name := rwSeq) (priority := high) "rw " rwRuleSeq (location)? : tactic
syntax (name := erw) "erw " rwRule (location)? : tactic
syntax (name := erwSeq) (priority := high) "erw " rwRuleSeq (location)? : tactic

private def withCheapRefl (tac : Syntax) : MacroM Syntax :=
  `(tactic| $tac; try (withReducible rfl))

@[macro rw]
def expandRw : Macro :=
  fun stx => withCheapRefl (stx.setKind `Lean.Parser.Tactic.rewrite |>.setArg 0 (mkAtomFrom stx "rewrite"))

@[macro rwSeq]
def expandRwSeq : Macro :=
  fun stx => withCheapRefl (stx.setKind `Lean.Parser.Tactic.rewriteSeq |>.setArg 0 (mkAtomFrom stx "rewrite"))

@[macro erw]
def expandERw : Macro :=
  fun stx => withCheapRefl (stx.setKind `Lean.Parser.Tactic.erewrite |>.setArg 0 (mkAtomFrom stx "erewrite"))

@[macro erwSeq]
def expandERwSeq : Macro :=
  fun stx => withCheapRefl (stx.setKind `Lean.Parser.Tactic.erewriteSeq |>.setArg 0 (mkAtomFrom stx "erewrite"))

syntax (name := injection) "injection " term (" with " (colGt (ident <|> "_"))+)? : tactic

syntax simpPre   := "↓"
syntax simpPost  := "↑"
syntax simpLemma := (simpPre <|> simpPost)? term
syntax simpErase := "-" ident
syntax (name := simp) "simp " ("(" &"config" " := " term ")")? (&"only ")? ("[" (simpErase <|> simpLemma),* "]")? (location)? : tactic

-- Auxiliary macro for lifting have/suffices/let/...
-- It makes sure the "continuation" `?_` is the main goal after refining
macro "refineLift " e:term : tactic => `(focus (refine $e; rotateRight))

macro "have " d:haveDecl : tactic => `(refineLift have $d:haveDecl; ?_)
/- We use a priority > default, to avoid ambiguity with previous `have` notation -/
macro (priority := high) "have" x:ident " := " p:term : tactic => `(have $x:ident : _ := $p)
macro "suffices " d:sufficesDecl : tactic => `(refineLift suffices $d:sufficesDecl; ?_)
macro "let " d:letDecl : tactic => `(refineLift let $d:letDecl; ?_)
macro "show " e:term : tactic => `(refineLift show $e:term from ?_)
syntax (name := letrec) withPosition(atomic(group("let " &"rec ")) letRecDecls) : tactic
macro_rules
  | `(tactic| let rec $d:letRecDecls) => `(tactic| refineLift let rec $d:letRecDecls; ?_)

-- Similar to `refineLift`, but using `refine'`
macro "refineLift' " e:term : tactic => `(focus (refine' $e; rotateRight))
macro "have' " d:haveDecl : tactic => `(refineLift' have $d:haveDecl; ?_)
macro (priority := high) "have'" x:ident " := " p:term : tactic => `(have' $x:ident : _ := $p)
macro "let' " d:letDecl : tactic => `(refineLift' let $d:letDecl; ?_)

syntax inductionAlt  := "| " (group("@"? ident) <|> "_") (ident <|> "_")* " => " (hole <|> syntheticHole <|> tacticSeq)
syntax inductionAlts := "with " (tactic)? withPosition( (colGe inductionAlt)+)
syntax (name := induction) "induction " term,+ (" using " ident)?  ("generalizing " ident+)? (inductionAlts)? : tactic
syntax casesTarget := atomic(ident " : ")? term
syntax (name := cases) "cases " casesTarget,+ (" using " ident)? (inductionAlts)? : tactic

syntax (name := existsIntro) "exists " term : tactic


syntax "repeat " tacticSeq : tactic
macro_rules
  | `(tactic| repeat $seq) => `(tactic| first ($seq); repeat $seq | skip)

end Tactic

namespace Attr
-- simp attribute syntax
syntax (name := simp) "simp" (Tactic.simpPre <|> Tactic.simpPost)? (prio)? : attr
end Attr

end Parser
end Lean

macro "‹" type:term "›" : term => `((by assumption : $type))
