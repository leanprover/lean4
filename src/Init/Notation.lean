/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Notation for operators defined at Prelude.lean
-/
prelude
import Init.Prelude
import Init.Coe

-- DSL for specifying parser precedences and priorities

namespace Lean.Parser.Syntax

syntax:65 (name := addPrec) prec " + " prec:66 : prec
syntax:65 (name := subPrec) prec " - " prec:66 : prec

syntax:65 (name := addPrio) prio " + " prio:66 : prio
syntax:65 (name := subPrio) prio " - " prio:66 : prio

end Lean.Parser.Syntax

namespace Lean

instance : CoeHead (TSyntax ks) Syntax where
  coe stx := stx.raw

instance : Coe SyntaxNodeKind SyntaxNodeKinds where
  coe k := List.cons k List.nil

end Lean

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
  | `(if $h : $c then $t else $e) => `(let_mvar% ?m := $c; wait_if_type_mvar% ?m; dite ?m (fun $h:ident => $t) (fun $h:ident => $e))

syntax (name := termIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("if " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(if $c then $t else $e) => `(let_mvar% ?m := $c; wait_if_type_mvar% ?m; ite ?m $t $e)

macro "if " "let " pat:term " := " d:term " then " t:term " else " e:term : term =>
  `(match $d:term with | $pat => $t | _ => $e)

syntax (name := boolIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("bif " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(bif $c then $t else $e) => `(cond $c $t $e)

syntax:min term " <| " term:min : term

macro_rules
  | `($f $args* <| $a) => `($f $args* $a)
  | `($f <| $a) => `($f $a)

syntax:min term " |> " term:min1 : term

macro_rules
  | `($a |> $f $args*) => `($f $args* $a)
  | `($a |> $f)        => `($f $a)

-- Haskell-like pipe <|
-- Note that we have a whitespace after `$` to avoid an ambiguity with the antiquotations.
syntax:min term atomic(" $" ws) term:min : term

macro_rules
  | `($f $args* $ $a) => `($f $args* $a)
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
    -- NOTE: we do not have `TSepArray.getElems` yet at this point
    let rec expandListLit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← ``(List.cons $(⟨elems.elemsAndSeps[i]!⟩) $result))
    if elems.elemsAndSeps.size < 64 then
      expandListLit elems.elemsAndSeps.size false (← ``(List.nil))
    else
      `(%[ $elems,* | List.nil ])

-- Declare `this` as a keyword that unhygienically binds to a scope-less `this` assumption (or other binding).
-- The keyword prevents declaring a `this` binding except through metapgrogramming, as is done by `have`/`show`.
/-- Special identifier introduced by "anonymous" `have : ...`, `suffices p ...` etc. -/
macro tk:"this" : term => return Syntax.ident tk.getHeadInfo "this".toSubstring `this []

/-
  Category for carrying raw syntax trees between macros; any content is printed as is by the pretty printer.
  The only accepted parser for this category is an antiquotation. -/
declare_syntax_cat rawStx

instance : Coe Syntax (TSyntax `rawStx) where
  coe stx := ⟨stx⟩
