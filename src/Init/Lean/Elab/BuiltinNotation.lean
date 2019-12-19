/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Term

namespace Lean
namespace Elab
namespace Term

@[builtinTermElab dollar] def elabDollar : TermElab :=
fun stx expectedType? => do
  -- term `$` term
  let f := stx.getArg 0;
  let a := stx.getArg 2;
  elabTerm (mkAppStx f #[a]) expectedType?

def mkProjStx (t : Syntax) (i : Syntax) : Syntax :=
Syntax.node `Lean.Parser.Term.proj #[t, mkAtom("."), i]

@[builtinTermElab dollarProj] def elabDollarProj : TermElab :=
fun stx expectedType? => do
  -- term `$.` field
  let f := stx.getArg 0;
  let i := stx.getArg 2;
  elabTerm (mkProjStx f i) expectedType?

def elabInfix (f : Syntax) : TermElab :=
fun stx expectedType? => do
  -- term `op` term
  let a := stx.getArg 0;
  let b := stx.getArg 2;
  elabTerm (mkAppStx f #[a, b]) expectedType?

def elabInfixOp (op : Name) : TermElab :=
fun stx expectedType? => elabInfix (mkTermId (stx.getArg 1) op) stx expectedType?

@[builtinTermElab prod] def elabProd : TermElab := elabInfixOp `Prod
@[builtinTermElab fcomp] def ElabFComp : TermElab := elabInfixOp `Function.comp

@[builtinTermElab add] def elabAdd : TermElab := elabInfixOp `HasAdd.add
@[builtinTermElab sub] def elabSub : TermElab := elabInfixOp `HasSub.sub
@[builtinTermElab mul] def elabMul : TermElab := elabInfixOp `HasMul.mul
@[builtinTermElab div] def elabDiv : TermElab := elabInfixOp `HasDiv.div
@[builtinTermElab mod] def elabMod : TermElab := elabInfixOp `HasMod.mod
@[builtinTermElab modN] def elabModN : TermElab := elabInfixOp `HasModN.modn
@[builtinTermElab pow] def elabPow : TermElab := elabInfixOp `HasPow.pow

@[builtinTermElab le] def elabLE : TermElab := elabInfixOp `HasLessEq.LessEq
@[builtinTermElab ge] def elabGE : TermElab := elabInfixOp `GreaterEq
@[builtinTermElab lt] def elabLT : TermElab := elabInfixOp `HasLess.Less
@[builtinTermElab gt] def elabGT : TermElab := elabInfixOp `Greater
@[builtinTermElab eq] def elabEq : TermElab := elabInfixOp `Eq
@[builtinTermElab ne] def elabNe : TermElab := elabInfixOp `Ne
@[builtinTermElab beq] def elabBEq : TermElab := elabInfixOp `HasBeq.beq
@[builtinTermElab bne] def elabBNe : TermElab := elabInfixOp `bne
@[builtinTermElab heq] def elabHEq : TermElab := elabInfixOp `HEq
@[builtinTermElab equiv] def elabEquiv : TermElab := elabInfixOp `HasEquiv.Equiv

@[builtinTermElab and] def elabAnd : TermElab := elabInfixOp `And
@[builtinTermElab or] def elabOr : TermElab := elabInfixOp `Or
@[builtinTermElab iff] def elabIff : TermElab := elabInfixOp `Iff

@[builtinTermElab band] def elabBAnd : TermElab := elabInfixOp `and
@[builtinTermElab bor] def elabBOr : TermElab := elabInfixOp `or

@[builtinTermElab append] def elabAppend : TermElab := elabInfixOp `HasAppend.append
@[builtinTermElab cons] def elabCons : TermElab := elabInfixOp `List.cons

@[builtinTermElab andthen] def elabAndThen : TermElab := elabInfixOp `HasAndthen.andthen
@[builtinTermElab bindOp] def elabBind : TermElab := elabInfixOp `HasBind.bind

@[builtinTermElab seq] def elabseq : TermElab := elabInfixOp `HasSeq.seq
@[builtinTermElab seqLeft] def elabseqLeft : TermElab := elabInfixOp `HasSeqLeft.seqLeft
@[builtinTermElab seqRight] def elabseqRight : TermElab := elabInfixOp `HasSeqRight.seqRight

@[builtinTermElab map] def elabMap : TermElab := elabInfixOp `Functor.map
@[builtinTermElab mapRev] def elabMapRev : TermElab := elabInfixOp `Functor.mapRev
@[builtinTermElab mapConst] def elabMapConst : TermElab := elabInfixOp `Functor.mapConst
@[builtinTermElab mapConstRev] def elabMapConstRev : TermElab := elabInfixOp `Functor.mapConstRev

@[builtinTermElab orelse] def elabOrElse : TermElab := elabInfixOp `HasOrelse.orelse
@[builtinTermElab orM] def elabOrM : TermElab := elabInfixOp `orM
@[builtinTermElab andM] def elabAndM : TermElab := elabInfixOp `andM

/-
TODO
@[builtinTermElab] def elabsubst : TermElab := elabInfixOp infixR " ▸ " 75
-/

end Term
end Elab
end Lean
