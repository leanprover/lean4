/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Term
import Init.Lean.Elab.Quotation

namespace Lean
namespace Elab
namespace Term

@[builtinTermElab «do»] def elabDo : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
-- TODO: implement more than the bare minimum necessary for the paper example
| `(do $x:ident ← $e:term; $f:term) => `(HasBind.bind $e (fun $x:ident => $f:term))
| _                                 => throwUnsupportedSyntax

@[builtinTermElab dollar] def elabDollar : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `($f $args* $ $a) => let args := args.push a; `($f $args*)
| `($f $ $a)        => `($f $a)
| _                 => throwUnsupportedSyntax

@[builtinTermElab dollarProj] def elabDollarProj : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `($term $.$field) => `($(term).$field)
| _                 => throwUnsupportedSyntax

@[builtinTermElab «if»] def elabIf : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `(if $h : $cond then $t else $e) => `(dite $cond (fun $h:ident => $t) (fun $h:ident => $e))
| `(if $cond then $t else $e)      => `(ite $cond $t $e)
| _                                => throwUnsupportedSyntax

@[builtinTermElab subtype] def elabSubtype : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `({ $x : $type // $p }) => `(Subtype (fun ($x:ident : $type) => $p))
| `({ $x // $p })         => `(Subtype (fun ($x:ident : _) => $p))
| _                       => throwUnsupportedSyntax

@[builtinTermElab anonymousCtor] def elabAnoymousCtor : TermElab :=
fun stx expectedType? => do
let ref := stx;
tryPostponeIfNoneOrMVar expectedType?;
match expectedType? with
| none              => throwError ref "invalid constructor ⟨...⟩, expected type must be known"
| some expectedType => do
  expectedType ← instantiateMVars ref expectedType;
  let expectedType := expectedType.consumeMData;
  match expectedType.getAppFn with
  | Expr.const constName _ _ => do
    env ← getEnv;
    match env.find? constName with
    | some (ConstantInfo.inductInfo val) =>
      if val.ctors.length != 1 then
        throwError ref ("invalid constructor ⟨...⟩, '" ++ constName ++ "' must have only one constructor")
      else
        let ctor   := mkCTermIdFrom ref val.ctors.head!;
        let args   := (stx.getArg 1).getArgs.getEvenElems; do
        let newStx := mkAppStx ctor args;
        withMacroExpansion ref newStx $ elabTerm newStx expectedType?
    | _ => throwError ref ("invalid constructor ⟨...⟩, '" ++ constName ++ "' is not an inductive type")
  | _ => throwError ref ("invalid constructor ⟨...⟩, expected type is not an inductive type " ++ indentExpr expectedType)

@[builtinTermElab «show»] def elabShow : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `(show $type from $val) => let thisId := mkTermIdFrom stx `this; `((fun ($thisId : $type) => $thisId) $val)
| _                       => throwUnsupportedSyntax

@[builtinTermElab «have»] def elabHave : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `(have $type from $val; $body)      => let thisId := mkTermIdFrom stx `this; `((fun ($thisId : $type) => $body) $val)
| `(have $type := $val; $body)        => let thisId := mkTermIdFrom stx `this; `((fun ($thisId : $type) => $body) $val)
| `(have $x : $type from $val; $body) => `((fun ($x:ident : $type) => $body) $val)
| `(have $x : $type := $val; $body)   => `((fun ($x:ident : $type) => $body) $val)
| _                                   => throwUnsupportedSyntax

@[termElab «where»] def elabWhere : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `($body where $decls*) =>  do
  let decls := decls.getEvenElems;
  decls.foldrM
    (fun decl body => `(let $decl; $body))
    body
| _                      => throwUnsupportedSyntax

@[termElab «parser!»] def elabParserMacro : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `(parser! $e) => do
  some declName ← getDeclName?
    | throwError stx "invalid `parser!` macro, it must be used in definitions";
  match extractMacroScopes declName with
  | { name := Name.str _ s _, scopes :=  scps, .. } => do
    let kind := quote declName;
    let s    := quote s;
    p ← `(Lean.Parser.leadingNode $kind $e);
    if scps == [] then
      -- TODO simplify the following quotation as soon as we have coercions
      `(HasOrelse.orelse (Lean.Parser.mkAntiquot $s (some $kind)) $p)
    else
      -- if the parser decl is hidden by hygiene, it doesn't make sense to provide an antiquotation kind
      `(HasOrelse.orelse (Lean.Parser.mkAntiquot $s none) $p)
  | _             => throwError stx "invalid `parser!` macro, unexpected declaration name"
| _             => throwUnsupportedSyntax

@[termElab «tparser!»] def elabTParserMacro : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `(tparser! $e) => do
  declName? ← getDeclName?;
  match declName? with
  | some declName => let kind := quote declName; `(Lean.Parser.trailingNode $kind $e)
  | none          => throwError stx "invalid `tparser!` macro, it must be used in definitions"
| _             => throwUnsupportedSyntax

def elabInfix (f : Syntax) : TermElab :=
fun stx expectedType? => do
  -- term `op` term
  let a := stx.getArg 0;
  let b := stx.getArg 2;
  elabTerm (mkAppStx f #[a, b]) expectedType?

def elabInfixOp (op : Name) : TermElab :=
fun stx expectedType? => elabInfix (mkCTermIdFrom (stx.getArg 1) op) stx expectedType?

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
