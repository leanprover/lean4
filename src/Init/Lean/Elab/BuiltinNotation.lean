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

@[builtinMacro Lean.Parser.Term.dollar] def expandDollar : Macro :=
fun stx => match_syntax stx with
| `($f $args* $ $a) => let args := args.push a; `($f $args*)
| `($f $ $a)        => `($f $a)
| _                 => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.dollarProj] def expandDollarProj : Macro :=
fun stx => match_syntax stx with
| `($term $.$field) => `($(term).$field)
| _                 => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.if] def expandIf : Macro :=
fun stx => match_syntax stx with
| `(if $h : $cond then $t else $e) => `(dite $cond (fun $h:ident => $t) (fun $h:ident => $e))
| `(if $cond then $t else $e)      => `(ite $cond $t $e)
| _                                => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.subtype] def expandSubtype : Macro :=
fun stx => match_syntax stx with
| `({ $x : $type // $p }) => `(Subtype (fun ($x:ident : $type) => $p))
| `({ $x // $p })         => `(Subtype (fun ($x:ident : _) => $p))
| _                       => Macro.throwUnsupported

@[builtinTermElab anonymousCtor] def elabAnonymousCtor : TermElab :=
fun stx expectedType? => match_syntax stx with
| `(⟨$args*⟩) => do
  let ref := stx;
  tryPostponeIfNoneOrMVar expectedType?;
  match expectedType? with
  | some expectedType => do
    expectedType ← instantiateMVars ref expectedType;
    let expectedType := expectedType.consumeMData;
    match expectedType.getAppFn with
    | Expr.const constName _ _ => do
      env ← getEnv;
      match env.find? constName with
      | some (ConstantInfo.inductInfo val) =>
        match val.ctors with
        | [ctor] => do
          stx ← `($(mkCTermIdFrom ref ctor) $(args.getSepElems)*);
          withMacroExpansion ref stx $ elabTerm stx expectedType?
        | _ => throwError ref ("invalid constructor ⟨...⟩, '" ++ constName ++ "' must have only one constructor")
      | _ => throwError ref ("invalid constructor ⟨...⟩, '" ++ constName ++ "' is not an inductive type")
    | _ => throwError ref ("invalid constructor ⟨...⟩, expected type is not an inductive type " ++ indentExpr expectedType)
  | none => throwError ref "invalid constructor ⟨...⟩, expected type must be known"
| _ => throwUnsupportedSyntax

@[builtinMacro Lean.Parser.Term.show] def expandShow : Macro :=
fun stx => match_syntax stx with
| `(show $type from $val) => let thisId := mkTermIdFrom stx `this; `((fun ($thisId : $type) => $thisId) $val)
| _                       => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.have] def expandHave : Macro :=
fun stx => match_syntax stx with
| `(have $type from $val; $body)      => let thisId := mkTermIdFrom stx `this; `((fun ($thisId : $type) => $body) $val)
| `(have $type := $val; $body)        => let thisId := mkTermIdFrom stx `this; `((fun ($thisId : $type) => $body) $val)
| `(have $x : $type from $val; $body) => `((fun ($x:ident : $type) => $body) $val)
| `(have $x : $type := $val; $body)   => `((fun ($x:ident : $type) => $body) $val)
| _                                   => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.where] def expandWhere : Macro :=
fun stx => match_syntax stx with
| `($body where $decls:letDecl*) =>  do
  let decls := decls.getEvenElems;
  decls.foldrM
    (fun decl body => `(let $decl:letDecl; $body))
    body
| _                      => Macro.throwUnsupported

@[builtinTermElab «parser!»] def elabParserMacro : TermElab :=
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

@[builtinTermElab «tparser!»] def elabTParserMacro : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `(tparser! $e) => do
  declName? ← getDeclName?;
  match declName? with
  | some declName => let kind := quote declName; `(Lean.Parser.trailingNode $kind $e)
  | none          => throwError stx "invalid `tparser!` macro, it must be used in definitions"
| _             => throwUnsupportedSyntax

def elabInfix (f : Syntax) : Macro :=
fun stx => do
  -- term `op` term
  let a := stx.getArg 0;
  let b := stx.getArg 2;
  pure (mkAppStx f #[a, b])

def elabInfixOp (op : Name) : Macro :=
fun stx => elabInfix (mkCTermIdFrom (stx.getArg 1) op) stx

@[builtinMacro Lean.Parser.Term.prod] def elabProd : Macro := elabInfixOp `Prod
@[builtinMacro Lean.Parser.Term.fcomp] def ElabFComp : Macro := elabInfixOp `Function.comp

@[builtinMacro Lean.Parser.Term.add] def elabAdd : Macro := elabInfixOp `HasAdd.add
@[builtinMacro Lean.Parser.Term.sub] def elabSub : Macro := elabInfixOp `HasSub.sub
@[builtinMacro Lean.Parser.Term.mul] def elabMul : Macro := elabInfixOp `HasMul.mul
@[builtinMacro Lean.Parser.Term.div] def elabDiv : Macro := elabInfixOp `HasDiv.div
@[builtinMacro Lean.Parser.Term.mod] def elabMod : Macro := elabInfixOp `HasMod.mod
@[builtinMacro Lean.Parser.Term.modN] def elabModN : Macro := elabInfixOp `HasModN.modn
@[builtinMacro Lean.Parser.Term.pow] def elabPow : Macro := elabInfixOp `HasPow.pow

@[builtinMacro Lean.Parser.Term.le] def elabLE : Macro := elabInfixOp `HasLessEq.LessEq
@[builtinMacro Lean.Parser.Term.ge] def elabGE : Macro := elabInfixOp `GreaterEq
@[builtinMacro Lean.Parser.Term.lt] def elabLT : Macro := elabInfixOp `HasLess.Less
@[builtinMacro Lean.Parser.Term.gt] def elabGT : Macro := elabInfixOp `Greater
@[builtinMacro Lean.Parser.Term.eq] def elabEq : Macro := elabInfixOp `Eq
@[builtinMacro Lean.Parser.Term.ne] def elabNe : Macro := elabInfixOp `Ne
@[builtinMacro Lean.Parser.Term.beq] def elabBEq : Macro := elabInfixOp `HasBeq.beq
@[builtinMacro Lean.Parser.Term.bne] def elabBNe : Macro := elabInfixOp `bne
@[builtinMacro Lean.Parser.Term.heq] def elabHEq : Macro := elabInfixOp `HEq
@[builtinMacro Lean.Parser.Term.equiv] def elabEquiv : Macro := elabInfixOp `HasEquiv.Equiv

@[builtinMacro Lean.Parser.Term.and] def elabAnd : Macro := elabInfixOp `And
@[builtinMacro Lean.Parser.Term.or] def elabOr : Macro := elabInfixOp `Or
@[builtinMacro Lean.Parser.Term.iff] def elabIff : Macro := elabInfixOp `Iff

@[builtinMacro Lean.Parser.Term.band] def elabBAnd : Macro := elabInfixOp `and
@[builtinMacro Lean.Parser.Term.bor] def elabBOr : Macro := elabInfixOp `or

@[builtinMacro Lean.Parser.Term.append] def elabAppend : Macro := elabInfixOp `HasAppend.append
@[builtinMacro Lean.Parser.Term.cons] def elabCons : Macro := elabInfixOp `List.cons

@[builtinMacro Lean.Parser.Term.andthen] def elabAndThen : Macro := elabInfixOp `HasAndthen.andthen
@[builtinMacro Lean.Parser.Term.bindOp] def elabBind : Macro := elabInfixOp `HasBind.bind

@[builtinMacro Lean.Parser.Term.seq] def elabseq : Macro := elabInfixOp `HasSeq.seq
@[builtinMacro Lean.Parser.Term.seqLeft] def elabseqLeft : Macro := elabInfixOp `HasSeqLeft.seqLeft
@[builtinMacro Lean.Parser.Term.seqRight] def elabseqRight : Macro := elabInfixOp `HasSeqRight.seqRight

@[builtinMacro Lean.Parser.Term.map] def elabMap : Macro := elabInfixOp `Functor.map
@[builtinMacro Lean.Parser.Term.mapRev] def elabMapRev : Macro := elabInfixOp `Functor.mapRev
@[builtinMacro Lean.Parser.Term.mapConst] def elabMapConst : Macro := elabInfixOp `Functor.mapConst
@[builtinMacro Lean.Parser.Term.mapConstRev] def elabMapConstRev : Macro := elabInfixOp `Functor.mapConstRev

@[builtinMacro Lean.Parser.Term.orelse] def elabOrElse : Macro := elabInfixOp `HasOrelse.orelse
@[builtinMacro Lean.Parser.Term.orM] def elabOrM : Macro := elabInfixOp `orM
@[builtinMacro Lean.Parser.Term.andM] def elabAndM : Macro := elabInfixOp `andM

/-
TODO
@[builtinTermElab] def elabsubst : TermElab := elabInfixOp infixR " ▸ " 75
-/

end Term
end Elab
end Lean
