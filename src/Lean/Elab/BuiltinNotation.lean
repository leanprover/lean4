/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Term
import Lean.Elab.Quotation
import Lean.Elab.SyntheticMVars

namespace Lean
namespace Elab
namespace Term

open Meta

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
  tryPostponeIfNoneOrMVar expectedType?;
  match expectedType? with
  | some expectedType => do
    expectedType ← instantiateMVars expectedType;
    let expectedType := expectedType.consumeMData;
    expectedType ← whnf expectedType;
    matchConstStruct expectedType.getAppFn
      (fun _ => throwError ("invalid constructor ⟨...⟩, expected type must be a structure " ++ indentExpr expectedType))
      (fun val _ ctor => do
        newStx ← `($(mkCIdentFrom stx ctor.name) $(args.getSepElems)*);
        withMacroExpansion stx newStx $ elabTerm newStx expectedType?)
  | none => throwError "invalid constructor ⟨...⟩, expected type must be known"
| _ => throwUnsupportedSyntax

@[builtinMacro Lean.Parser.Term.show] def expandShow : Macro :=
fun stx => match_syntax stx with
| `(show $type from $val)         => let thisId := mkIdentFrom stx `this; `(let! $thisId : $type := $val; $thisId)
| `(show $type by $tac:tacticSeq) => `(show $type from by $tac:tacticSeq)
| _                               => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.have] def expandHave : Macro :=
fun stx =>
let stx := stx.setArg 4 (mkNullNode #[mkAtomFrom stx ";"]); -- HACK
match_syntax stx with
| `(have $type from $val; $body)              => let thisId := mkIdentFrom stx `this; `(let! $thisId : $type := $val; $body)
| `(have $type by $tac:tacticSeq; $body)      => `(have $type from by $tac:tacticSeq; $body)
| `(have $type := $val; $body)                => let thisId := mkIdentFrom stx `this; `(let! $thisId : $type := $val; $body)
| `(have $x : $type from $val; $body)         => `(let! $x:ident : $type := $val; $body)
| `(have $x : $type by $tac:tacticSeq; $body) => `(have $x : $type from by $tac:tacticSeq; $body)
| `(have $x : $type := $val; $body)           => `(let! $x:ident : $type := $val; $body)
| _                                           => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.where] def expandWhere : Macro :=
fun stx => match_syntax stx with
| `($body where $decls:letDecl*) =>  do
  let decls := decls.getEvenElems;
  decls.foldrM
    (fun decl body => `(let $decl:letDecl; $body))
    body
| _                      => Macro.throwUnsupported

private def elabParserMacroAux (prec : Syntax) (e : Syntax) : TermElabM Syntax := do
some declName ← getDeclName?
  | throwError "invalid `parser!` macro, it must be used in definitions";
match extractMacroScopes declName with
| { name := Name.str _ s _, scopes :=  scps, .. } => do
  let kind := quote declName;
  let s    := quote s;
  p ← `(Lean.Parser.leadingNode $kind $prec $e);
  if scps == [] then
    -- TODO simplify the following quotation as soon as we have coercions
    `(HasOrelse.orelse (Lean.Parser.mkAntiquot $s (some $kind)) $p)
  else
    -- if the parser decl is hidden by hygiene, it doesn't make sense to provide an antiquotation kind
    `(HasOrelse.orelse (Lean.Parser.mkAntiquot $s none) $p)
| _  => throwError "invalid `parser!` macro, unexpected declaration name"

@[builtinTermElab «parser!»] def elabParserMacro : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `(parser! $e)         => elabParserMacroAux (quote Parser.maxPrec) e
| `(parser! : $prec $e) => elabParserMacroAux prec e
| _                     => throwUnsupportedSyntax

private def elabTParserMacroAux (prec : Syntax) (e : Syntax) : TermElabM Syntax := do
declName? ← getDeclName?;
match declName? with
| some declName => let kind := quote declName; `(Lean.Parser.trailingNode $kind $prec $e)
| none          => throwError "invalid `tparser!` macro, it must be used in definitions"

@[builtinTermElab «tparser!»] def elabTParserMacro : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `(tparser! $e)         => elabTParserMacroAux (quote Parser.maxPrec) e
| `(tparser! : $prec $e) => elabTParserMacroAux prec e
| _                      => throwUnsupportedSyntax

private def mkNativeReflAuxDecl (type val : Expr) : TermElabM Name := do
auxName ← mkAuxName `_nativeRefl;
let decl := Declaration.defnDecl {
  name := auxName, lparams := [], type := type, value := val,
  hints := ReducibilityHints.abbrev,
  isUnsafe := false };
addDecl decl;
compileDecl decl;
pure auxName

private def elabClosedTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
e ← elabTermAndSynthesize stx expectedType?;
when e.hasMVar $
  throwError ("invalid macro application, term contains metavariables" ++ indentExpr e);
when e.hasFVar $
  throwError ("invalid macro application, term contains free variables" ++ indentExpr e);
pure e

@[builtinTermElab «nativeRefl»] def elabNativeRefl : TermElab :=
fun stx _ => do
  let arg := stx.getArg 1;
  e ← elabClosedTerm arg none;
  type ← inferType e;
  type ← whnf type;
  unless (type.isConstOf `Bool || type.isConstOf `Nat) $
    throwError ("invalid `nativeRefl!` macro application, term must have type `Nat` or `Bool`" ++ indentExpr type);
  auxDeclName ← mkNativeReflAuxDecl type e;
  let isBool := type.isConstOf `Bool;
  let reduceValFn := if isBool then `Lean.reduceBool else `Lean.reduceNat;
  let reduceThm   := if isBool then `Lean.ofReduceBool else `Lean.ofReduceNat;
  let aux         := Lean.mkConst auxDeclName;
  let reduceVal   := mkApp (Lean.mkConst reduceValFn) aux;
  val? ← liftMetaM $ Meta.reduceNative? reduceVal;
  match val? with
  | none     => throwError ("failed to reduce term at `nativeRefl!` macro application" ++ indentExpr e)
  | some val => do
    rflPrf ← mkEqRefl val;
    let r  := mkApp3 (Lean.mkConst reduceThm) aux val rflPrf;
    eq ← mkEq e val;
    mkExpectedTypeHint r eq

private def getPropToDecide (arg : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=
if arg.isOfKind `Lean.Parser.Term.hole then do
  tryPostponeIfNoneOrMVar expectedType?;
  match expectedType? with
  | none => throwError "invalid macro, expected type is not available"
  | some expectedType => do
    expectedType ← instantiateMVars expectedType;
    when (expectedType.hasFVar || expectedType.hasMVar) $
      throwError ("expected type must not contain free or meta variables" ++ indentExpr expectedType);
    pure expectedType
else
  let prop := mkSort levelZero;
  elabClosedTerm arg prop

@[builtinTermElab «nativeDecide»] def elabNativeDecide : TermElab :=
fun stx expectedType? => do
  let arg  := stx.getArg 1;
  p ← getPropToDecide arg expectedType?;
  d ← mkAppM `Decidable.decide #[p];
  auxDeclName ← mkNativeReflAuxDecl (Lean.mkConst `Bool) d;
  rflPrf ← mkEqRefl (toExpr true);
  let r   := mkApp3 (Lean.mkConst `Lean.ofReduceBool) (Lean.mkConst auxDeclName) (toExpr true) rflPrf;
  mkExpectedTypeHint r p

@[builtinTermElab Lean.Parser.Term.decide] def elabDecide : TermElab :=
fun stx expectedType? => do
  let arg  := stx.getArg 1;
  p ← getPropToDecide arg expectedType?;
  d ← mkAppM `Decidable.decide #[p];
  d ← instantiateMVars d;
  let s := d.appArg!; -- get instance from `d`
  rflPrf ← mkEqRefl (toExpr true);
  pure $ mkApp3 (Lean.mkConst `ofDecideEqTrue) p s rflPrf

def expandInfix (f : Syntax) : Macro :=
fun stx => do
  -- term `op` term
  let a := stx.getArg 0;
  let b := stx.getArg 2;
  pure (mkAppStx f #[a, b])

def expandInfixOp (op : Name) : Macro :=
fun stx => expandInfix (mkCIdentFrom (stx.getArg 1) op) stx

def expandPrefixOp (op : Name) : Macro :=
fun stx => do
  -- `op` term
  let a := stx.getArg 1;
  pure (mkAppStx (mkCIdentFrom (stx.getArg 0) op) #[a])


@[builtinMacro Lean.Parser.Term.prod] def expandProd : Macro := expandInfixOp `Prod
@[builtinMacro Lean.Parser.Term.fcomp] def ExpandFComp : Macro := expandInfixOp `Function.comp

@[builtinMacro Lean.Parser.Term.add] def expandAdd : Macro := expandInfixOp `HasAdd.add
@[builtinMacro Lean.Parser.Term.sub] def expandSub : Macro := expandInfixOp `HasSub.sub
@[builtinMacro Lean.Parser.Term.mul] def expandMul : Macro := expandInfixOp `HasMul.mul
@[builtinMacro Lean.Parser.Term.div] def expandDiv : Macro := expandInfixOp `HasDiv.div
@[builtinMacro Lean.Parser.Term.mod] def expandMod : Macro := expandInfixOp `HasMod.mod
@[builtinMacro Lean.Parser.Term.modN] def expandModN : Macro := expandInfixOp `HasModN.modn
@[builtinMacro Lean.Parser.Term.pow] def expandPow : Macro := expandInfixOp `HasPow.pow

@[builtinMacro Lean.Parser.Term.le] def expandLE : Macro := expandInfixOp `HasLessEq.LessEq
@[builtinMacro Lean.Parser.Term.ge] def expandGE : Macro := expandInfixOp `GreaterEq
@[builtinMacro Lean.Parser.Term.lt] def expandLT : Macro := expandInfixOp `HasLess.Less
@[builtinMacro Lean.Parser.Term.gt] def expandGT : Macro := expandInfixOp `Greater
@[builtinMacro Lean.Parser.Term.eq] def expandEq : Macro := expandInfixOp `Eq
@[builtinMacro Lean.Parser.Term.ne] def expandNe : Macro := expandInfixOp `Ne
@[builtinMacro Lean.Parser.Term.beq] def expandBEq : Macro := expandInfixOp `HasBeq.beq
@[builtinMacro Lean.Parser.Term.bne] def expandBNe : Macro := expandInfixOp `bne
@[builtinMacro Lean.Parser.Term.heq] def expandHEq : Macro := expandInfixOp `HEq
@[builtinMacro Lean.Parser.Term.equiv] def expandEquiv : Macro := expandInfixOp `HasEquiv.Equiv

@[builtinMacro Lean.Parser.Term.and] def expandAnd : Macro := expandInfixOp `And
@[builtinMacro Lean.Parser.Term.or] def expandOr : Macro := expandInfixOp `Or
@[builtinMacro Lean.Parser.Term.iff] def expandIff : Macro := expandInfixOp `Iff

@[builtinMacro Lean.Parser.Term.band] def expandBAnd : Macro := expandInfixOp `and
@[builtinMacro Lean.Parser.Term.bor] def expandBOr : Macro := expandInfixOp `or

@[builtinMacro Lean.Parser.Term.append] def expandAppend : Macro := expandInfixOp `HasAppend.append
@[builtinMacro Lean.Parser.Term.cons] def expandCons : Macro := expandInfixOp `List.cons

@[builtinMacro Lean.Parser.Term.andthen] def expandAndThen : Macro := expandInfixOp `HasAndthen.andthen
@[builtinMacro Lean.Parser.Term.bindOp] def expandBind : Macro := expandInfixOp `HasBind.bind

@[builtinMacro Lean.Parser.Term.seq] def expandseq : Macro := expandInfixOp `HasSeq.seq
@[builtinMacro Lean.Parser.Term.seqLeft] def expandseqLeft : Macro := expandInfixOp `HasSeqLeft.seqLeft
@[builtinMacro Lean.Parser.Term.seqRight] def expandseqRight : Macro := expandInfixOp `HasSeqRight.seqRight

@[builtinMacro Lean.Parser.Term.map] def expandMap : Macro := expandInfixOp `Functor.map
@[builtinMacro Lean.Parser.Term.mapRev] def expandMapRev : Macro := expandInfixOp `Functor.mapRev

@[builtinMacro Lean.Parser.Term.orelse] def expandOrElse : Macro := expandInfixOp `HasOrelse.orelse
@[builtinMacro Lean.Parser.Term.orM] def expandOrM : Macro := expandInfixOp `orM
@[builtinMacro Lean.Parser.Term.andM] def expandAndM : Macro := expandInfixOp `andM

@[builtinMacro Lean.Parser.Term.not] def expandNot : Macro := expandPrefixOp `Not
@[builtinMacro Lean.Parser.Term.bnot] def expandBNot : Macro := expandPrefixOp `not

@[builtinTermElab panic] def elabPanic : TermElab :=
fun stx expectedType? => do
  let arg := stx.getArg 1;
  pos ← getRefPosition;
  env ← getEnv;
  declName? ← getDeclName?;
  stxNew ← match declName? with
  | some declName => `(panicWithPosWithDecl $(quote (toString env.mainModule)) $(quote (toString declName)) $(quote pos.line) $(quote pos.column) $arg)
  | none => `(panicWithPos $(quote (toString env.mainModule)) $(quote pos.line) $(quote pos.column) $arg);
  withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?

@[builtinMacro Lean.Parser.Term.unreachable]  def expandUnreachable : Macro :=
fun stx => `(panic! "unreachable code has been reached")

@[builtinMacro Lean.Parser.Term.assert]  def expandAssert : Macro :=
fun stx =>
  -- TODO: support for disabling runtime assertions
  let cond := stx.getArg 1;
  let body := stx.getArg 3;
  match cond.reprint with
  | some code => `(if $cond then $body else panic! ("assertion violation: " ++ $(quote code)))
  | none => `(if $cond then $body else panic! ("assertion violation"))

@[builtinMacro Lean.Parser.Term.dbgTrace]  def expandDbgTrace : Macro :=
fun stx =>
  let arg  := stx.getArg 1;
  let body := stx.getArg 3;
  `(dbgTrace $arg fun _ => $body)

@[builtinMacro Lean.Parser.Term.«sorry»]  def expandSorry : Macro :=
fun _ => `(sorryAx _ false)

@[builtinTermElab emptyC] def expandEmptyC : TermElab :=
fun stx expectedType? => do
  stxNew ← `(HasEmptyc.emptyc);
  withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?

/-
TODO
@[builtinTermElab] def elabsubst : TermElab := expandInfixOp infixR " ▸ " 75
-/

end Term
end Elab
end Lean
