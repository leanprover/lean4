/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Init.Data.ToString
import Lean.Compiler.BorrowedAnnotation
import Lean.Meta.KAbstract
import Lean.Elab.Term
import Lean.Elab.Quotation
import Lean.Elab.SyntheticMVars

namespace Lean.Elab.Term
open Meta

@[builtinMacro Lean.Parser.Term.dollar] def expandDollar : Macro := fun stx =>
  match_syntax stx with
  | `($f $args* $ $a) => let args := args.push a; `($f $args*)
  | `($f $ $a)        => `($f $a)
  | _                 => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.if] def expandIf : Macro := fun stx =>
  match_syntax stx with
  | `(if $h : $cond then $t else $e) => `(dite $cond (fun $h:ident => $t) (fun $h:ident => $e))
  | `(if $cond then $t else $e)      => `(ite $cond $t $e)
  | _                                => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.subtype] def expandSubtype : Macro := fun stx =>
  match_syntax stx with
  | `({ $x : $type // $p }) => `(Subtype (fun ($x:ident : $type) => $p))
  | `({ $x // $p })         => `(Subtype (fun ($x:ident : _) => $p))
  | _                       => Macro.throwUnsupported

@[builtinTermElab anonymousCtor] def elabAnonymousCtor : TermElab := fun stx expectedType? =>
  match_syntax stx with
  | `(⟨$args*⟩) => do
    tryPostponeIfNoneOrMVar expectedType?
    match expectedType? with
    | some expectedType =>
      let expectedType ← whnf expectedType
      matchConstInduct expectedType.getAppFn
        (fun _ => throwError! "invalid constructor ⟨...⟩, expected type must be an inductive type {indentExpr expectedType}")
        (fun ival us => do
          match ival.ctors with
          | [ctor] =>
            let newStx ← `($(mkCIdentFrom stx ctor) $(args.getSepElems)*)
            withMacroExpansion stx newStx $ elabTerm newStx expectedType?
          | _ => throwError! "invalid constructor ⟨...⟩, expected type must be an inductive type with only one constructor {indentExpr expectedType}")
    | none => throwError "invalid constructor ⟨...⟩, expected type must be known"
  | _ => throwUnsupportedSyntax

@[builtinTermElab borrowed] def elabBorrowed : TermElab := fun stx expectedType? =>
  match_syntax stx with
  | `(@& $e) => do return markBorrowed (← elabTerm e expectedType?)
  | _ => throwUnsupportedSyntax

@[builtinMacro Lean.Parser.Term.show] def expandShow : Macro := fun stx =>
  match_syntax stx with
  | `(show $type from $val)         => let thisId := mkIdentFrom stx `this; `(let! $thisId : $type := $val; $thisId)
  | `(show $type by $tac:tacticSeq) => `(show $type from by $tac:tacticSeq)
  | _                               => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.have] def expandHave : Macro := fun stx =>
  let stx := stx.setArg 4 (mkNullNode #[mkAtomFrom stx ";"]) -- HACK
  match_syntax stx with
  | `(have $type from $val; $body)              => let thisId := mkIdentFrom stx `this; `(let! $thisId : $type := $val; $body)
  | `(have $type by $tac:tacticSeq; $body)      => `(have $type from by $tac:tacticSeq; $body)
  | `(have $type := $val; $body)                => let thisId := mkIdentFrom stx `this; `(let! $thisId : $type := $val; $body)
  | `(have $x : $type from $val; $body)         => `(let! $x:ident : $type := $val; $body)
  | `(have $x : $type by $tac:tacticSeq; $body) => `(have $x : $type from by $tac:tacticSeq; $body)
  | `(have $x : $type := $val; $body)           => `(let! $x:ident : $type := $val; $body)
  | _                                           => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.where] def expandWhere : Macro := fun stx =>
  match_syntax stx with
  | `($body where $decls:letDecl*) =>  do
    let decls := decls.getEvenElems
    decls.foldrM
      (fun decl body => `(let $decl:letDecl; $body))
      body
  | _                      => Macro.throwUnsupported

private def elabParserMacroAux (prec : Syntax) (e : Syntax) : TermElabM Syntax := do
  let (some declName) ← getDeclName?
    | throwError "invalid `parser!` macro, it must be used in definitions"
  match extractMacroScopes declName with
  | { name := Name.str _ s _, scopes :=  scps, .. } =>
    let kind := quote declName
    let s    := quote s
    let p ← `(Lean.Parser.leadingNode $kind $prec $e)
    if scps == [] then
      -- TODO simplify the following quotation as soon as we have coercions
      `(HasOrelse.orelse (Lean.Parser.mkAntiquot $s (some $kind)) $p)
    else
      -- if the parser decl is hidden by hygiene, it doesn't make sense to provide an antiquotation kind
      `(HasOrelse.orelse (Lean.Parser.mkAntiquot $s none) $p)
  | _  => throwError "invalid `parser!` macro, unexpected declaration name"

@[builtinTermElab «parser!»] def elabParserMacro : TermElab :=
  adaptExpander fun stx => match_syntax stx with
  | `(parser! $e)         => elabParserMacroAux (quote Parser.maxPrec) e
  | `(parser! : $prec $e) => elabParserMacroAux prec e
  | _                     => throwUnsupportedSyntax

private def elabTParserMacroAux (prec : Syntax) (e : Syntax) : TermElabM Syntax := do
  let declName? ← getDeclName?
  match declName? with
  | some declName => let kind := quote declName; `(Lean.Parser.trailingNode $kind $prec $e)
  | none          => throwError "invalid `tparser!` macro, it must be used in definitions"

@[builtinTermElab «tparser!»] def elabTParserMacro : TermElab :=
  adaptExpander fun stx => match_syntax stx with
  | `(tparser! $e)         => elabTParserMacroAux (quote Parser.maxPrec) e
  | `(tparser! : $prec $e) => elabTParserMacroAux prec e
  | _                      => throwUnsupportedSyntax

private def mkNativeReflAuxDecl (type val : Expr) : TermElabM Name := do
  let auxName ← mkAuxName `_nativeRefl
  let decl := Declaration.defnDecl {
    name := auxName, lparams := [], type := type, value := val,
    hints := ReducibilityHints.abbrev,
    isUnsafe := false }
  addDecl decl
  compileDecl decl
  pure auxName

private def elabClosedTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let e ← elabTermAndSynthesize stx expectedType?
  if e.hasMVar then
    throwError! "invalid macro application, term contains metavariables{indentExpr e}"
  if e.hasFVar then
    throwError! "invalid macro application, term contains free variables{indentExpr e}"
  pure e

@[builtinTermElab «nativeRefl»] def elabNativeRefl : TermElab := fun stx _ => do
  let arg := stx[1]
  let e ← elabClosedTerm arg none
  let type ← inferType e
  let type ← whnf type
  unless type.isConstOf `Bool || type.isConstOf `Nat do
    throwError! "invalid `nativeRefl!` macro application, term must have type `Nat` or `Bool`{indentExpr type}"
  let auxDeclName ← mkNativeReflAuxDecl type e
  let isBool := type.isConstOf `Bool
  let reduceValFn := if isBool then `Lean.reduceBool else `Lean.reduceNat
  let reduceThm   := if isBool then `Lean.ofReduceBool else `Lean.ofReduceNat
  let aux         := Lean.mkConst auxDeclName
  let reduceVal   := mkApp (Lean.mkConst reduceValFn) aux
  let val? ← liftMetaM $ Meta.reduceNative? reduceVal
  match val? with
  | none     => throwError! "failed to reduce term at `nativeRefl!` macro application{e}"
  | some val =>
    let rflPrf ← mkEqRefl val
    let r  := mkApp3 (Lean.mkConst reduceThm) aux val rflPrf
    let eq ← mkEq e val
    mkExpectedTypeHint r eq

private def getPropToDecide (expectedType? : Option Expr) : TermElabM Expr := do
  tryPostponeIfNoneOrMVar expectedType?
  match expectedType? with
  | none => throwError "invalid macro, expected type is not available"
  | some expectedType =>
    synthesizeSyntheticMVars
    let expectedType ← instantiateMVars expectedType
    if expectedType.hasFVar || expectedType.hasMVar then
      throwError! "expected type must not contain free or meta variables{indentExpr expectedType}"
    pure expectedType

@[builtinTermElab «nativeDecide»] def elabNativeDecide : TermElab := fun stx expectedType? => do
  let p ← getPropToDecide expectedType?
  let d ← mkDecide p
  let auxDeclName ← mkNativeReflAuxDecl (Lean.mkConst `Bool) d
  let rflPrf ← mkEqRefl (toExpr true)
  let r   := mkApp3 (Lean.mkConst `Lean.ofReduceBool) (Lean.mkConst auxDeclName) (toExpr true) rflPrf
  mkExpectedTypeHint r p

@[builtinTermElab Lean.Parser.Term.decide] def elabDecide : TermElab := fun stx expectedType? => do
  let p ← getPropToDecide expectedType?
  let d ← mkDecide p
  let d ← instantiateMVars d
  let s := d.appArg! -- get instance from `d`
  let rflPrf ← mkEqRefl (toExpr true)
  pure $ mkApp3 (Lean.mkConst `ofDecideEqTrue) p s rflPrf

def expandInfix (f : Syntax) : Macro := fun stx => do
  -- term `op` term
  let a := stx[0]
  let b := stx[2]
  pure (mkAppStx f #[a, b])

def expandInfixOp (op : Name) : Macro := fun stx =>
  expandInfix (mkCIdentFrom stx[1] op) stx

def expandPrefixOp (op : Name) : Macro := fun stx => do
  -- `op` term
  let a := stx[1]
  pure (mkAppStx (mkCIdentFrom stx[0] op) #[a])


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
@[builtinMacro Lean.Parser.Term.uminus] def expandUMinus : Macro := expandPrefixOp `HasNeg.neg

@[builtinTermElab panic] def elabPanic : TermElab := fun stx expectedType? => do
  let arg := stx[1]
  let pos ← getRefPosition
  let env ← getEnv
  let stxNew ← match (← getDeclName?) with
  | some declName => `(panicWithPosWithDecl $(quote (toString env.mainModule)) $(quote (toString declName)) $(quote pos.line) $(quote pos.column) $arg)
  | none => `(panicWithPos $(quote (toString env.mainModule)) $(quote pos.line) $(quote pos.column) $arg)
  withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?

@[builtinMacro Lean.Parser.Term.unreachable]  def expandUnreachable : Macro := fun stx =>
  `(panic! "unreachable code has been reached")

@[builtinMacro Lean.Parser.Term.assert]  def expandAssert : Macro := fun stx =>
  -- TODO: support for disabling runtime assertions
  let cond := stx[1]
  let body := stx[3]
  match cond.reprint with
  | some code => `(if $cond then $body else panic! ("assertion violation: " ++ $(quote code)))
  | none => `(if $cond then $body else panic! ("assertion violation"))

@[builtinMacro Lean.Parser.Term.dbgTrace]  def expandDbgTrace : Macro := fun stx =>
  let arg  := stx[1]
  let body := stx[3]
  if arg.getKind == interpolatedStrKind then
    `(dbgTrace (s! $arg) fun _ => $body)
  else
    `(dbgTrace (toString $arg) fun _ => $body)

@[builtinMacro Lean.Parser.Term.«sorry»]  def expandSorry : Macro := fun _ =>
  `(sorryAx _ false)

@[builtinTermElab emptyC] def expandEmptyC : TermElab := fun stx expectedType? => do
  let stxNew ← `(HasEmptyc.emptyc)
  withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?

/-- Return syntax `Prod.mk elems[0] (Prod.mk elems[1] ... (Prod.mk elems[elems.size - 2] elems[elems.size - 1])))` -/
partial def mkPairs (elems : Array Syntax) : MacroM Syntax :=
  let rec loop (i : Nat) (acc : Syntax) := do
    if i > 0 then
      let i    := i - 1
      let elem := elems[i]
      let acc ← `(Prod.mk $elem $acc)
      loop i acc
    else
      pure acc
  loop (elems.size - 1) elems.back

/--
  Try to expand `·` notation, and if successful elaborate result.
  This method is used to elaborate the Lean parentheses notation.
  Recall that in Lean the `·` notation must be surrounded by parentheses.
  We may change this is the future, but right now, here are valid examples
  - `(· + 1)`
  - `(f ⟨·, 1⟩ ·)`
  - `(· + ·)`
  - `(f · a b)` -/
private def elabCDot (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  match (← liftMacroM $ expandCDot? stx) with
  | some stx' => withMacroExpansion stx stx' (elabTerm stx' expectedType?)
  | none      => elabTerm stx expectedType?

@[builtinTermElab paren] def elabParen : TermElab := fun stx expectedType? =>
  match_syntax stx with
  | `(())           => pure $ Lean.mkConst `Unit.unit
  | `(($e : $type)) => do
    let type ← withSynthesize (mayPostpone := true) $ elabType type
    let e ← elabCDot e type
    ensureHasType type e
  | `(($e))         => elabCDot e expectedType?
  | `(($e, $es*))   => do
    let pairs ← liftMacroM $ mkPairs (#[e] ++ es.getEvenElems)
    withMacroExpansion stx pairs (elabTerm pairs expectedType?)
  | _ => throwError "unexpected parentheses notation"

@[builtinTermElab subst] def elabSubst : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  let some expectedType ← pure expectedType? |
    throwError! "invalid `▸` notation, expected type must be known"
  let expectedType ← instantiateMVars expectedType
  if expectedType.hasExprMVar then
    tryPostpone
    throwError! "invalid `▸` notation, expected type contains metavariables{indentExpr expectedType}"
  match_syntax stx with
  | `($heq ▸ $h) => do
     let heq ← elabTerm heq none
     let heqType ← inferType heq
     let heqType ← instantiateMVars heqType
     match (← Meta.matchEq? heqType) with
     | none => throwError! "invalid `▸` notation, argument{indentExpr heq}\nhas type{indentExpr heqType}\nequality expected"
     | some (α, lhs, rhs) =>
       let mkMotive (typeWithLooseBVar : Expr) :=
         withLocalDeclD (← mkFreshUserName `x) α fun x => do
           mkLambdaFVars #[x] $ typeWithLooseBVar.instantiate1 x
       let expectedAbst ← kabstract expectedType rhs
       unless expectedAbst.hasLooseBVars do
         expectedAbst ← kabstract expectedType lhs
         unless expectedAbst.hasLooseBVars do
           throwError! "invalid `▸` notation, expected type{indentExpr expectedType}\ndoes contain equation left-hand-side nor right-hand-side{indentExpr heqType}"
         heq ← mkEqSymm heq
         (lhs, rhs) := (rhs, lhs)
       let hExpectedType := expectedAbst.instantiate1 lhs
       let h ← withRef h do
         let h ← elabTerm h hExpectedType
         try
           ensureHasType hExpectedType h
         catch ex =>
           -- if `rhs` occurs in `hType`, we try to apply `heq` to `h` too
           let hType ← inferType h
           let hTypeAbst ← kabstract hType rhs
           unless hTypeAbst.hasLooseBVars do
             throw ex
           let hTypeNew := hTypeAbst.instantiate1 lhs
           unless (← isDefEq hExpectedType hTypeNew) do
             throw ex
           mkEqNDRec (← mkMotive hTypeAbst) h (← mkEqSymm heq)
       mkEqNDRec (← mkMotive expectedAbst) h heq
  | _ => throwUnsupportedSyntax

@[builtinTermElab stateRefT] def elabStateRefT : TermElab := fun stx _ => do
  let σ ← elabType stx[1]
  let m := stx[2]
  if m.getKind == `Lean.Parser.Term.macroDollarArg then
    m := m[1]
  let m ← elabTerm m (← mkArrow (mkSort levelOne) (mkSort levelOne))
  let ω ← mkFreshExprMVar (mkSort levelOne)
  let stWorld ← mkAppM `STWorld #[ω, m]
  mkInstMVar stWorld
  mkAppM `StateRefT' #[ω, σ, m]

end Lean.Elab.Term
