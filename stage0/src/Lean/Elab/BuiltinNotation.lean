/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Init.Data.ToString
import Lean.Compiler.BorrowedAnnotation
import Lean.Meta.KAbstract
import Lean.Meta.Transform
import Lean.Elab.Term
import Lean.Elab.SyntheticMVars

namespace Lean.Elab.Term
open Meta

@[builtinTermElab anonymousCtor] def elabAnonymousCtor : TermElab := fun stx expectedType? =>
  match stx with
  | `(⟨$args,*⟩) => do
    tryPostponeIfNoneOrMVar expectedType?
    match expectedType? with
    | some expectedType =>
      let expectedType ← whnf expectedType
      matchConstInduct expectedType.getAppFn
        (fun _ => throwError! "invalid constructor ⟨...⟩, expected type must be an inductive type {indentExpr expectedType}")
        (fun ival us => do
          match ival.ctors with
          | [ctor] =>
            let newStx ← `($(mkCIdentFrom stx ctor) $(args)*)
            withMacroExpansion stx newStx $ elabTerm newStx expectedType?
          | _ => throwError! "invalid constructor ⟨...⟩, expected type must be an inductive type with only one constructor {indentExpr expectedType}")
    | none => throwError "invalid constructor ⟨...⟩, expected type must be known"
  | _ => throwUnsupportedSyntax

@[builtinTermElab borrowed] def elabBorrowed : TermElab := fun stx expectedType? =>
  match stx with
  | `(@& $e) => return markBorrowed (← elabTerm e expectedType?)
  | _ => throwUnsupportedSyntax

@[builtinMacro Lean.Parser.Term.show] def expandShow : Macro := fun stx =>
  match stx with
  | `(show $type from $val)         => let thisId := mkIdentFrom stx `this; `(let! $thisId : $type := $val; $thisId)
  | `(show $type by $tac:tacticSeq) => `(show $type from by $tac:tacticSeq)
  | _                               => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.have] def expandHave : Macro := fun stx =>
  let mkId (x? : Option Syntax) : Syntax :=
    x?.getD <| mkIdentFrom stx `this
  match stx with
  | `(have $[$x :]? $type from $val $[;]? $body)              => let x := mkId x; `(let! $x : $type := $val; $body)
  | `(have $[$x :]? $type := $val $[;]? $body)                => let x := mkId x; `(let! $x : $type := $val; $body)
  | `(have $[$x :]? $type by $tac:tacticSeq $[;]? $body)      => `(have $[$x :]? $type from by $tac:tacticSeq; $body)
  | _                                                         => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.suffices] def expandSuffices : Macro
  | `(suffices $[$x :]? $type from $val $[;]? $body)         => `(have $[$x :]? $type from $body; $val)
  | `(suffices $[$x :]? $type by $tac:tacticSeq $[;]? $body) => `(have $[$x :]? $type from $body; by $tac:tacticSeq)
  | _                                                        => Macro.throwUnsupported

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
      `(OrElse.orElse (Lean.Parser.mkAntiquot $s (some $kind)) $p)
    else
      -- if the parser decl is hidden by hygiene, it doesn't make sense to provide an antiquotation kind
      `(OrElse.orElse (Lean.Parser.mkAntiquot $s none) $p)
  | _  => throwError "invalid `parser!` macro, unexpected declaration name"

@[builtinTermElab «parser!»] def elabParserMacro : TermElab :=
  adaptExpander fun stx => match stx with
  | `(parser! $e)         => elabParserMacroAux (quote Parser.maxPrec) e
  | `(parser! : $prec $e) => elabParserMacroAux prec e
  | _                     => throwUnsupportedSyntax

private def elabTParserMacroAux (prec : Syntax) (e : Syntax) : TermElabM Syntax := do
  let declName? ← getDeclName?
  match declName? with
  | some declName => let kind := quote declName; `(Lean.Parser.trailingNode $kind $prec $e)
  | none          => throwError "invalid `tparser!` macro, it must be used in definitions"

@[builtinTermElab «tparser!»] def elabTParserMacro : TermElab :=
  adaptExpander fun stx => match stx with
  | `(tparser! $e)         => elabTParserMacroAux (quote Parser.maxPrec) e
  | `(tparser! : $prec $e) => elabTParserMacroAux prec e
  | _                      => throwUnsupportedSyntax

private def mkNativeReflAuxDecl (type val : Expr) : TermElabM Name := do
  let auxName ← mkAuxName `_nativeRefl
  let decl := Declaration.defnDecl {
    name := auxName, levelParams := [], type := type, value := val,
    hints := ReducibilityHints.abbrev,
    safety := DefinitionSafety.safe
  }
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
  let val? ← Meta.reduceNative? reduceVal
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
    let mut expectedType ← instantiateMVars expectedType
    if expectedType.hasFVar then
      expectedType ← zetaReduce expectedType
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
  let r ← withDefault <| whnf d
  unless r.isConstOf ``true do
    throwError! "failed to reduce to 'true'{indentExpr p}"
  let s := d.appArg! -- get instance from `d`
  let rflPrf ← mkEqRefl (toExpr true)
  pure $ mkApp3 (Lean.mkConst `ofDecideEqTrue) p s rflPrf

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

@[builtinTermElab «sorry»] def elabSorry : TermElab := fun stx expectedType? => do
  logWarning "declaration uses 'sorry'"
  let stxNew ← `(sorryAx _ false)
  withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?

@[builtinTermElab emptyC] def expandEmptyC : TermElab := fun stx expectedType? => do
  let stxNew ← `(EmptyCollection.emptyCollection)
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

private partial def hasCDot : Syntax → Bool
  | Syntax.node k args =>
    if k == `Lean.Parser.Term.paren then false
    else if k == `Lean.Parser.Term.cdot then true
    else args.any hasCDot
  | _ => false

/--
  Auxiliary function for expandind the `·` notation.
  The extra state `Array Syntax` contains the new binder names.
  If `stx` is a `·`, we create a fresh identifier, store in the
  extra state, and return it. Otherwise, we just return `stx`. -/
private partial def expandCDot : Syntax → StateT (Array Syntax) MacroM Syntax
  | stx@(Syntax.node k args) =>
    if k == `Lean.Parser.Term.paren then pure stx
    else if k == `Lean.Parser.Term.cdot then withFreshMacroScope do
      let id ← `(a)
      modify fun s => s.push id;
      pure id
    else do
      let args ← args.mapM expandCDot
      pure $ Syntax.node k args
  | stx => pure stx

/--
  Return `some` if succeeded expanding `·` notation occurring in
  the given syntax. Otherwise, return `none`.
  Examples:
  - `· + 1` => `fun _a_1 => _a_1 + 1`
  - `f · · b` => `fun _a_1 _a_2 => f _a_1 _a_2 b` -/
def expandCDot? (stx : Syntax) : MacroM (Option Syntax) := do
  if hasCDot stx then
    let (newStx, binders) ← (expandCDot stx).run #[];
    `(fun $binders* => $newStx)
  else
    pure none

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
  match (← liftMacroM <| expandCDot? stx) with
  | some stx' => withMacroExpansion stx stx' (elabTerm stx' expectedType?)
  | none      => elabTerm stx expectedType?

@[builtinTermElab paren] def elabParen : TermElab := fun stx expectedType? => do
  match stx with
  | `(())           => return Lean.mkConst `Unit.unit
  | `(($e : $type)) =>
    let type ← withSynthesize (mayPostpone := true) $ elabType type
    let e ← elabCDot e type
    ensureHasType type e
  | `(($e))         => elabCDot e expectedType?
  | `(($e, $es,*))  =>
    let pairs ← liftMacroM <| mkPairs (#[e] ++ es)
    withMacroExpansion stx pairs (elabCDot pairs expectedType?)
  | _ => throwError "unexpected parentheses notation"

@[builtinTermElab subst] def elabSubst : TermElab := fun stx expectedType? => do
  let expectedType ← tryPostponeIfHasMVars expectedType? "invalid `▸` notation"
  match stx with
  | `($heq ▸ $h) => do
     let mut heq ← elabTerm heq none
     let heqType ← inferType heq
     let heqType ← instantiateMVars heqType
     match (← Meta.matchEq? heqType) with
     | none => throwError! "invalid `▸` notation, argument{indentExpr heq}\nhas type{indentExpr heqType}\nequality expected"
     | some (α, lhs, rhs) =>
       let mut lhs := lhs
       let mut rhs := rhs
       let mkMotive (typeWithLooseBVar : Expr) :=
         withLocalDeclD (← mkFreshUserName `x) α fun x => do
           mkLambdaFVars #[x] $ typeWithLooseBVar.instantiate1 x
       let mut expectedAbst ← kabstract expectedType rhs
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
  let mut m := stx[2]
  if m.getKind == `Lean.Parser.Term.macroDollarArg then
    m := m[1]
  let m ← elabTerm m (← mkArrow (mkSort levelOne) (mkSort levelOne))
  let ω ← mkFreshExprMVar (mkSort levelOne)
  let stWorld ← mkAppM `STWorld #[ω, m]
  discard <| mkInstMVar stWorld
  mkAppM `StateRefT' #[ω, σ, m]

@[builtinTermElab noindex] def elabNoindex : TermElab := fun stx expectedType? => do
  let e ← elabTerm stx[1] expectedType?
  return DiscrTree.mkNoindexAnnotation e

end Lean.Elab.Term
