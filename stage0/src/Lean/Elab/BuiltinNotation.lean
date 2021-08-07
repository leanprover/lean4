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
        (fun _ => throwError "invalid constructor ⟨...⟩, expected type must be an inductive type {indentExpr expectedType}")
        (fun ival us => do
          match ival.ctors with
          | [ctor] =>
            let cinfo ← getConstInfoCtor ctor
            let numExplicitFields ← forallTelescopeReducing cinfo.type fun xs _ => do
              let mut n := 0
              for i in [cinfo.numParams:xs.size] do
                if (← getFVarLocalDecl xs[i]).binderInfo.isExplicit then
                  n := n + 1
              return n
            let args := args.getElems
            if args.size < numExplicitFields then
              throwError "invalid constructor ⟨...⟩, insufficient number of arguments, constructs '{ctor}' has #{numExplicitFields} explicit fields, but only #{args.size} provided"
            let newStx ←
              if args.size == numExplicitFields then
                `($(mkCIdentFrom stx ctor) $(args)*)
              else if numExplicitFields == 0 then
                throwError "invalid constructor ⟨...⟩, insufficient number of arguments, constructs '{ctor}' does not have explicit fields, but #{args.size} provided"
              else
                let extra := args[numExplicitFields-1:args.size]
                let newLast ← `(⟨$[$extra],*⟩)
                let newArgs := args[0:numExplicitFields-1].toArray.push newLast
                `($(mkCIdentFrom stx ctor) $(newArgs)*)
            withMacroExpansion stx newStx $ elabTerm newStx expectedType?
          | _ => throwError "invalid constructor ⟨...⟩, expected type must be an inductive type with only one constructor {indentExpr expectedType}")
    | none => throwError "invalid constructor ⟨...⟩, expected type must be known"
  | _ => throwUnsupportedSyntax

@[builtinTermElab borrowed] def elabBorrowed : TermElab := fun stx expectedType? =>
  match stx with
  | `(@& $e) => return markBorrowed (← elabTerm e expectedType?)
  | _ => throwUnsupportedSyntax

@[builtinMacro Lean.Parser.Term.show] def expandShow : Macro := fun stx =>
  match stx with
  | `(show $type from $val)            => let thisId := mkIdentFrom stx `this; `(let_fun $thisId : $type := $val; $thisId)
  | `(show $type by%$b $tac:tacticSeq) => `(show $type from by%$b $tac:tacticSeq)
  | _                                  => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.have] def expandHave : Macro := fun stx =>
  let thisId := mkIdentFrom stx `this
  match stx with
  | `(have $x $bs* $[: $type]? := $val $[;]? $body)            => `(let_fun $x $bs* $[: $type]? := $val; $body)
  | `(have $[: $type]? := $val $[;]? $body)                    => `(have $thisId:ident $[: $type]? := $val; $body)
  | `(have $x $bs* $[: $type]? $alts:matchAlts $[;]? $body)    => `(let_fun $x $bs* $[: $type]? $alts:matchAlts; $body)
  | `(have $[: $type]? $alts:matchAlts $[;]? $body)            => `(have $thisId:ident $[: $type]? $alts:matchAlts; $body)
  | `(have $pattern:term $[: $type]? := $val:term $[;]? $body) => `(let_fun $pattern:term $[: $type]? := $val:term ; $body)
  | _                                                          => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.suffices] def expandSuffices : Macro
  | `(suffices $[$x :]? $type from $val $[;]? $body)            => `(have $[$x]? : $type := $body; $val)
  | `(suffices $[$x :]? $type by%$b $tac:tacticSeq $[;]? $body) => `(have $[$x]? : $type := $body; by%$b $tac:tacticSeq)
  | _                                                           => Macro.throwUnsupported

open Lean.Parser in
private def elabParserMacroAux (prec : Syntax) (e : Syntax) : TermElabM Syntax := do
  let (some declName) ← getDeclName?
    | throwError "invalid `leading_parser` macro, it must be used in definitions"
  match extractMacroScopes declName with
  | { name := Name.str _ s _, scopes :=  scps, .. } =>
    let kind := quote declName
    let s    := quote s
    -- if the parser decl is hidden by hygiene, it doesn't make sense to provide an antiquotation kind
    let antiquotKind ← if scps == [] then `(some $kind) else `(none)
    ``(withAntiquot (mkAntiquot $s $antiquotKind) (leadingNode $kind $prec $e))
  | _  => throwError "invalid `leading_parser` macro, unexpected declaration name"

@[builtinTermElab «leading_parser»] def elabLeadingParserMacro : TermElab :=
  adaptExpander fun stx => match stx with
  | `(leading_parser $e)         => elabParserMacroAux (quote Parser.maxPrec) e
  | `(leading_parser : $prec $e) => elabParserMacroAux prec e
  | _                            => throwUnsupportedSyntax

private def elabTParserMacroAux (prec lhsPrec : Syntax) (e : Syntax) : TermElabM Syntax := do
  let declName? ← getDeclName?
  match declName? with
  | some declName => let kind := quote declName; ``(Lean.Parser.trailingNode $kind $prec $lhsPrec $e)
  | none          => throwError "invalid `trailing_parser` macro, it must be used in definitions"

@[builtinTermElab «trailing_parser»] def elabTrailingParserMacro : TermElab :=
  adaptExpander fun stx => match stx with
  | `(trailing_parser$[:$prec?]?$[:$lhsPrec?]? $e) =>
    elabTParserMacroAux (prec?.getD <| quote Parser.maxPrec) (lhsPrec?.getD <| quote 0) e
  | _ => throwUnsupportedSyntax

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
    if k == ``Lean.Parser.Term.paren then false
    else if k == ``Lean.Parser.Term.cdot then true
    else args.any hasCDot
  | _ => false

/--
  Return `some` if succeeded expanding `·` notation occurring in
  the given syntax. Otherwise, return `none`.
  Examples:
  - `· + 1` => `fun _a_1 => _a_1 + 1`
  - `f · · b` => `fun _a_1 _a_2 => f _a_1 _a_2 b` -/
partial def expandCDot? (stx : Syntax) : MacroM (Option Syntax) := do
  if hasCDot stx then
    let (newStx, binders) ← (go stx).run #[];
    `(fun $binders* => $newStx)
  else
    pure none
where
  /--
    Auxiliary function for expanding the `·` notation.
    The extra state `Array Syntax` contains the new binder names.
    If `stx` is a `·`, we create a fresh identifier, store in the
    extra state, and return it. Otherwise, we just return `stx`. -/
  go : Syntax → StateT (Array Syntax) MacroM Syntax
    | stx@(Syntax.node k args) =>
      if k == ``Lean.Parser.Term.paren then pure stx
      else if k == ``Lean.Parser.Term.cdot then withFreshMacroScope do
        let id ← `(a)
        modify fun s => s.push id;
        pure id
      else do
        let args ← args.mapM go
        pure $ Syntax.node k args
    | stx => pure stx

/--
  Helper method for elaborating terms such as `(.+.)` where a constant name is expected.
  This method is usually used to implement tactics that function names as arguments (e.g., `simp`).
-/
def elabCDotFunctionAlias? (stx : Syntax) : TermElabM (Option Expr) := do
  let some stx ← liftMacroM <| expandCDotArg? stx | pure none
  let stx ← liftMacroM <| expandMacros stx
  match stx with
  | `(fun $binders* => $f:ident $args*) =>
    if binders == args then
      try Term.resolveId? f catch _ => return none
    else
      return none
  | `(fun $binders* => binop% $f:ident $a $b) =>
    if binders == #[a, b] then
      try Term.resolveId? f catch _ => return none
    else
      return none
  | _ => return none
where
  expandCDotArg? (stx : Syntax) : MacroM (Option Syntax) :=
    match stx with
    | `(($e)) => Term.expandCDot? e
    | _ => Term.expandCDot? stx


/--
  Try to expand `·` notation.
  Recall that in Lean the `·` notation must be surrounded by parentheses.
  We may change this is the future, but right now, here are valid examples
  - `(· + 1)`
  - `(f ⟨·, 1⟩ ·)`
  - `(· + ·)`
  - `(f · a b)` -/
@[builtinMacro Lean.Parser.Term.paren] def expandParen : Macro
  | `(())           => `(Unit.unit)
  | `(($e : $type)) => do
    match (← expandCDot? e) with
    | some e => `(($e : $type))
    | none   => Macro.throwUnsupported
  | `(($e))         => return (← expandCDot? e).getD e
  | `(($e, $es,*))  => do
    let pairs ← mkPairs (#[e] ++ es)
    (← expandCDot? pairs).getD pairs
  | stx =>
    if !stx[1][0].isMissing && stx[1][1].isMissing then
      -- parsed `(` and `term`, assume it's a basic parenthesis to get any elaboration output at all
      `(($(stx[1][0])))
    else
      throw <| Macro.Exception.error stx "unexpected parentheses notation"

@[builtinTermElab paren] def elabParen : TermElab := fun stx expectedType? => do
  match stx with
  | `(($e : $type)) =>
    let type ← withSynthesize (mayPostpone := true) <| elabType type
    let e ← elabTerm e type
    ensureHasType type e
  | _ => throwUnsupportedSyntax

@[builtinTermElab subst] def elabSubst : TermElab := fun stx expectedType? => do
  let expectedType ← tryPostponeIfHasMVars expectedType? "invalid `▸` notation"
  match stx with
  | `($heq ▸ $h) => do
     let mut heq ← elabTerm heq none
     let heqType ← inferType heq
     let heqType ← instantiateMVars heqType
     match (← Meta.matchEq? heqType) with
     | none => throwError "invalid `▸` notation, argument{indentExpr heq}\nhas type{indentExpr heqType}\nequality expected"
     | some (α, lhs, rhs) =>
       let mut lhs := lhs
       let mut rhs := rhs
       let mkMotive (typeWithLooseBVar : Expr) := do
         withLocalDeclD (← mkFreshUserName `x) α fun x => do
           mkLambdaFVars #[x] $ typeWithLooseBVar.instantiate1 x
       let mut expectedAbst ← kabstract expectedType rhs
       unless expectedAbst.hasLooseBVars do
         expectedAbst ← kabstract expectedType lhs
         unless expectedAbst.hasLooseBVars do
           throwError "invalid `▸` notation, expected type{indentExpr expectedType}\ndoes contain equation left-hand-side nor right-hand-side{indentExpr heqType}"
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
  let mut mStx := stx[2]
  if mStx.getKind == ``Lean.Parser.Term.macroDollarArg then
    mStx := mStx[1]
  let m ← elabTerm mStx (← mkArrow (mkSort levelOne) (mkSort levelOne))
  let ω ← mkFreshExprMVar (mkSort levelOne)
  let stWorld ← mkAppM ``STWorld #[ω, m]
  discard <| mkInstMVar stWorld
  mkAppM ``StateRefT' #[ω, σ, m]

@[builtinTermElab noindex] def elabNoindex : TermElab := fun stx expectedType? => do
  let e ← elabTerm stx[1] expectedType?
  return DiscrTree.mkNoindexAnnotation e

end Lean.Elab.Term
