/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Gabriel Ebner
-/
prelude
import Lean.Compiler.BorrowedAnnotation
import Lean.Meta.KAbstract
import Lean.Meta.Closure
import Lean.Meta.MatchUtil
import Lean.Compiler.ImplementedByAttr
import Lean.Elab.SyntheticMVars
import Lean.Elab.Eval
import Lean.Elab.Binders

namespace Lean.Elab.Term
open Meta

@[builtin_term_elab coeNotation] def elabCoe : TermElab := fun stx expectedType? => do
  let stx := stx[1]
  tryPostponeIfNoneOrMVar expectedType?
  let e ← elabTerm stx none
  if expectedType?.isNone then
    throwError "invalid coercion notation, expected type is not known"
  ensureHasType expectedType? e

@[builtin_term_elab coeFunNotation] def elabCoeFunNotation : TermElab := fun stx _ => do
  let x ← elabTerm stx[1] none
  if let some ty ← coerceToFunction? x then
    return ty
  else
    throwError "cannot coerce to function{indentExpr x}"

@[builtin_term_elab coeSortNotation] def elabCoeSortNotation : TermElab := fun stx _ => do
  let x ← elabTerm stx[1] none
  if let some ty ← coerceToSort? x then
    return ty
  else
    throwError "cannot coerce to sort{indentExpr x}"

@[builtin_term_elab anonymousCtor] def elabAnonymousCtor : TermElab := fun stx expectedType? =>
  match stx with
  | `(⟨$args,*⟩) => do
    tryPostponeIfNoneOrMVar expectedType?
    match expectedType? with
    | some expectedType =>
      let expectedType ← whnf expectedType
      matchConstInduct expectedType.getAppFn
        (fun _ => throwError "invalid constructor ⟨...⟩, expected type must be an inductive type {indentExpr expectedType}")
        (fun ival _ => do
          match ival.ctors with
          | [ctor] =>
            if isPrivateNameFromImportedModule (← getEnv) ctor then
              throwError "invalid ⟨...⟩ notation, constructor for `{ival.name}` is marked as private"
            let cinfo ← getConstInfoCtor ctor
            let numExplicitFields ← forallTelescopeReducing cinfo.type fun xs _ => do
              let mut n := 0
              for h : i in [cinfo.numParams:xs.size] do
                if (← getFVarLocalDecl xs[i]).binderInfo.isExplicit then
                  n := n + 1
              return n
            let args := args.getElems
            if args.size < numExplicitFields then
              throwError "invalid constructor ⟨...⟩, insufficient number of arguments, constructs '{ctor}' has #{numExplicitFields} explicit fields, but only #{args.size} provided"
            let newStx ← if args.size == numExplicitFields then
              `($(mkCIdentFrom stx ctor (canonical := true)) $(args)*)
            else if numExplicitFields == 0 then
              throwError "invalid constructor ⟨...⟩, insufficient number of arguments, constructs '{ctor}' does not have explicit fields, but #{args.size} provided"
            else
              let extra := args[numExplicitFields-1:args.size]
              let newLast ← `(⟨$[$extra],*⟩)
              let newArgs := args[0:numExplicitFields-1].toArray.push newLast
              `($(mkCIdentFrom stx ctor (canonical := true)) $(newArgs)*)
            withMacroExpansion stx newStx $ elabTerm newStx expectedType?
          | _ => throwError "invalid constructor ⟨...⟩, expected type must be an inductive type with only one constructor {indentExpr expectedType}")
    | none => throwError "invalid constructor ⟨...⟩, expected type must be known"
  | _ => throwUnsupportedSyntax

@[builtin_term_elab borrowed] def elabBorrowed : TermElab := fun stx expectedType? =>
  match stx with
  | `(@& $e) => return markBorrowed (← elabTerm e expectedType?)
  | _ => throwUnsupportedSyntax

@[builtin_macro Lean.Parser.Term.show] def expandShow : Macro := fun stx =>
  match stx with
  | `(show $type by%$b $tac) => `(show $type from by%$b $tac)
  | _                        => Macro.throwUnsupported

@[builtin_term_elab Lean.Parser.Term.show] def elabShow : TermElab := fun stx expectedType? => do
  match stx with
  | `(show $type from $val)  =>
    /-
    We first elaborate the type and try to unify it with the expected type if available.
    Note that, we should not throw an error if the types do not unify. Recall that we have coercions and
    the following is supported in Lean 3 and 4.
    ```
    example : Int :=
      show Nat from 0
    ```
    -/
    let type ← withSynthesize (postpone := .yes) do
      let type ← elabType type
      if let some expectedType := expectedType? then
        -- Recall that a similar approach is used when elaborating applications
        discard <| isDefEq expectedType type
      return type
    /-
    Recall that we do not use the same approach used to elaborate type ascriptions.
    For the `($val : $type)` notation, we just elaborate `val` using `type` and
    ensure it has type `type`. This approach only ensure the type resulting expression
    is definitionally equal to `type`. For the `show` notation we use `let_fun` to ensure the type
    of the resulting expression is *structurally equal* `type`. Structural equality is important,
    for example, if the resulting expression is a `simp`/`rw` parameter. Here is an example:
    ```
    example (x : Nat) : (x + 0) + y = x + y := by
      rw [show x + 0 = x from rfl]
    ```
    -/
    let thisId := mkIdentFrom stx `this
    let valNew ← `(let_fun $thisId : $(← exprToSyntax type) := $val; $thisId)
    elabTerm valNew expectedType?
  | _ => throwUnsupportedSyntax

@[builtin_macro Lean.Parser.Term.have] def expandHave : Macro := fun stx =>
  match stx with
  | `(have $hy:hygieneInfo $bs* $[: $type]? := $val; $body) =>
    `(have $(HygieneInfo.mkIdent hy `this (canonical := true)) $bs* $[: $type]? := $val; $body)
  | `(have $hy:hygieneInfo $bs* $[: $type]? $alts; $body)   =>
    `(have $(HygieneInfo.mkIdent hy `this (canonical := true)) $bs* $[: $type]? $alts; $body)
  | `(have $x:ident $bs* $[: $type]? := $val; $body) => `(let_fun $x $bs* $[: $type]? := $val; $body)
  | `(have $x:ident $bs* $[: $type]? $alts; $body)   => `(let_fun $x $bs* $[: $type]? $alts; $body)
  | `(have _%$x     $bs* $[: $type]? := $val; $body) => `(let_fun _%$x $bs* $[: $type]? := $val; $body)
  | `(have _%$x     $bs* $[: $type]? $alts; $body)   => `(let_fun _%$x $bs* $[: $type]? $alts; $body)
  | `(have $pattern:term $[: $type]? := $val; $body) => `(let_fun $pattern:term $[: $type]? := $val; $body)
  | _                                                => Macro.throwUnsupported

@[builtin_macro Lean.Parser.Term.suffices] def expandSuffices : Macro
  | `(suffices%$tk $x:ident      : $type from $val; $body)   => `(have%$tk $x : $type := $body; $val)
  | `(suffices%$tk _%$x          : $type from $val; $body)   => `(have%$tk _%$x : $type := $body; $val)
  | `(suffices%$tk $hy:hygieneInfo $type from $val; $body)   => `(have%$tk $hy:hygieneInfo : $type := $body; $val)
  | `(suffices%$tk $x:ident      : $type $b:byTactic'; $body) =>
    -- Pass on `SourceInfo` of `b` to `have`. This is necessary to display the goal state in the
    -- trailing whitespace of `by` and sound since `byTactic` and `byTactic'` are identical.
    let b := ⟨b.raw.setKind `Lean.Parser.Term.byTactic⟩
    `(have%$tk $x : $type := $body; $b:byTactic)
  | `(suffices%$tk _%$x          : $type $b:byTactic'; $body) =>
    let b := ⟨b.raw.setKind `Lean.Parser.Term.byTactic⟩
    `(have%$tk _%$x : $type := $body; $b:byTactic)
  | `(suffices%$tk $hy:hygieneInfo $type $b:byTactic'; $body) =>
    let b := ⟨b.raw.setKind `Lean.Parser.Term.byTactic⟩
    `(have%$tk $hy:hygieneInfo : $type := $body; $b:byTactic)
  | _ => Macro.throwUnsupported

open Lean.Parser in
private def elabParserMacroAux (prec e : Term) (withAnonymousAntiquot : Bool) : TermElabM Syntax := do
  let (some declName) ← getDeclName?
    | throwError "invalid `leading_parser` macro, it must be used in definitions"
  match extractMacroScopes declName with
  | { name := .str _ s, .. } =>
    let kind := quote declName
    let mut p ← ``(withAntiquot
      (mkAntiquot $(quote s) $kind $(quote withAnonymousAntiquot))
      (leadingNode $kind $prec $e))
    -- cache only unparameterized parsers
    if (← getLCtx).all (·.isAuxDecl) then
      p ← ``(withCache $kind $p)
    return p
  | _  => throwError "invalid `leading_parser` macro, unexpected declaration name"

@[builtin_term_elab «leading_parser»] def elabLeadingParserMacro : TermElab :=
  adaptExpander fun
    | `(leading_parser $[: $prec?]? $[(withAnonymousAntiquot := $anon?)]? $e) =>
        elabParserMacroAux (prec?.getD (quote Parser.maxPrec)) e (anon?.all (·.raw.isOfKind ``Parser.Term.trueVal))
    | _ => throwUnsupportedSyntax

private def elabTParserMacroAux (prec lhsPrec e : Term) : TermElabM Syntax := do
  let declName? ← getDeclName?
  match declName? with
  | some declName => let kind := quote declName; ``(Lean.Parser.trailingNode $kind $prec $lhsPrec $e)
  | none          => throwError "invalid `trailing_parser` macro, it must be used in definitions"

@[builtin_term_elab «trailing_parser»] def elabTrailingParserMacro : TermElab :=
  adaptExpander fun stx => match stx with
  | `(trailing_parser$[:$prec?]?$[:$lhsPrec?]? $e) =>
    elabTParserMacroAux (prec?.getD <| quote Parser.maxPrec) (lhsPrec?.getD <| quote 0) e
  | _ => throwUnsupportedSyntax

@[builtin_term_elab Lean.Parser.Term.panic] def elabPanic : TermElab := fun stx expectedType? => do
  match stx with
  | `(panic! $arg) =>
    let pos ← getRefPosition
    let env ← getEnv
    let stxNew ← match (← getDeclName?) with
    | some declName => `(panicWithPosWithDecl $(quote (toString env.mainModule)) $(quote (toString declName)) $(quote pos.line) $(quote pos.column) $arg)
    | none => `(panicWithPos $(quote (toString env.mainModule)) $(quote pos.line) $(quote pos.column) $arg)
    withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
  | _ => throwUnsupportedSyntax

@[builtin_macro Lean.Parser.Term.unreachable]  def expandUnreachable : Macro := fun _ =>
  `(panic! "unreachable code has been reached")

@[builtin_macro Lean.Parser.Term.assert]  def expandAssert : Macro
  | `(assert! $cond; $body) =>
    match cond.raw.reprint with
    | some code => `(if $cond then $body else panic! ("assertion violation: " ++ $(quote code)))
    | none => `(if $cond then $body else panic! ("assertion violation"))
  | _ => Macro.throwUnsupported

register_builtin_option debugAssertions : Bool := {
  defValue := false
  descr := "enable `debug_assert!` statements\
    \n\
    \nDefaults to `false` unless the Lake `buildType` is `debug`."
}

@[builtin_term_elab Lean.Parser.Term.debugAssert]  def elabDebugAssert : TermElab :=
  adaptExpander fun
    | `(Parser.Term.debugAssert| debug_assert! $cond; $body) => do
      if debugAssertions.get (← getOptions) then
        `(assert! $cond; $body)
      else
        return body
    | _ => throwUnsupportedSyntax

@[builtin_macro Lean.Parser.Term.dbgTrace]  def expandDbgTrace : Macro
  | `(dbg_trace $arg:interpolatedStr; $body) => `(dbgTrace (s! $arg) fun _ => $body)
  | `(dbg_trace $arg:term; $body)            => `(dbgTrace (toString $arg) fun _ => $body)
  | _                                        => Macro.throwUnsupported

@[builtin_term_elab «sorry»] def elabSorry : TermElab := fun _ expectedType? => do
  let type ← expectedType?.getDM mkFreshTypeMVar
  mkLabeledSorry type (synthetic := false) (unique := true)

/-- Return syntax `Prod.mk elems[0] (Prod.mk elems[1] ... (Prod.mk elems[elems.size - 2] elems[elems.size - 1])))` -/
partial def mkPairs (elems : Array Term) : MacroM Term :=
  let rec loop (i : Nat) (acc : Term) := do
    if i > 0 then
      let i    := i - 1
      let elem := elems[i]!
      let acc ← `(Prod.mk $elem $acc)
      loop i acc
    else
      pure acc
  loop (elems.size - 1) elems.back!

/-- Return syntax `PProd.mk elems[0] (PProd.mk elems[1] ... (PProd.mk elems[elems.size - 2] elems[elems.size - 1])))` -/
partial def mkPPairs (elems : Array Term) : MacroM Term :=
  let rec loop (i : Nat) (acc : Term) := do
    if i > 0 then
      let i    := i - 1
      let elem := elems[i]!
      let acc ← `(PProd.mk $elem $acc)
      loop i acc
    else
      pure acc
  loop (elems.size - 1) elems.back!

/-- Return syntax `MProd.mk elems[0] (MProd.mk elems[1] ... (MProd.mk elems[elems.size - 2] elems[elems.size - 1])))` -/
partial def mkMPairs (elems : Array Term) : MacroM Term :=
  let rec loop (i : Nat) (acc : Term) := do
    if i > 0 then
      let i    := i - 1
      let elem := elems[i]!
      let acc ← `(MProd.mk $elem $acc)
      loop i acc
    else
      pure acc
  loop (elems.size - 1) elems.back!


open Parser in
partial def hasCDot : Syntax → Bool
  | Syntax.node _ k args =>
    if k == ``Term.paren || k == ``Term.typeAscription || k == ``Term.tuple then false
    else if k == ``Term.cdot then true
    else args.any hasCDot
  | _ => false

/--
  Return `some` if succeeded expanding `·` notation occurring in
  the given syntax. Otherwise, return `none`.
  Examples:
  - `· + 1` => `fun x => x + 1`
  - `f · · b` => `fun x1 x2 => f x1 x2 b` -/
partial def expandCDot? (stx : Term) : MacroM (Option Term) := do
  if hasCDot stx then
    withFreshMacroScope do
      let mut (newStx, binders) ← (go stx).run #[]
      if binders.size == 1 then
        -- It is nicer using `x` over `x1` if there's only a single binder.
        let x1 := binders[0]!
        let x := mkIdentFrom x1 (← MonadQuotation.addMacroScope `x) (canonical := true)
        binders := binders.set! 0 x
        newStx ← newStx.replaceM fun s => pure (if s == x1 then x else none)
      `(fun $binders* => $(⟨newStx⟩))
  else
    pure none
where
  /--
  Auxiliary function for expanding the `·` notation.
  The extra state `Array Syntax` contains the new binder names.
  If `stx` is a `·`, we create a fresh identifier, store it in the
  extra state, and return it. Otherwise, we just return `stx`.
  -/
  go : Syntax → StateT (Array Ident) MacroM Syntax
  | stx@`(($(_))) => pure stx
  | stx@`(·) => do
    let name ← MonadQuotation.addMacroScope <| Name.mkSimple s!"x{(← get).size + 1}"
    let id := mkIdentFrom stx name (canonical := true)
    modify (fun s => s.push id)
    pure id
  | stx => match stx with
    | .node _ k args => do
      let args ←
        if k == choiceKind then
          if args.isEmpty then
            return stx
          let s ← get
          let args' ← args.mapM (fun arg => go arg |>.run s)
          let s' := args'[0]!.2
          unless args'.all (fun (_, s'') => s''.size == s'.size) do
            Macro.throwErrorAt stx "Ambiguous notation in cdot function has different numbers of '·' arguments in each alternative."
          set s'
          pure <| args'.map Prod.fst
        else
          args.mapM go
      return .node (.fromRef stx (canonical := true)) k args
    | _ => pure stx

/--
  Helper method for elaborating terms such as `(.+.)` where a constant name is expected.
  This method is usually used to implement tactics that take function names as arguments
  (e.g., `simp`).
-/
def elabCDotFunctionAlias? (stx : Term) : TermElabM (Option Expr) := do
  let some stx ← liftMacroM <| expandCDotArg? stx | pure none
  let stx ← liftMacroM <| expandMacros stx
  match stx with
  | `(fun $binders* => $f $args*) =>
    if binders.raw.toList.isPerm args.raw.toList then
      try Term.resolveId? f catch _ => return none
    else
      return none
  | `(fun $binders* => binop% $f $a $b)
  | `(fun $binders* => binop_lazy% $f $a $b)
  | `(fun $binders* => leftact% $f $a $b)
  | `(fun $binders* => rightact% $f $a $b)
  | `(fun $binders* => binrel% $f $a $b)
  | `(fun $binders* => binrel_no_prop% $f $a $b) =>
    if binders == #[a, b] || binders == #[b, a] then
      try Term.resolveId? f catch _ => return none
    else
      return none
  | `(fun $binders* => unop% $f $a) =>
    if binders == #[a] then
      try Term.resolveId? f catch _ => return none
    else
      return none
  | _ => return none
where
  expandCDotArg? (stx : Term) : MacroM (Option Term) :=
    match stx with
    | `(($e)) => Term.expandCDot? e
    | _ => Term.expandCDot? stx

@[builtin_macro Lean.Parser.Term.paren] def expandParen : Macro
  | `(($e)) => return (← expandCDot? e).getD e
  | _       => Macro.throwUnsupported

@[builtin_macro Lean.Parser.Term.tuple] def expandTuple : Macro
  | `(()) => ``(Unit.unit)
  | `(($e, $es,*)) => do
    let pairs ← mkPairs (#[e] ++ es)
    return (← expandCDot? pairs).getD pairs
  | _ => Macro.throwUnsupported

@[builtin_macro Lean.Parser.Term.typeAscription] def expandTypeAscription : Macro
  | `(($e : $(type)?)) => do
    match (← expandCDot? e) with
    | some e => `(($e : $(type)?))
    | none   => Macro.throwUnsupported
  | _ => Macro.throwUnsupported

@[builtin_term_elab typeAscription] def elabTypeAscription : TermElab
  | `(($e : $type)), _ => do
    let type ← withSynthesize (postpone := .yes) <| elabType type
    let e ← elabTerm e type
    ensureHasType type e
  | `(($e :)), expectedType? => do
    let e ← withSynthesize (postpone := .no) <| elabTerm e none
    ensureHasType expectedType? e
  | _, _ => throwUnsupportedSyntax

/-- Return `true` if `lhs` is a free variable and `rhs` does not depend on it. -/
private def isSubstCandidate (lhs rhs : Expr) : MetaM Bool :=
  if lhs.isFVar then
    return !(← dependsOn rhs lhs.fvarId!)
  else
    return false

/--
  Given an expression `e` that is the elaboration of `stx`, if `e` is a free variable, then return `k stx`.
  Otherwise, return `(fun x => k x) e`
-/
private def withLocalIdentFor (stx : Term) (e : Expr) (k : Term → TermElabM Expr) : TermElabM Expr := do
  if e.isFVar then
    k stx
  else
    let id ← mkFreshUserName `h
    let aux ← withLocalDeclD id (← inferType e) fun x => do mkLambdaFVars #[x] (← k (mkIdentFrom stx id))
    return mkApp aux e

@[builtin_term_elab subst] def elabSubst : TermElab := fun stx expectedType? => do
  let expectedType? ← tryPostponeIfHasMVars? expectedType?
  match stx with
  | `($heqStx ▸ $hStx) => do
     synthesizeSyntheticMVars
     let mut heq ← withSynthesize <| elabTerm heqStx none
     let heqType ← inferType heq
     let heqType ← instantiateMVars heqType
     match (← Meta.matchEq? heqType) with
     | none => throwError "invalid `▸` notation, argument{indentExpr heq}\nhas type{indentExpr heqType}\nequality expected"
     | some (α, lhs, rhs) =>
       let mut lhs := lhs
       let mut rhs := rhs
       let mkMotive (lhs typeWithLooseBVar : Expr) := do
         withLocalDeclD (← mkFreshUserName `x) α fun x => do
           withLocalDeclD (← mkFreshUserName `h) (← mkEq lhs x) fun h => do
             mkLambdaFVars #[x, h] $ typeWithLooseBVar.instantiate1 x
       match expectedType? with
       | some expectedType =>
         let mut expectedAbst ← kabstract expectedType rhs
         unless expectedAbst.hasLooseBVars do
           expectedAbst ← kabstract expectedType lhs
           unless expectedAbst.hasLooseBVars do
             throwError "invalid `▸` notation, expected result type of cast is {indentExpr expectedType}\nhowever, the equality {indentExpr heq}\nof type {indentExpr heqType}\ndoes not contain the expected result type on either the left or the right hand side"
           heq ← mkEqSymm heq
           (lhs, rhs) := (rhs, lhs)
         let hExpectedType := expectedAbst.instantiate1 lhs
         let (h, badMotive?) ← withRef hStx do
           let h ← elabTerm hStx hExpectedType
           try
             return (← ensureHasType hExpectedType h, none)
           catch ex =>
             -- if `rhs` occurs in `hType`, we try to apply `heq` to `h` too
             let hType ← inferType h
             let hTypeAbst ← kabstract hType rhs
             unless hTypeAbst.hasLooseBVars do
               throw ex
             let hTypeNew := hTypeAbst.instantiate1 lhs
             unless (← isDefEq hExpectedType hTypeNew) do
               throw ex
             let motive ← mkMotive rhs hTypeAbst
             if !(← isTypeCorrect motive) then
               return (h, some motive)
             else
               return (← mkEqRec motive h (← mkEqSymm heq), none)
         let motive ← mkMotive lhs expectedAbst
         if badMotive?.isSome || !(← isTypeCorrect motive) then
           -- Before failing try to use `subst`
           if ← (isSubstCandidate lhs rhs <||> isSubstCandidate rhs lhs) then
             withLocalIdentFor heqStx heq fun heqStx => do
               let h ← instantiateMVars h
               if h.hasMVar then
                 -- If `h` has metavariables, we try to elaborate `hStx` again after we substitute `heqStx`
                 -- Remark: re-elaborating `hStx` may be problematic if `hStx` contains the `lhs` of `heqStx` which will be eliminated by `subst`
                 let stxNew ← `(by subst $heqStx; exact $hStx)
                 withMacroExpansion stx stxNew (elabTerm stxNew expectedType)
               else
                 withLocalIdentFor hStx h fun hStx => do
                   let stxNew ← `(by subst $heqStx; exact $hStx)
                   withMacroExpansion stx stxNew (elabTerm stxNew expectedType)
           else
             throwError "invalid `▸` notation, failed to compute motive for the substitution"
         else
           mkEqRec motive h heq
       | none =>
         let h ← elabTerm hStx none
         let hType ← inferType h
         let mut hTypeAbst ← kabstract hType lhs
         unless hTypeAbst.hasLooseBVars do
           hTypeAbst ← kabstract hType rhs
           unless hTypeAbst.hasLooseBVars do
             throwError "invalid `▸` notation, the equality{indentExpr heq}\nhas type {indentExpr heqType}\nbut neither side of the equality is mentioned in the type{indentExpr hType}"
           heq ← mkEqSymm heq
           (lhs, rhs) := (rhs, lhs)
         let motive ← mkMotive lhs hTypeAbst
         unless (← isTypeCorrect motive) do
           throwError "invalid `▸` notation, failed to compute motive for the substitution"
         mkEqRec motive h heq
  | _ => throwUnsupportedSyntax

@[builtin_term_elab stateRefT] def elabStateRefT : TermElab := fun stx _ => do
  let σ ← elabType stx[1]
  let mut mStx := stx[2]
  if mStx.getKind == ``Lean.Parser.Term.macroDollarArg then
    mStx := mStx[1]
  let m ← elabTerm mStx (← mkArrow (mkSort levelOne) (mkSort levelOne))
  let ω ← mkFreshExprMVar (mkSort levelOne)
  let stWorld ← mkAppM ``STWorld #[ω, m]
  discard <| mkInstMVar stWorld
  mkAppM ``StateRefT' #[ω, σ, m]

@[builtin_term_elab noindex] def elabNoindex : TermElab := fun stx expectedType? => do
  let e ← elabTerm stx[1] expectedType?
  return DiscrTree.mkNoindexAnnotation e

@[builtin_term_elab «unsafe»]
def elabUnsafe : TermElab := fun stx expectedType? =>
  match stx with
  | `(unsafe $t) => do
    let t ← elabTermAndSynthesize t expectedType?
    if (← logUnassignedUsingErrorInfos (← getMVars t)) then
      throwAbortTerm
    let t ← mkAuxDefinitionFor (← mkAuxName `unsafe) t
    let .const unsafeFn unsafeLvls .. := t.getAppFn | unreachable!
    let .defnInfo unsafeDefn ← getConstInfo unsafeFn | unreachable!
    let implName ← mkAuxName `unsafe_impl
    addDecl <| Declaration.defnDecl {
      name        := implName
      type        := unsafeDefn.type
      levelParams := unsafeDefn.levelParams
      value       := (← mkOfNonempty unsafeDefn.type)
      hints       := .opaque
      safety      := .safe
    }
    setImplementedBy implName unsafeFn
    return mkAppN (Lean.mkConst implName unsafeLvls) t.getAppArgs
  | _ => throwUnsupportedSyntax

/-- Elaborator for `by_elab`. -/
@[builtin_term_elab byElab] def elabRunElab : TermElab := fun stx expectedType? =>
  match stx with
  | `(by_elab $cmds:doSeq) => do
    if let `(Lean.Parser.Term.doSeq| $e:term) := cmds then
      if e matches `(Lean.Parser.Term.doSeq| fun $[$_args]* => $_) then
        let tac ← unsafe evalTerm
          (Option Expr → TermElabM Expr)
          (Lean.mkForall `x .default
            (mkApp (Lean.mkConst ``Option) (Lean.mkConst ``Expr))
            (mkApp (Lean.mkConst ``TermElabM) (Lean.mkConst ``Expr))) e
        return ← tac expectedType?
    (← unsafe evalTerm (TermElabM Expr) (mkApp (Lean.mkConst ``TermElabM) (Lean.mkConst ``Expr))
      (← `(do $cmds)))
  | _ => throwUnsupportedSyntax

@[builtin_term_elab Lean.Parser.Term.haveI] def elabHaveI : TermElab := fun stx expectedType? => do
  match stx with
  | `(haveI $x:ident $bs* : $ty := $val; $body) =>
    withExpectedType expectedType? fun expectedType => do
      let (ty, val) ← elabBinders bs fun bs => do
        let ty ← elabType ty
        let val ← elabTermEnsuringType val ty
        pure (← mkForallFVars bs ty, ← mkLambdaFVars bs val)
      withLocalDeclD x.getId ty fun x => do
        return (← (← elabTerm body expectedType).abstractM #[x]).instantiate #[val]
  | _ => throwUnsupportedSyntax

@[builtin_term_elab Lean.Parser.Term.letI] def elabLetI : TermElab := fun stx expectedType? => do
  match stx with
  | `(letI $x:ident $bs* : $ty := $val; $body) =>
    withExpectedType expectedType? fun expectedType => do
      let (ty, val) ← elabBinders bs fun bs => do
        let ty ← elabType ty
        let val ← elabTermEnsuringType val ty
        pure (← mkForallFVars bs ty, ← mkLambdaFVars bs val)
      withLetDecl x.getId ty val fun x => do
        return (← (← elabTerm body expectedType).abstractM #[x]).instantiate #[val]
  | _ => throwUnsupportedSyntax

end Lean.Elab.Term
