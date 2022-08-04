/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Init.Data.ToString
import Lean.Compiler.BorrowedAnnotation
import Lean.Meta.KAbstract
import Lean.Meta.Transform
import Lean.Elab.App
import Lean.Elab.SyntheticMVars

namespace Lean.Elab.Term
open Meta

@[builtinTermElab coeNotation] def elabCoe : TermElab := fun stx expectedType? => do
  let stx := stx[1]
  tryPostponeIfNoneOrMVar expectedType?
  let e ← elabTerm stx none
  let type ← inferType e
  match expectedType? with
  | some expectedType =>
    if (← isDefEq expectedType type) then
      return e
    else
      mkCoe expectedType type e
  | _ => throwError "invalid coercion notation, expected type is not known"

/--
The *anonymous constructor* `⟨e, ...⟩` is equivalent to `c e ...` if the
expected type is an inductive type with a single constructor `c`.
If more terms are given than `c` has parameters, the remaining arguments
are turned into a new anonymous constructor application. For example,
`⟨a, b, c⟩ : α × (β × γ)` is equivalent to `⟨a, ⟨b, c⟩⟩`. -/
@[builtinTermElab anonymousCtor] def elabAnonymousCtor : TermElab := fun stx expectedType? =>
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
            let cinfo ← getConstInfoCtor ctor
            let numExplicitFields ← forallTelescopeReducing cinfo.type fun xs _ => do
              let mut n := 0
              for i in [cinfo.numParams:xs.size] do
                if (← getFVarLocalDecl xs[i]!).binderInfo.isExplicit then
                  n := n + 1
              return n
            let args := args.getElems
            if args.size < numExplicitFields then
              throwError "invalid constructor ⟨...⟩, insufficient number of arguments, constructs '{ctor}' has #{numExplicitFields} explicit fields, but only #{args.size} provided"
            let newStx ← if args.size == numExplicitFields then
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
  | `(show $type from $val)  => let thisId := mkIdentFrom stx `this; `(let_fun $thisId : $type := $val; $thisId)
  | `(show $type by%$b $tac) => `(show $type from by%$b $tac)
  | _                        => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.have] def expandHave : Macro := fun stx =>
  let thisId := mkIdentFrom stx `this
  match stx with
  | `(have $x $bs* $[: $type]? := $val; $body)            => `(let_fun $x $bs* $[: $type]? := $val; $body)
  | `(have $[: $type]? := $val; $body)                    => `(have $thisId $[: $type]? := $val; $body)
  | `(have $x $bs* $[: $type]? $alts; $body)              => `(let_fun $x $bs* $[: $type]? $alts; $body)
  | `(have $[: $type]? $alts:matchAlts; $body)            => `(have $thisId $[: $type]? $alts:matchAlts; $body)
  | `(have $pattern:term $[: $type]? := $val:term; $body) => `(let_fun $pattern:term $[: $type]? := $val:term ; $body)
  | _                                                     => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.suffices] def expandSuffices : Macro
  | `(suffices $[$x :]? $type from $val; $body)            => `(have $[$x]? : $type := $body; $val)
  | `(suffices $[$x :]? $type by%$b $tac:tacticSeq; $body) => `(have $[$x]? : $type := $body; by%$b $tac)
  | _                                                           => Macro.throwUnsupported

open Lean.Parser in
private def elabParserMacroAux (prec e : Term) (withAnonymousAntiquot : Bool) : TermElabM Syntax := do
  let (some declName) ← getDeclName?
    | throwError "invalid `leading_parser` macro, it must be used in definitions"
  match extractMacroScopes declName with
  | { name := .str _ s, .. } =>
    let kind := quote declName
    let s    := quote s
    ``(withAntiquot (mkAntiquot $s $kind $(quote withAnonymousAntiquot)) (leadingNode $kind $prec $e))
  | _  => throwError "invalid `leading_parser` macro, unexpected declaration name"

@[builtinTermElab «leading_parser»] def elabLeadingParserMacro : TermElab :=
  adaptExpander fun stx => match stx with
  | `(leading_parser $[: $prec?]? $[(withAnonymousAntiquot := $anon?)]? $e) =>
    elabParserMacroAux (prec?.getD (quote Parser.maxPrec)) e (anon?.all (·.raw.isOfKind ``Parser.Term.trueVal))
  | _ => throwUnsupportedSyntax

private def elabTParserMacroAux (prec lhsPrec e : Term) : TermElabM Syntax := do
  let declName? ← getDeclName?
  match declName? with
  | some declName => let kind := quote declName; ``(Lean.Parser.trailingNode $kind $prec $lhsPrec $e)
  | none          => throwError "invalid `trailing_parser` macro, it must be used in definitions"

@[builtinTermElab «trailing_parser»] def elabTrailingParserMacro : TermElab :=
  adaptExpander fun stx => match stx with
  | `(trailing_parser$[:$prec?]?$[:$lhsPrec?]? $e) =>
    elabTParserMacroAux (prec?.getD <| quote Parser.maxPrec) (lhsPrec?.getD <| quote 0) e
  | _ => throwUnsupportedSyntax

/--
`panic! msg` formally evaluates to `@Inhabited.default α` if the expected type
`α` implements `Inhabited`.
At runtime, `msg` and the file position are printed to stderr unless the C
function `lean_set_panic_messages(false)` has been executed before. If the C
function `lean_set_exit_on_panic(true)` has been executed before, the process is
then aborted. -/
@[builtinTermElab Lean.Parser.Term.panic] def elabPanic : TermElab := fun stx expectedType? => do
  match stx with
  | `(panic! $arg) =>
    let pos ← getRefPosition
    let env ← getEnv
    let stxNew ← match (← getDeclName?) with
    | some declName => `(panicWithPosWithDecl $(quote (toString env.mainModule)) $(quote (toString declName)) $(quote pos.line) $(quote pos.column) $arg)
    | none => `(panicWithPos $(quote (toString env.mainModule)) $(quote pos.line) $(quote pos.column) $arg)
    withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
  | _ => throwUnsupportedSyntax

/-- A shorthand for `panic! "unreachable code has been reached"`. -/
@[builtinMacro Lean.Parser.Term.unreachable]  def expandUnreachable : Macro := fun _ =>
  `(panic! "unreachable code has been reached")

/-- `assert! cond` panics if `cond` evaluates to `false`. -/
@[builtinMacro Lean.Parser.Term.assert]  def expandAssert : Macro
  | `(assert! $cond; $body) =>
    -- TODO: support for disabling runtime assertions
    match cond.raw.reprint with
    | some code => `(if $cond then $body else panic! ("assertion violation: " ++ $(quote code)))
    | none => `(if $cond then $body else panic! ("assertion violation"))
  | _ => Macro.throwUnsupported

/--
`dbg_trace e; body` evaluates to `body` and prints `e` (which can be an
interpolated string literal) to stderr. It should only be used for debugging. -/
@[builtinMacro Lean.Parser.Term.dbgTrace]  def expandDbgTrace : Macro
  | `(dbg_trace $arg:interpolatedStr; $body) => `(dbgTrace (s! $arg) fun _ => $body)
  | `(dbg_trace $arg:term; $body)            => `(dbgTrace (toString $arg) fun _ => $body)
  | _                                        => Macro.throwUnsupported

/-- A temporary placeholder for a missing proof or value. -/
@[builtinTermElab «sorry»] def elabSorry : TermElab := fun stx expectedType? => do
  let stxNew ← `(sorryAx _ false)
  withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?

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
  loop (elems.size - 1) elems.back

private partial def hasCDot : Syntax → Bool
  | Syntax.node _ k args =>
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
partial def expandCDot? (stx : Term) : MacroM (Option Term) := do
  if hasCDot stx then
    let (newStx, binders) ← (go stx).run #[]
    `(fun $binders* => $(⟨newStx⟩))
  else
    pure none
where
  /--
    Auxiliary function for expanding the `·` notation.
    The extra state `Array Syntax` contains the new binder names.
    If `stx` is a `·`, we create a fresh identifier, store in the
    extra state, and return it. Otherwise, we just return `stx`. -/
  go : Syntax → StateT (Array Ident) MacroM Syntax
    | stx@`(($(_))) => pure stx
    | `(·) => withFreshMacroScope do
      let id : Ident ← `(a)
      modify fun s => s.push id
      pure id
    | stx => match stx with
      | .node i k args => do
        let args ← args.mapM go
        pure $ Syntax.node i k args
      | _ => pure stx

/--
  Helper method for elaborating terms such as `(.+.)` where a constant name is expected.
  This method is usually used to implement tactics that function names as arguments (e.g., `simp`).
-/
def elabCDotFunctionAlias? (stx : Term) : TermElabM (Option Expr) := do
  let some stx ← liftMacroM <| expandCDotArg? stx | pure none
  let stx ← liftMacroM <| expandMacros stx
  match stx with
  | `(fun $binders* => $f $args*) =>
    if binders == args then
      try Term.resolveId? f catch _ => return none
    else
      return none
  | `(fun $binders* => binop% $f $a $b) =>
    if binders == #[a, b] then
      try Term.resolveId? f catch _ => return none
    else
      return none
  | _ => return none
where
  expandCDotArg? (stx : Term) : MacroM (Option Term) :=
    match stx with
    | `(($e)) => Term.expandCDot? e
    | _ => Term.expandCDot? stx


/--
You can use parentheses for
- Grouping expressions, e.g., `a * (b + c)`.
- Creating tuples, e.g., `(a, b, c)` is notation for `Prod.mk a (Prod.mk b c)`.
- Performing type ascription, e.g., `(0 : Int)` instructs Lean to process `0` as a value of type `Int`.
- Creating `Unit.unit`, `()` is just a shorthand for `Unit.unit`.
- Creating simple functions when combined with `·`. Here are some examples:
  - `(· + 1)` is shorthand for `fun x => x + 1`
  - `(· + ·)` is shorthand for `fun x y => x + y`
  - `(f · a b)` is shorthand for `fun x => f x a b`
  - `(h (· + 1) ·)` is shorthand for `fun x => h (fun y => y + 1) x`
-/
@[builtinMacro Lean.Parser.Term.paren] def expandParen : Macro
  | `(())           => `(Unit.unit)
  | `(($e : $type)) => do
    match (← expandCDot? e) with
    | some e => `(($e : $type))
    | none   => Macro.throwUnsupported
  | `(($e))         => return (← expandCDot? e).getD e
  | `(($e, $es,*))  => do
    let pairs ← mkPairs (#[e] ++ es)
    return (← expandCDot? pairs).getD pairs
  | stx =>
    if !stx[1][0].isMissing && stx[1][1].isMissing then
      -- parsed `(` and `term`, assume it's a basic parenthesis to get any elaboration output at all
      `(($(⟨stx[1][0]⟩)))
    else
      throw <| Macro.Exception.error stx "unexpected parentheses notation"

@[builtinTermElab paren] def elabParen : TermElab := fun stx _ => do
  match stx with
  | `(($e : $type)) =>
    let type ← withSynthesize (mayPostpone := true) <| elabType type
    let e ← elabTerm e type
    ensureHasType type e
  | _ => throwUnsupportedSyntax

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

/--
`h ▸ e` is a macro built on top of `Eq.rec` and `Eq.symm` definitions.
Given `h : a = b` and `e : p a`, the term `h ▸ e` has type `p b`.
You can also view `h ▸ e` as a "type casting" operation where you change the type of `e` by using `h`.
See the Chapter "Quantifiers and Equality" in the manual "Theorem Proving in Lean" for additional information.
-/
@[builtinTermElab subst] def elabSubst : TermElab := fun stx expectedType? => do
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
           -- Before failing try tos use `subst`
           if ← (isSubstCandidate lhs rhs <||> isSubstCandidate rhs lhs) then
             withLocalIdentFor heqStx heq fun heqStx =>
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
         let hTypeAbst ← kabstract hType lhs
         let motive ← mkMotive lhs hTypeAbst
         unless (← isTypeCorrect motive) do
           throwError "invalid `▸` notation, failed to compute motive for the substitution"
         mkEqRec motive h heq
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
