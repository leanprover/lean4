/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.BuiltinDo.Basic
meta import Lean.Parser.Do
import Init.Control.Do
import Init.While
import Lean.Meta.ProdN

public section

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta

@[builtin_macro Lean.Parser.Term.doFor] def expandDoFor : Macro := fun stx => do
  match stx with
  | `(doFor| for $[$_ : ]? $_:ident in $_ $[$_inv:doForInvariant]? do $_) =>
    -- This is the target form of the expander, handled by `elabDoFor` below.
    Macro.throwUnsupported
  | `(doFor| for%$tk $decls:doForDecl,* $[$inv:doForInvariant]? do $body) =>
    if let some inv := inv then
      Macro.throwErrorAt inv "The `invariant` clause is only supported on `for x in xs do …` \
        with a single identifier binder."
    let decls := decls.getElems
    let `(doForDecl| $[$h? : ]? $pattern in $xs) := decls[0]! | Macro.throwUnsupported
    let mut doElems := #[]
    let mut body := body
    -- Expand `pattern` into an `Ident` `x`:
    let x ←
      if pattern.raw.isIdent then
        pure ⟨pattern⟩
      else if pattern.raw.isOfKind ``Lean.Parser.Term.hole then
        Term.mkFreshIdent pattern
      else
        -- This case is a last resort, because it introduces a `match` and that will cause eager
        -- defaulting. In practice this means that `mut` vars default to `Nat` too often.
        -- Hence we try to only generate a `match` if we absolutely must.
        let x ← Term.mkFreshIdent pattern
        body ← `(doSeq| match $x:term with | $pattern => $body)
        pure x
    -- Expand the remaining `doForDecl`s:
    for doForDecl in decls[1...*] do
      /-
        Expand
        ```
        for x in xs, y in ys do
          body
        ```
        into
        ```
        let mut s := Std.toStream ys
        for x in xs do
          match Std.Stream.next? s with
          | none => break
          | some (y, s') =>
            s := s'
            body
        ```
      -/
      let `(doForDecl| $[$h? : ]? $y in $ys) := doForDecl | Macro.throwUnsupported
      if let some h := h? then
        Macro.throwErrorAt h "The proof annotation here has not been implemented yet."
      /- Recall that `@` (explicit) disables `coeAtOutParam`.
         We used `@` at `Stream` functions to make sure `resultIsOutParamSupport` is not used. -/
      let toStreamApp ← withRef ys `(@Std.toStream _ _ _ $ys)
      let s := mkIdentFrom ys (← withFreshMacroScope <| MonadQuotation.addMacroScope `__s)
      doElems := doElems.push (← `(doSeqItem| let mut $s := $toStreamApp:term))
      body ← `(doSeq|
        match @Std.Stream.next? _ _ _ $s with
          | none => break
          | some ($y, s') =>
            $s:ident := s'
            do $body)
    doElems := doElems.push (← `(doSeqItem| for%$tk $[$h? : ]? $x:ident in $xs do $body))
    `(doElem| do $doElems*)
  | _ => Macro.throwUnsupported

/-- The already-elaborated pieces of a loop, handed to the builder of an `invariant` clause's
`vcgen` gadget. -/
structure LoopGadgetArgs where
  /-- The collection being iterated. -/
  xs : Expr
  /-- The initial state tuple. -/
  init : Expr
  /-- The loop body, a function from the element and the state tuple to a `ForInStep`. -/
  body : Expr
  /-- The type of the state tuple. -/
  σ : Expr
  /-- The mutable variables carried through the loop, in state-tuple order. -/
  loopMutVars : Array MutVar
  /-- Whether the state tuple carries an early-return slot. -/
  returnsEarly : Bool
  /-- The monad of the surrounding `do` block. -/
  mi : MonadInfo

/-- The pattern matching the loop's state tuple. Its layout is `[return?, mutVars…, unit?]`, so an
annotation can name the loop's mutable variables directly; the early-return slot and the filler
become wildcards. -/
private def LoopGadgetArgs.statePat (args : LoopGadgetArgs) : DoElabM Term := do
  let hole ← `(_)
  let mut binders : Array Term := #[]
  if args.returnsEarly then binders := binders.push hole
  for mv in args.loopMutVars do binders := binders.push ⟨mv.ident.raw⟩
  if args.returnsEarly && args.loopMutVars.isEmpty then binders := binders.push hole
  match binders with
  | #[]  => `(_)
  | #[b] => pure b
  | _    => `(⟨$binders,*⟩)

/-- Abstract `e` over the loop's state tuple, so that `e` may refer to the loop's mutable variables
by name. -/
private def LoopGadgetArgs.mkStateFun (args : LoopGadgetArgs) (ref : Syntax) (e : Term) :
    DoElabM Term := do
  let statePat ← args.statePat
  let stateId := mkIdentFrom ref (← mkFreshUserName `__s)
  `(fun $stateId:ident => match $stateId:ident with | $statePat => $e)

/-- Check that the `vcgen` gadget `gadget` is available in the user's context, which requires the
metatheory to be imported. -/
private def checkGadget (ref : Syntax) (gadget : Name) : DoElabM Unit := do
  unless (← getEnv).contains gadget do
    throwErrorAt ref
      "the `invariant` clause elaborates to a `vcgen` gadget; add `import Std.Internal.Do` to use it."

/-- Rebuild the already-elaborated loop as a `forInWithInvariant` call carrying the `invariant`
clause: `ForIn.forInWithInvariant`, or `ForIn'.forInWithInvariant'` for a membership-proof binder
(`for h : x in xs`). -/
private def mkForInWithInvariant (invClause : Syntax) (h? : Option Syntax)
    (args : LoopGadgetArgs) : DoElabM Expr := do
  let `(doForInvariant| invariant $cursorBinders* => $invBody) := invClause | throwUnsupportedSyntax
  let statePat ← args.statePat
  let stateId := mkIdentFrom invClause (← mkFreshUserName `__s)
  let invLam ← `(fun $cursorBinders* $stateId:ident =>
    match $stateId:ident with | $statePat => $invBody)
  -- The `forInWithInvariant` gadgets live downstream of this module, so they are referenced by an
  -- unresolved name that resolves in the user's context (which imports the metatheory).
  let gadget := if h?.isSome then `Std.Internal.Do.ForIn'.forInWithInvariant'
    else `Std.Internal.Do.ForIn.forInWithInvariant
  checkGadget invClause gadget
  let call ← `($(mkIdent gadget) $(← Term.exprToSyntax args.xs) $(← Term.exprToSyntax args.init)
    $(← Term.exprToSyntax args.body) $invLam)
  Term.elabTermEnsuringType call (mkApp args.mi.m args.σ)

/-- Rebuild the already-elaborated `while` loop as a `Loop.forInWithInvariant` call carrying the
`invariant` clause's invariant and measure together with the negated loop condition `guard`. -/
def mkWhileWithInvariant (invClause : Syntax) (guard : Term) (args : LoopGadgetArgs) :
    DoElabM Expr := do
  let `(doWhileInvariant| invariant $invBody $[$dec?:doWhileDecreasing]?) := invClause
    | throwUnsupportedSyntax
  let some dec := dec?
    | throwErrorAt invClause "A `while` loop's `invariant` clause needs a termination measure. \
        Append `decreasing e`, where `e : Nat` strictly decreases on every iteration."
  let `(doWhileDecreasing| decreasing $measureBody) := dec | throwUnsupportedSyntax
  let invLam ← args.mkStateFun invClause invBody
  let measureLam ← args.mkStateFun dec measureBody
  let exitLam ← args.mkStateFun guard (← `(¬ $guard))
  let gadget := `Std.Internal.Do.Loop.forInWithInvariant
  checkGadget invClause gadget
  let call ← `($(mkIdent gadget) $(← Term.exprToSyntax args.xs) $(← Term.exprToSyntax args.init)
    $(← Term.exprToSyntax args.body) $measureLam $invLam $exitLam)
  Term.elabTermEnsuringType call (mkApp args.mi.m args.σ)

/-- Elaborate a `ForIn` loop over `xs` binding `x` (and optionally the membership proof `h?`) with
body `body`. When `mkGadget?` is given, the elaborated loop is rebuilt as the `vcgen` gadget it
returns instead of a plain `ForIn.forIn` application. `while` loops elaborate through here as a loop
over `Loop.mk`. -/
def elabForLoop (tk : Syntax) (h? : Option Ident) (x : Ident) (xs : Term) (body : DoSeq)
    (mkGadget? : Option (LoopGadgetArgs → DoElabM Expr)) (dec : DoElemCont) : DoElabM Expr := do
  let dec ← dec.ensureUnitAt tk
  checkMutVarsForShadowing #[x]
  let uα ← mkFreshLevelMVar
  let uρ ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort (uα.succ)) (userName := `α) -- assigned by outParam
  let ρ ← mkFreshExprMVar (mkSort (uρ.succ)) (userName := `ρ) -- assigned in the next line
  let xs ← Term.elabTermEnsuringType xs ρ
  let mi := (← read).monadInfo
  let mutVars := (← read).mutVars

  let info ← inferControlInfoSeq body
  let oldReturnCont ← getReturnCont
  let returnVarName ← mkFreshUserName `__r
  let loopMutVars := mutVars.filter fun x => info.reassigns.contains x.getId
  let loopMutVarNames :=
    if info.returnsEarly then
      returnVarName :: (loopMutVars.map (·.getId)).toList
    else
      (loopMutVars.map (·.getId)).toList
  let useLoopMutVars (e : Option Expr) : TermElabM (Array Expr) := do
    let mut defs := #[]
    unless e.isNone || info.returnsEarly do
      throwError "Early returning {e} but the info said there is no early return"
    if info.returnsEarly then
      let returnVar ←
        match e with
        | none => mkNone oldReturnCont.resultType
        | some e => mkSome oldReturnCont.resultType e
      defs := defs.push returnVar
    for x in loopMutVars do
      let defn ← getLocalDeclFromUserName x.getId
      Term.addTermInfo' x.ident defn.toExpr
      -- ForIn forces the mut tuple into the universe mi.u: that of the do block result type.
      -- If we don't do this, then we are stuck on solving constraints such as
      --   `max ?u.46 ?u.47 =?= max (max ?u.22 ?u.46) ?u.47`
      -- It's important we do this as a separate isLevelDefEq check on the decremented level because
      -- otherwise (`ensureHasType (mkSort mi.u.succ)`) we are stuck on constraints like
      --   `max (?u+1) (?v+1) =?= ?u+1`
      let u ← getDecLevel defn.type
      discard <| isLevelDefEq u mi.u
      defs := defs.push defn.toExpr
    if info.returnsEarly && loopMutVars.isEmpty then
      defs := defs.push (mkConst ``Unit.unit)
    return defs

  let (preS, σ) ← mkProdMkN (← useLoopMutVars none) mi.u

  let (app, p?) ← match h? with
    | none =>
      let instForIn ← Term.mkInstMVar <| mkApp3 (mkConst ``ForIn [uρ, uα, mi.u, mi.v]) mi.m ρ α
      let app := mkConst ``ForIn.forIn [uρ, uα, mi.u, mi.v]
      -- ForIn.forIn : {m ρ α : _} → [ForIn m ρ α] → {β : _} → ρ → β → (α → β → m (ForInStep β)) → m β
      let app := mkApp7 app mi.m ρ α instForIn σ xs preS -- 1 arg remaining: loop body
      pure (app, none)
    | some _ =>
      let d ← mkFreshExprMVar (mkApp2 (mkConst ``Membership [uα, uρ]) α ρ) (userName := `d) -- outParam
      let instForIn ← Term.mkInstMVar <| mkApp4 (mkConst ``ForIn' [uρ, uα, mi.u, mi.v]) mi.m ρ α d
      let app := mkConst ``ForIn'.forIn' [uρ, uα, mi.u, mi.v]
      -- ForIn'.forIn' : {m ρ α : _} → [Membership α ρ] → [ForIn' m ρ α d] → {β : _} → ρ → β → ((a : α) → a ∈ x → β → m (ForInStep β)) → m β
      let app := mkApp8 app mi.m ρ α d instForIn σ xs preS -- 1 arg remaining: loop body
      pure (app, some d)
  let s ← mkFreshUserName `__s
  let xh : Array (Name × (Array Expr → DoElabM Expr)) := match h?, p? with
    | some h, some d =>
      #[(x.getId, fun _ => pure α),
        (h.getId, fun x => pure (mkApp5 (mkConst ``Membership.mem [uα, uρ]) α ρ d xs x[0]!))]
    | _, _ =>
      #[(x.getId, fun _ => pure α)]

  let body ←
    withLocalDeclsD xh fun xh => do
    Term.addLocalVarInfo x xh[0]!
    if let some h := h? then
      Term.addLocalVarInfo h xh[1]!
    withLocalDecl s .default σ (kind := .implDetail) fun loopS => do
    mkLambdaFVars (xh.push loopS) <| ← do
    bindMutVarsFromTuple loopMutVarNames loopS.fvarId! do
    let newDoBlockResultType := mkApp (mkConst ``ForInStep [mi.u]) σ
    withDoBlockResultType newDoBlockResultType do
    let continueCont := do
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars none) mi.u
      let yield := mkApp2 (mkConst ``ForInStep.yield [mi.u]) σ tuple
      mkPureApp newDoBlockResultType yield
    let breakCont := do
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars none) mi.u
      let done := mkApp2 (mkConst ``ForInStep.done [mi.u]) σ tuple
      mkPureApp newDoBlockResultType done
    let returnCont := { oldReturnCont with k := fun e => do
        let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars (some e)) mi.u
        let done := mkApp2 (mkConst ``ForInStep.done [mi.u]) σ tuple
        mkPureApp newDoBlockResultType done
      }
    enterLoopBody breakCont continueCont returnCont do
    -- Elaborate the loop body, which must have result type `PUnit`, just like the whole `for` loop.
    elabDoSeq body { dec with k := continueCont, kind := .duplicable }

  let forIn ← match mkGadget? with
    | none => pure (mkApp app body)
    | some mkGadget =>
      mkGadget { xs, init := preS, body, σ, loopMutVars, returnsEarly := info.returnsEarly, mi }

  let γ := (← read).doBlockResultType
  let rest ←
    withLocalDeclD s σ fun postS => do mkLambdaFVars #[postS] <| ← do
      bindMutVarsFromTuple loopMutVarNames postS.fvarId! do
        if info.returnsEarly then
          let ret ← getFVarFromUserName returnVarName
          let ret ← if loopMutVars.isEmpty then mkAppM ``Prod.fst #[ret] else pure ret
          let motive := mkLambda `_ .default (← inferType ret) (← mkMonadApp γ)
          let app := mkApp3 (mkConst ``Break.runK.match_1 [mi.u, mi.v.succ]) oldReturnCont.resultType motive ret
          let none := mkSimpleThunk (← dec.continueWithUnit)
          let some ← withLocalDeclD (← mkFreshUserName `r) oldReturnCont.resultType fun r => do
            mkLambdaFVars #[r] (← oldReturnCont.k r)
          return mkApp2 app some none
        else
          dec.continueWithUnit

  mkBindApp σ γ forIn rest

@[builtin_doElem_elab Lean.Parser.Term.doFor] def elabDoFor : DoElab := fun stx dec => do
  let `(doFor| for%$tk $[$h? : ]? $x:ident in $xs $[$inv?:doForInvariant]? do $body) := stx
    | throwUnsupportedSyntax
  let mkGadget? := inv?.map fun invClause args => mkForInWithInvariant invClause h? args
  elabForLoop tk h? x xs body mkGadget? dec
