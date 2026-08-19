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
    let decls := decls.getElems
    if let some inv := inv then
      if decls.size > 1 then
        Macro.throwErrorAt inv "The `invariant` clause takes a `for` loop over a single collection."
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
    doElems := doElems.push
      (← `(doSeqItem| for%$tk $[$h? : ]? $x:ident in $xs $[$inv:doForInvariant]? do $body))
    `(doElem| do $doElems*)
  | _ => Macro.throwUnsupported

/-- Demand the class that the `invariant` clause's specification is stated over, so that the
container that lacks it is reported at the clause. -/
private def checkPureForIn (invClause : Syntax) (h? : Option Syntax) (xs α : Expr) (mi : MonadInfo) :
    DoElabM Unit := withRef invClause do
  let cls := if h?.isSome then `Std.Internal.PureForIn' else `Std.Internal.PureForIn
  unless (← getEnv).contains cls do return
  let ty ← Term.elabType <| ←
    `($(mkIdent cls) $(← Term.exprToSyntax mi.m) $(← Term.exprToSyntax (← inferType xs))
      $(← Term.exprToSyntax α))
  discard <| Term.mkInstMVar ty
    (extraErrorMsg? := m!"The `invariant` clause is stated over this class, which says that \
      iterating the container produces its elements without effects.")

/-- Rebuild the already-elaborated loop as a `forInWithInvariant` call carrying the `invariant`
clause: `ForIn.forInWithInvariant`, or `ForIn'.forInWithInvariant'` for a membership-proof binder
(`for h : x in xs`). The mut tuple's layout is `[return?, mutVars…, unit?]`, so the invariant can
name the loop's mutable variables directly; the early-return slot becomes a wildcard. Binders past
the first two bind the arguments of the assertion itself. -/
private def mkForInWithInvariant (invClause : Syntax) (h? : Option Syntax)
    (xs α preS body σ : Expr) (loopMutVars : Array MutVar) (returnsEarly : Bool)
    (mi : MonadInfo) : DoElabM Expr := do
  if let `(doForInvariant| invariant $_* : $ty => $_) := invClause then
    throwErrorAt ty "The `invariant` clause takes no type ascription covering all its binders; \
      ascribe the type on an individual binder, as in `invariant (pref : List α) suff => ...`."
  let `(doForInvariant| invariant $binders* => $invBody) := invClause | throwUnsupportedSyntax
  checkPureForIn invClause h? xs α mi
  unless binders.size ≥ 2 do
    throwErrorAt invClause "The `invariant` clause takes at least two binders: the elements \
      consumed so far and the elements remaining."
  let loopBinders := binders.take 2
  let assertionBinders := binders.extract 2
  let invBody ← if assertionBinders.isEmpty then pure invBody else
    `(fun $assertionBinders* => $invBody)
  let hole ← `(_)
  let mut mutBinders : Array Term := #[]
  if returnsEarly then mutBinders := mutBinders.push hole
  for mv in loopMutVars do mutBinders := mutBinders.push ⟨mv.ident.raw⟩
  if returnsEarly && loopMutVars.isEmpty then mutBinders := mutBinders.push hole
  let mutTuplePat : Term ← match mutBinders with
    | #[]  => `(_)
    | #[b] => pure b
    | _    => `(⟨$mutBinders,*⟩)
  let mutTupleBinder := mkIdentFrom invClause (← mkFreshUserName `__s)
  let invLam ← `(fun $loopBinders* $mutTupleBinder:ident =>
    match $mutTupleBinder:ident with | $mutTuplePat => $invBody)
  -- The `forInWithInvariant` gadgets live downstream of this module, so they are referenced by an
  -- unresolved name that resolves in the user's context (which imports the metatheory).
  let gadget := if h?.isSome then `Std.Internal.Do.ForIn'.forInWithInvariant'
    else `Std.Internal.Do.ForIn.forInWithInvariant
  unless (← getEnv).contains gadget do
    throwErrorAt invClause
      "the `invariant` clause elaborates to a `vcgen` gadget; add `import Std.Internal.Do` to use it."
  let call ← `($(mkIdent gadget)
    $(← Term.exprToSyntax xs) $(← Term.exprToSyntax preS) $(← Term.exprToSyntax body) $invLam)
  Term.elabTermEnsuringType call (mkApp mi.m σ)

@[builtin_doElem_elab Lean.Parser.Term.doFor] def elabDoFor : DoElab := fun stx dec => do
  let `(doFor| for%$tk $[$h? : ]? $x:ident in $xs $[$inv?:doForInvariant]? do $body) := stx
    | throwUnsupportedSyntax
  if let some invClause := inv? then
    warnIntrinsicExperimental invClause.raw[0] m!"`invariant` clause"
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

  let forIn ← match inv? with
    | none => pure (mkApp app body)
    | some invClause =>
      mkForInWithInvariant invClause h? xs α preS body σ loopMutVars info.returnsEarly mi

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
