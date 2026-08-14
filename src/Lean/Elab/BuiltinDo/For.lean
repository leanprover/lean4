/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.BuiltinDo.Basic
meta import Lean.Parser.Do
meta import Std.WP.Gadget.ForIn
import Init.Control.Do
import Init.Data.Sum.Basic
import Init.While
import Lean.Meta.ProdN

public section

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta

@[builtin_macro Lean.Parser.Term.doFor] def expandDoFor : Macro := fun stx => do
  match stx with
  | `(doFor| for $[$_ : ]? $_:ident in $_ $[$_inv:doLoopInvariant]? $[$_dec:doLoopDecreasing]? do $_) =>
    -- This is the target form of the expander, handled by `elabDoFor` below.
    Macro.throwUnsupported
  | `(doFor| for%$tk $decls:doForDecl,* $[$inv:doLoopInvariant]? $[$dec:doLoopDecreasing]? do $body) =>
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
      (← `(doSeqItem| for%$tk $[$h? : ]? $x:ident in $xs
        $[$inv:doLoopInvariant]? $[$dec:doLoopDecreasing]? do $body))
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

/-- The assertion language of the `do` block's monad, which `WPMonad` computes as an output
parameter: synthesizing `WPMonad StateM Nat _ _` assigns `Nat → Prop` for the assertions of
`StateM Nat`. The result is what the monad's assertions are known to be right here, so a monad
whose instance is not available reports nothing. The type is built from syntax so that the
universes and the instance arguments of the class come from elaboration. -/
private def assertionLanguage? : DoElabM (Option Expr) := do
  unless (← getEnv).contains ``Std.WP.WPMonad do return none
  let wpTy ← Term.elabType <| ←
    `($(mkIdent ``Std.WP.WPMonad) $(← Term.exprToSyntax (← read).monadInfo.m) _ _)
  let .some _ ← trySynthInstance wpTy | return none
  let some pred := wpTy.getAppArgs[1]? | return none
  let pred ← instantiateMVars pred
  return if pred.hasExprMVar then none else some pred

/-- Report a clause that binds more arguments than the loop's assertions take, such as the state of
a state monad. The language's arguments are the arrows before its result. -/
private def checkAssertionBinders (ref : Syntax) (what : String) (binders : Nat)
    (pred? : Option Expr) : DoElabM Unit := do
  if binders == 0 then return
  let some pred := pred? | return
  let arity := pred.getForallArity
  if binders > arity then
    let takes := if arity == 1 then m!"one argument" else m!"{arity} arguments"
    let has := if binders == 1 then m!"one binder" else m!"{binders} binders"
    throwErrorAt ref "The {what} of a loop in this monad takes {takes}, and this clause has \
      {has}. The loop's mutable variables are named without binding them."

/-- Bind the arguments of an assertion, which the clause states after the loop's own binders. -/
private def mkAssertionFun (binders : TSyntaxArray ``Lean.Parser.Term.funBinder) (body : Term) :
    DoElabM Term :=
  if binders.isEmpty then pure body else `(fun $binders* => $body)

/-- The pattern that names the loop's mutable variables in the state tuple, whose layout is
`[return?, mutVars…, unit?]`; the early-return slot becomes a wildcard. -/
private def mkStatePat (loopMutVars : Array MutVar) (returnsEarly : Bool) : DoElabM Term := do
  let hole ← `(_)
  let mut binders : Array Term := #[]
  if returnsEarly then binders := binders.push hole
  for mv in loopMutVars do binders := binders.push ⟨mv.ident.raw⟩
  if returnsEarly && loopMutVars.isEmpty then binders := binders.push hole
  match binders with
    | #[]  => `(_)
    | #[b] => pure b
    | _    => `(⟨$binders,*⟩)

/-- The already-elaborated pieces of a `forIn` application that an annotation's gadget is
built from. -/
structure ForInApp where
  /-- The collection being iterated. -/
  xs : Expr
  /-- The initial state tuple. -/
  init : Expr
  /-- The loop body, a function from the element and the state tuple to a `ForInStep`. -/
  body : Expr
  /-- The type of the state tuple. -/
  σ : Expr
  /-- The pattern naming the loop's mutable variables in the state tuple. -/
  statePat : Term

/-- Abstract `e` over the loop's state tuple, so that `e` may name the loop's mutable variables. -/
private def ForInApp.mkStateFun (g : ForInApp) (e : Term) : DoElabM Term :=
  `(fun $(g.statePat) => $e)

/-- Abstract `e` over the cursor of a `repeat` loop, so that `e` may name the loop's mutable
variables whether the loop is iterating or done. -/
private def ForInApp.mkCursorFun (g : ForInApp) (cursor : Ident) (e : Term) : DoElabM Term :=
  `(fun $cursor:ident => match $cursor:ident with
      | .inl $(g.statePat) | .inr $(g.statePat) => $e)

/-- Elaborate the gadget application that replaces the loop. The gadgets live downstream of this
module, so `gadget` is an unresolved name that resolves in the user's context. -/
private def ForInApp.mkCall (g : ForInApp) (ref : Syntax) (gadget : Name)
    (annotations : Array Term) : DoElabM Expr := do
  unless (← getEnv).contains gadget do
    throwErrorAt ref "a loop annotation elaborates to a `vcgen` gadget; \
      add `import Std.WP` to use it."
  let call ← `($(mkIdent gadget) $(← Term.exprToSyntax g.xs) $(← Term.exprToSyntax g.init)
    $(← Term.exprToSyntax g.body) $annotations*)
  Term.elabTermEnsuringType call (mkApp (← read).monadInfo.m g.σ)

/-- The binders and body of an `invariant` clause. An ascription covering the binder list would
cover the loop's binders and the assertion's alike, so it is reported here. -/
private def destructInvariant (invClause : TSyntax ``doLoopInvariant) :
    DoElabM (TSyntaxArray ``Lean.Parser.Term.funBinder × Term) := do
  if let `(doLoopInvariant| invariant $_* : $ty => $_) := invClause then
    throwErrorAt ty "The `invariant` clause takes no type ascription covering all its binders; \
      ascribe the type on an individual binder, as in `invariant (pref : List α) suff => ...`."
  let `(doLoopInvariant| invariant $binders* => $body) := invClause | throwUnsupportedSyntax
  return (binders, body)

/-- Rebuild the loop over a collection as a `forInPureWithInvariant` call carrying the `invariant`
clause, or `forInPureWithInvariant'` for a membership-proof binder (`for h : x in xs`). The
invariant names the loop's mutable variables directly; its first two binders are the elements
consumed so far and the elements remaining, and binders past them bind the arguments of the
assertion itself. -/
private def mkForInPureWithInvariant (g : ForInApp) (invClause : TSyntax ``doLoopInvariant)
    (h? : Option Ident) (α : Expr) : DoElabM Expr := do
  let (binders, invBody) ← destructInvariant invClause
  checkPureForIn invClause h? g.xs α (← read).monadInfo
  unless binders.size ≥ 2 do
    throwErrorAt invClause "The `invariant` clause takes at least two binders: the elements \
      consumed so far and the elements remaining."
  let loopBinders := binders.take 2
  let assertionBinders := binders.drop 2
  checkAssertionBinders invClause "invariant" assertionBinders.size (← assertionLanguage?)
  let invBody ← mkAssertionFun assertionBinders invBody
  let invLam ← `(fun $loopBinders* => $(← g.mkStateFun invBody))
  let gadget := if h?.isSome then ``Std.WP.Gadget.forInPureWithInvariant'
    else ``Std.WP.Gadget.forInPureWithInvariant
  g.mkCall invClause gadget #[invLam]

/-- Rebuild the loop of a `repeat` as a call to the gadget carrying the annotations the loop states.
Both clauses name the loop's mutable variables directly. The `invariant` clause is a function of the
`Bool` that says whether the loop has left; the cursor's own payload is the state tuple, which the
mutable variables already name. -/
private def mkForInLoopGadget (g : ForInApp)
    (inv? : Option (TSyntax ``doLoopInvariant)) (dec? : Option (TSyntax ``doLoopDecreasing)) :
    DoElabM (Option Expr) := do
  let pred? ← assertionLanguage?
  let invArg? ← inv?.mapM fun invClause => do
    let (binders, invBody) ← destructInvariant invClause
    let exitBinder := binders[0]!
    let assertionBinders := binders.drop 1
    checkAssertionBinders invClause "invariant" assertionBinders.size pred?
    let invBody ← mkAssertionFun assertionBinders invBody
    let cursor := mkIdentFrom invClause (← mkFreshUserName `__c)
    let invBody ← if exitBinder.raw.isOfKind ``hole then pure invBody else
      let exitPat : Term := ⟨exitBinder.raw⟩
      let hasLeft ← `($(mkIdent ``Sum.isRight) $cursor:ident)
      `(match $hasLeft:term with | $exitPat => $invBody)
    -- `RepeatInvariant.mk` keeps the clause's declared type on the term. A bare lambda carries the
    -- unfolded type, and a specification's instance arguments are synthesized before the check that
    -- would unfold it.
    return ((invClause : Syntax), ← `($(mkIdent ``Std.WP.RepeatInvariant.mk)
      $(← g.mkCursorFun cursor invBody)))
  let varArg? ← dec?.mapM fun decClause => do
    let (binders, body) ← match decClause with
      | `(doLoopDecreasing| decreasing $binders* => $body) => pure (binders, body)
      | `(doLoopDecreasing| decreasing $measure:term) => pure (#[], measure)
      | _ => throwUnsupportedSyntax
    checkAssertionBinders decClause "measure" binders.size pred?
    return ((decClause : Syntax), ← g.mkStateFun (← mkAssertionFun binders body))
  let some (ref, gadget, annotations) := (match invArg?, varArg? with
    | some (ref, inv), some (_, var) =>
      some (ref, ``Std.WP.Gadget.forInLoopWithInvariantAndVariant, #[inv, var])
    | some (ref, inv), none => some (ref, ``Std.WP.Gadget.forInLoopWithInvariant, #[inv])
    | none, some (ref, var) => some (ref, ``Std.WP.Gadget.forInLoopWithVariant, #[var])
    | none, none => none) | return none
  some <$> g.mkCall ref gadget annotations

@[builtin_doElem_elab Lean.Parser.Term.doFor] def elabDoFor : DoElab := fun stx dec => do
  let `(doFor| for%$tk $[$h? : ]? $x:ident in $xs
      $[$inv?:doLoopInvariant]? $[$dec?:doLoopDecreasing]? do $body) := stx
    | throwUnsupportedSyntax
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

  -- A loop over `Lean.Loop` is what `repeat` and `while` expand to, and it is the only one whose
  -- termination the program has to state.
  let mut forIn := mkApp app body
  unless inv?.isNone && dec?.isNone do
    let g : ForInApp :=
      { xs, init := preS, body, σ, statePat := ← mkStatePat loopMutVars info.returnsEarly }
    if (← instantiateMVars ρ).isConstOf ``Lean.Loop then
      if let some e ← mkForInLoopGadget g inv? dec? then forIn := e
    else if let some decClause := dec? then
      throwErrorAt decClause "A `for` loop terminates with the collection it iterates; \
        `decreasing` states the termination measure of a `repeat` or `while` loop."
    else if let some invClause := inv? then
      forIn ← mkForInPureWithInvariant g invClause h? α

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
