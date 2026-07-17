/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Meta.Sym.Apply
public import Std.Internal.Do.Order.Heyting
public import Lean.Elab.Tactic.Do.Internal.VCGen.FrameProc
import Lean.Meta.AppBuilder
import Lean.Meta.AbstractMVars

open Lean Meta Sym
open Lean.Order

namespace Lean.Elab.Tactic.Do.Internal

namespace VCGen

/-! ## Lattice split rules

Backward rules that decompose a lattice operator on the RHS of an entailment `pre ⊑ op … s⃗`. The
operator is saturated with distribution and unfolding rewrites, a terminal `⊑`-introduction rule
fires on the reduced form, and any state arguments the terminal leaves over-applied are point-framed
onto the precondition.

A frame operator contributes its own rewrites and terminals through its `@[frameproc]`; the built-in
seeds cover the lattice connectives `⊓`/`⇨`/`⌜·⌝`/`⊤` and the magic-wand residual `upperAdjoint`.
-/

/-- The lattice meet `⊓`: distributes via `meet_apply`, closes with `le_meet`. -/
public def LatticeOp.meet : LatticeOp :=
  { head := ``meet, rewrites := #[``meet_apply], terminal? := ``le_meet }
/-- Heyting implication `⇨`: distributes via `himp_apply`, closes with `le_himp`. -/
public def LatticeOp.himp : LatticeOp :=
  { head := ``Lean.Order.himp, rewrites := #[``himp_apply], terminal? := ``Lean.Order.le_himp }
/-- The pure assertion `⌜·⌝`: distributes via `ofProp_apply`, closes with the `⊤`-fixed
`top_le_ofProp`. -/
public def LatticeOp.ofProp : LatticeOp :=
  { head := ``Lean.Order.CompleteLattice.ofProp,
    rewrites := #[``Lean.Order.CompleteLattice.ofProp_apply], terminal? := ``Lean.Order.top_le_ofProp }
/-- The lattice top `⊤`: distributes via `top_apply`, closes with `le_top`. -/
public def LatticeOp.top : LatticeOp :=
  { head := ``Lean.Order.top, rewrites := #[``Lean.Order.top_apply], terminal? := ``le_top }
/-- The magic-wand residual `upperAdjoint f b`: point-framed, closes with `le_upperAdjoint`. -/
public def LatticeOp.upperAdjoint : LatticeOp :=
  { head := ``Lean.Order.PreservesSup.upperAdjoint,
    terminal? := ``Lean.Order.PreservesSup.le_upperAdjoint }

/-- The built-in connective splits, whose rewrites and terminals seed every saturation. -/
public def builtinLatticeOps : Array LatticeOp :=
  #[.meet, .himp, .ofProp, .top, .upperAdjoint]

/-- The lattice-split table keyed by operator head, merging the built-in connectives with the
registered frame operators' splits. -/
public def mkLatticeOpTable (frameSplits : Std.HashMap Name LatticeOp) :
    Std.HashMap Name LatticeOp :=
  builtinLatticeOps.foldl (fun t s => t.insert s.head s) frameSplits

/-- Index terminal lemmas by the head constant of their conclusion's RHS, recording the RHS argument
count so a split can size the excess state arguments to point-frame. -/
private def mkLatticeTerminals (names : Array Name) : MetaM (Std.HashMap Name (Name × Nat)) := do
  let mut m : Std.HashMap Name (Name × Nat) := {}
  for n in names do
    let ty ← Meta.inferType (← mkConstWithFreshMVarLevels n)
    let (_, _, concl) ← forallMetaTelescopeReducing ty
    let some (_, _, _, rhs) := (← instantiateMVars concl).app4? ``PartialOrder.rel
      | throwError "lattice terminal {n} does not conclude a `⊑` relation"
    let some h := rhs.getAppFn.constName?
      | throwError "lattice terminal {n} has no head constant on its conclusion right-hand side"
    m := m.insert h (n, rhs.getAppNumArgs)
  return m

/--
Saturate `e` by rewriting at the root with the first applicable equation from `rewrites`, handling
over-application, until none applies. Returns the reduced expression and, when a rewrite fired, a proof
`e = reduced`. Unification (`isDefEq`) drives the match, so schematic operands are supported. `fuel`
bounds the rewrite chain, turning a non-terminating `@[frameproc]` rewrite set into an error.
-/
private partial def saturateLatticeOp (rewrites : Array Name) (e : Expr) (fuel : Nat := 256) :
    MetaM (Expr × Option Expr) := do
  if fuel == 0 then
    throwError "lattice saturation did not terminate; a registered `@[frameproc]` rewrite set is \
      likely non-terminating on{indentExpr e}"
  for n in rewrites do
    let saved ← saveState
    let lemConst ← mkConstWithFreshMVarLevels n
    let (mvars, _, eqTy) ← forallMetaTelescopeReducing (← Meta.inferType lemConst)
    if let some (_, lhs, rhs) := (← instantiateMVars eqTy).eq? then
      let m := lhs.getAppNumArgs
      if m ≤ e.getAppNumArgs then
        let eArgs := e.getAppArgs
        let ePrefix := mkAppN e.getAppFn (eArgs.extract 0 m)
        let extra := eArgs.extract m eArgs.size
        if ← isDefEq lhs ePrefix then
          -- Lift the equation `lhs = rhs` across the over-application `extra` with iterated `congrFun`.
          let stepProof ← extra.foldlM (fun h a => mkCongrFun h a) (mkAppN lemConst mvars)
          let (reduced, rest?) ← saturateLatticeOp rewrites (mkAppN rhs extra) (fuel - 1)
          let proof ← match rest? with
            | none => pure stepProof
            | some restProof => mkEqTrans stepProof restProof
          return (reduced, some proof)
    saved.restore
  return (e, none)

/--
Point-frame the state chain `ss` of a goal `pre ⊑ opAs s₁ … sₙ`: peel the innermost argument via
`le_apply_of_point_meet_le`, gating the precondition to `fun u => ⌜u = sₙ⌝ ⊓ pre`, until the goal is
the function-level `gate ⊑ opAs`, then apply the terminal `introThm`, leaving its operand subgoals as
premises. An empty `ss` applies `introThm` directly. Returns the proof of `pre ⊑ opAs s₁ … sₙ`.
-/
private partial def mkPointFrameApply (introThm : Name) (opAs pre : Expr) (ss : List Expr) :
    MetaM Expr := do
  match ss with
  | [] =>
    let introRule ← mkConstWithFreshMVarLevels introThm
    let (xs, _, body) ← forallMetaTelescope (← Meta.inferType introRule)
    let target ← mkAppM ``PartialOrder.rel #[pre, opAs]
    unless ← isDefEq body target do
      throwError "lattice terminal {introThm} does not conclude {target}"
    return mkAppN introRule xs
  | _ =>
    let s := ss.getLast!
    let init := ss.dropLast
    let Q := mkAppN opAs init.toArray
    let preTy ← Meta.inferType pre
    let gate ← withLocalDeclD `u (← Meta.inferType s) fun u => do
      let ofp ← mkAppOptM ``Lean.Order.CompleteLattice.ofProp #[preTy, none, ← mkEq u s]
      mkLambdaFVars #[u] (← mkAppM ``Lean.Order.meet #[ofp, pre])
    let h ← mkPointFrameApply introThm opAs gate init
    mkAppM ``Lean.Order.le_apply_of_point_meet_le #[s, pre, Q, h]

/--
Build a reusable backward rule decomposing `pre ⊑ op … s⃗` for a lattice operator. The operator's
value arguments are made schematic; `rewrites` saturate the operator through its distribution and
unfolding equalities, the terminal keyed by the reduced head fires, and any state arguments left
over-applied by the terminal are point-framed onto the precondition. When the reduced head has no
registered terminal, the saturated `pre ⊑ reduced` is handed back as the sole subgoal. Throws when the
operator neither reduces nor has a terminal, since its rule would be the identity.

For `⊓`, produces `∀ a b s⃗ pre, pre ⊑ a s⃗ → pre ⊑ b s⃗ → pre ⊑ (a ⊓ b) s⃗`. For the opaque residual
`upperAdjoint f b`, produces `∀ f b s⃗ pre, f (fun u⃗ => ⌜u⃗ = s⃗⌝ ⊓ pre) ⊑ b → pre ⊑ upperAdjoint f b s⃗`.
-/
public def mkLatticeOpRule (rhs : Expr) (op : LatticeOp) : MetaM BackwardRule := do
  -- Merge the operator's own rewrites and terminal with the built-in connective seeds: saturation can
  -- reduce to any built-in connective, so its rewrites and terminals are always in scope. On a head
  -- clash the operator's own contribution wins: its rewrite is tried first, its terminal inserted last.
  let rewrites := builtinLatticeOps.foldl (· ++ ·.rewrites) op.rewrites
  let terminals ← mkLatticeTerminals
    (builtinLatticeOps.foldl (fun ts s => ts ++ s.terminal?.toArray) #[] ++ op.terminal?.toArray)
  rhs.withApp fun head args => do
    -- Hold the operator's `numConst` leading arguments (its carrier type and typeclass instances)
    -- concrete; make the operands and excess state arguments after them schematic, so the rule serves
    -- every operand and state chain of this shape.
    let vars ← (args.extract op.numConst).mapM fun a => do mkFreshExprMVar (← Meta.inferType a)
    let rhs' := mkAppN head (args.extract 0 op.numConst ++ vars)
    -- Saturate the operator and prove `pre ⊑ reduced`: fire the terminal keyed by the reduced head,
    -- or hand back the residual entailment as the subgoal when the head has none. An irreducible
    -- operator with no terminal would make that residual the original goal, so no rule is produced.
    let (reduced, eqProof?) ← saturateLatticeOp rewrites rhs'
    let pre ← mkFreshExprMVar (← Meta.inferType rhs')
    let redHead := reduced.getAppFn.constName?.getD .anonymous
    let termProof? ← terminals[redHead]?.mapM fun (termLemma, rhsArgCount) => do
      let args := reduced.getAppArgs
      mkPointFrameApply termLemma (mkAppN reduced.getAppFn (args.extract 0 rhsArgCount)) pre
        (args.extract rhsArgCount).toList
    let prf ←
      match (termProof?, eqProof?) with
      | (none, none) =>
        throwError "frame operator `{op.head}` neither reduces nor has a registered terminal; its \
          lattice split rule would be the identity"
      | (some termProof, none) => pure termProof
      | (_, some eqProof) =>
        -- Lift the saturation equality `rhs' = reduced` through `pre ⊑ ·`, turning the terminal proof of
        -- `pre ⊑ reduced` into a proof of `pre ⊑ rhs'`.
        let termProof ← termProof?.getDM (mkFreshExprMVar (← mkAppM ``PartialOrder.rel #[pre, reduced]))
        let relPre ← mkAppM ``PartialOrder.rel #[pre]
        let eqMp ← mkAppM ``Eq.mp #[← mkEqSymm (← mkCongrArg relPre eqProof)]
        pure (mkApp eqMp termProof)
    let res ← abstractMVars prf
    mkBackwardRuleFromExpr res.expr res.paramNames.toList


end VCGen
end Lean.Elab.Tactic.Do.Internal
