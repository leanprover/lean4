/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Normalize.Bool
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic

/-!
This module contains the implementation of the and flattening pass in the fixpoint pipeline, taking
hypotheses of the form `h : x && y = true` and splitting them into `h1 : x = true` and
`h2 : y = true` recursively.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

structure AndFlattenCache where
  cache : Std.HashSet Sym.ExprPtr := {}

abbrev FlattenM := StateRefT AndFlattenCache PreProcessM

@[inline]
def FlattenM.isCached (e : Expr) : FlattenM Bool := return (← get).cache.contains ⟨e⟩

@[inline]
def FlattenM.cache (e : Expr) : FlattenM Unit :=
  modify fun s => { s with cache := s.cache.insert ⟨e⟩ }

structure AndFlattenState where
  hypsToAdd : Array Hyp := #[]

/--
Flatten out ands. That is look for hypotheses of the form `h : (x && y) = true` and replace them
with `h.left : x = true` and `h.right : y = true`. This can enable more fine grained substitutions
in embedded constraint substitution.
-/
public partial def andFlatteningPass : Pass where
  name := `andFlattening
  run' := do
    discard <| process (← PreProcessM.getTargetMVarId) |>.run {}
    return false
where
  process (g : MVarId) : FlattenM Unit :=
    g.withContext do
      PreProcessM.flatMapHyps fun hyp => do
        let (_, newHyps) ← (processHyp hyp).run {}
        return newHyps.hypsToAdd

  processHyp (hyp : Hyp) : StateRefT AndFlattenState FlattenM Unit := do
    if let some (lhs, rhs) ← trySplit hyp then
      splitAnds [lhs, rhs]
    else
      modify fun s => { s with hypsToAdd := #[hyp] }

  splitAnds (worklist : List Hyp) : StateRefT AndFlattenState FlattenM Unit := do
    match worklist with
    | [] => return ()
    | hyp :: worklist =>
      match ← trySplit hyp with
      | some (left, right) => splitAnds <| left :: right :: worklist
      | none =>
        modify (fun s => { s with hypsToAdd := s.hypsToAdd.push hyp })
        splitAnds worklist

  trySplit (hyp : Hyp) :
      StateRefT AndFlattenState FlattenM (Option (Hyp × Hyp)) := do
    let typ := hyp.type
    if ← FlattenM.isCached typ then
      return none
    else
      FlattenM.cache typ
      let_expr Eq _ eqLhs eqRhs := typ | return none
      let_expr Bool.and lhs rhs := eqLhs | return none
      let_expr Bool.true := eqRhs | return none
      let mkEqTrue (lhs : Expr) : Sym.SymM Expr :=
        Sym.share <| mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) lhs (mkConst ``Bool.true)
      let leftHyp : Hyp := {
        name := hyp.name,
        type := ← mkEqTrue lhs,
        value := mkApp3 (mkConst ``Std.Tactic.BVDecide.Normalize.Bool.and_left) lhs rhs hyp.value
        source := .andFlattened hyp.source
      }
      let rightHyp : Hyp := {
        name := hyp.name,
        type := ← mkEqTrue rhs,
        value := mkApp3 (mkConst ``Std.Tactic.BVDecide.Normalize.Bool.and_right) lhs rhs hyp.value
        source := .andFlattened hyp.source
      }
      return some (leftHyp, rightHyp)


end Normalize
end Lean.Meta.Tactic.BVDecide
