/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.Basic
import Std.Sat.AIG.Lemmas

/-!
This module contains functions to construct AIG nodes while making use of the sub-circuit cache
if possible. For performance reasons these functions should usually be preferred over the naive
AIG node creation ones.
-/

namespace Std
namespace Sat

namespace AIG

variable {α : Type} [Hashable α] [DecidableEq α]

/--
A version of `AIG.mkAtom` that uses the subterm cache in `AIG`. This version is meant for
programming, for proving purposes use `AIG.mkAtom` and equality theorems to this one.
-/
def mkAtomCached (aig : AIG α) (n : α) : Entrypoint α :=
  let ⟨decls, cache, hdag, hzero, hconst⟩ := aig
  let decl := .atom n
  match cache.get? decl with
  | some hit =>
    ⟨⟨decls, cache, hdag, hzero, hconst⟩ , hit.idx, false, hit.hbound⟩
  | none =>
    let g := decls.size
    let cache := cache.insert decls decl
    let decls := decls.push decl
    have hdag := by
      intro i lhs rhs h1 h2
      simp only [Array.getElem_push] at h2
      split at h2
      · apply hdag <;> assumption
      · contradiction
    have hzero' := by simp [decls]
    have hconst := by simp [decls, Array.getElem_push, hzero, hconst]
    ⟨⟨decls, cache, hdag, hzero', hconst⟩, ⟨g, false, by simp [g, decls]⟩⟩

/--
A version of `AIG.mkConst` that uses the subterm cache in `AIG`. This version is meant for
programming, for proving purposes use `AIG.mkGate` and equality theorems to this one.
-/
@[inline]
def mkConstCached (aig : AIG α) (val : Bool) : Entrypoint α :=
  ⟨aig, ⟨0, val, aig.hzero⟩⟩

/--
A version of `AIG.mkGate` that uses the subterm cache in `AIG`. This version is meant for
programming, for proving purposes use `AIG.mkGate` and equality theorems to this one.

Beyond caching this function also implements a subset of the optimizations presented in:
-/
def mkGateCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  let lhs := input.lhs.gate
  let rhs := input.rhs.gate
  if lhs < rhs then
    go aig ⟨input.lhs, input.rhs⟩
  else
    go aig ⟨input.rhs, input.lhs⟩
where
  go (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
    let ⟨decls, cache, hdag, hzero, hconst⟩ := aig
    let lhs := input.lhs.gate
    let rhs := input.rhs.gate
    let linv := input.lhs.invert
    let rinv := input.rhs.invert
    have := input.lhs.hgate
    have := input.rhs.hgate
    let decl := .gate (.mk lhs linv) (.mk rhs rinv)
    match cache.get? decl with
    | some hit =>
      ⟨⟨decls, cache, hdag, hzero, hconst⟩, ⟨hit.idx, false, hit.hbound⟩⟩
    | none =>
      /-
      Here we implement the one-level subset of:
      https://fmv.jku.at/papers/BrummayerBiere-MEMICS06.pdf
      TODO: rest of the table
      -/
      let lhsVal := AIG.getConstant ⟨decls, cache, hdag, hzero, hconst⟩ input.lhs
      let rhsVal := AIG.getConstant ⟨decls, cache, hdag, hzero, hconst⟩ input.rhs
      match lhsVal, rhsVal with
      -- Boundedness
      | .some false, _ | _, .some false => mkConstCached ⟨decls, cache, hdag, hzero, hconst⟩ false
      -- Left Neutrality
      | .some true, _ => ⟨⟨decls, cache, hdag, hzero, hconst⟩, ⟨rhs, rinv, by assumption⟩⟩
      -- Right Neutrality
      | _, .some true => ⟨⟨decls, cache, hdag, hzero, hconst⟩, ⟨lhs, linv, by assumption⟩⟩
      -- No constant inputs
      | _, _ =>
        if lhs == rhs then
           -- Idempotency
          if linv == rinv then ⟨⟨decls, cache, hdag, hzero, hconst⟩, ⟨lhs, linv, by assumption⟩⟩
          -- Contradiction
          else mkConstCached ⟨decls, cache, hdag, hzero, hconst⟩ false
        else
          -- Gate couldn't be simplified
          let g := decls.size
          let cache := cache.insert decls decl
          let decls := decls.push decl
          have hdag := by
            intro i lhs rhs h1 h2
            simp only [Array.getElem_push] at h2
            simp_all
            split at h2
            · apply hdag <;> assumption
            · injection h2 with hl hr
              simp [← hl, ← hr]
              omega
          have hzero' := by simp [decls]
          have hconst := by simp [decls, Array.getElem_push, hzero, hconst]
          ⟨⟨decls, cache, hdag, hzero', hconst⟩, ⟨g, false, by simp [g, decls]⟩⟩

end AIG

end Sat
end Std
