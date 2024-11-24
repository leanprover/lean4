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
  let ⟨decls, cache, inv⟩ := aig
  let decl := .atom n
  match cache.get? decl with
  | some hit =>
    ⟨⟨decls, cache, inv⟩ , hit.idx, hit.hbound⟩
  | none =>
    let g := decls.size
    let cache := cache.insert decls decl
    let decls := decls.push decl
    have inv := by
      intro i lhs rhs linv rinv h1 h2
      simp only [Array.getElem_push] at h2
      split at h2
      · apply inv <;> assumption
      · contradiction
  ⟨⟨decls, cache, inv⟩, ⟨g, by simp [g, decls]⟩⟩

/--
A version of `AIG.mkConst` that uses the subterm cache in `AIG`. This version is meant for
programming, for proving purposes use `AIG.mkGate` and equality theorems to this one.
-/
def mkConstCached (aig : AIG α) (val : Bool) : Entrypoint α :=
  let ⟨decls, cache, inv⟩ := aig
  let decl := .const val
  match cache.get? decl with
  | some hit =>
    ⟨⟨decls, cache, inv⟩, hit.idx, hit.hbound⟩
  | none =>
    let g := decls.size
    let cache := cache.insert decls decl
    let decls := decls.push decl
    have inv := by
      intro i lhs rhs linv rinv h1 h2
      simp only [Array.getElem_push] at h2
      split at h2
      · apply inv <;> assumption
      · contradiction
  ⟨⟨decls, cache, inv⟩, ⟨g, by simp [g, decls]⟩⟩

/--
A version of `AIG.mkGate` that uses the subterm cache in `AIG`. This version is meant for
programming, for proving purposes use `AIG.mkGate` and equality theorems to this one.

Beyond caching this function also implements a subset of the optimizations presented in:
-/
def mkGateCached (aig : AIG α) (input : GateInput aig) : Entrypoint α :=
  let lhs := input.lhs.ref.gate
  let rhs := input.rhs.ref.gate
  if lhs < rhs then
    go aig ⟨input.lhs, input.rhs⟩
  else
    go aig ⟨input.rhs, input.lhs⟩
where
  go (aig : AIG α) (input : GateInput aig) : Entrypoint α :=
    let ⟨decls, cache, inv⟩ := aig
    let lhs := input.lhs.ref.gate
    let rhs := input.rhs.ref.gate
    let linv := input.lhs.inv
    let rinv := input.rhs.inv
    have := input.lhs.ref.hgate
    have := input.rhs.ref.hgate
    let decl := .gate lhs rhs linv rinv
    match cache.get? decl with
    | some hit =>
      ⟨⟨decls, cache, inv⟩, ⟨hit.idx, hit.hbound⟩⟩
    | none =>
      /-
      Here we implement the constant propagating subset of:
      https://fmv.jku.at/papers/BrummayerBiere-MEMICS06.pdf
      TODO: rest of the table
      -/
      match decls[lhs], decls[rhs], linv, rinv with
      -- Boundedness
      | .const true, _, true, _ | .const false, _, false, _
      | _, .const true, _, true | _, .const false, _, false =>
        mkConstCached ⟨decls, cache, inv⟩ false
      -- Left Neutrality
      | .const true, _, false, false | .const false, _, true, false =>
        ⟨⟨decls, cache, inv⟩, rhs, (by assumption)⟩
      -- Right Neutrality
      | _, .const true, false, false | _, .const false, false, true =>
        ⟨⟨decls, cache, inv⟩, lhs, (by assumption)⟩
      | _, _, _, _ =>
        if lhs == rhs && linv == false && rinv == false then
          -- Idempotency rule
         ⟨⟨decls, cache, inv⟩, lhs, (by assumption)⟩
        else if lhs == rhs && linv == !rinv then
          -- Contradiction rule
          mkConstCached ⟨decls, cache, inv⟩ false
        else
          let g := decls.size
          let cache := cache.insert decls decl
          let decls := decls.push decl
          have inv := by
            intro i lhs rhs linv rinv h1 h2
            simp only [decls] at *
            simp only [Array.getElem_push] at h2
            split at h2
            · apply inv <;> assumption
            · injections; omega
          ⟨⟨decls, cache, inv⟩, ⟨g, by simp [g, decls]⟩⟩

end AIG

end Sat
end Std
