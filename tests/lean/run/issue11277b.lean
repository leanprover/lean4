
prelude

import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Var

set_option Elab.async false
set_option warn.sorry false

@[expose] public section

/-!
This module contains the implementation of a bitblaster for `BitVec` expressions (`BVExpr`).
That is, expressions that evaluate to `BitVec` again. Its used as a building block in bitblasting
general `BitVec` problems with boolean substructure.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr

structure Cache.Key where
  w : Nat
  expr : BVExpr w
  deriving DecidableEq

instance : Hashable Cache.Key where
  -- The width is already mixed into the hash of `key.expr` which is completely cached.
  hash key := hash key.expr

structure Cache (aig : AIG BVBit) where
  map : Std.DHashMap Cache.Key (fun k => Vector AIG.Fanin k.w)
  hbound : ∀ k (h1 : k ∈ map), ∀ (h2 : i < k.1), (map.get k h1)[i].gate < aig.decls.size

@[inline]
def Cache.empty : Cache aig :=
  ⟨{}, by simp⟩

@[inline]
def Cache.insert (cache : Cache aig) (expr : BVExpr w) (refs : AIG.RefVec aig w) :
    Cache aig :=
  let ⟨map, hbound⟩ := cache
  have := by
    intro i k hk h2
    rw [Std.DHashMap.get_insert]
    split
    next heq =>
      rcases k with ⟨w, expr⟩
      simp only [beq_iff_eq, Key.mk.injEq] at heq
      rcases heq with ⟨heq1, heq2⟩
      symm at heq1
      subst heq1
      have := refs.hrefs h2
      rw [getElem_congr_coll]
      · exact this
      · simp
    · apply hbound
  ⟨map.insert ⟨w, expr⟩ refs.refs, this⟩

@[inline]
def Cache.get? (cache : Cache aig) (expr : BVExpr w) : Option (AIG.RefVec aig w) :=
  match h : cache.map.get? ⟨w, expr⟩ with
  | some refs =>
    have : ⟨w, expr⟩ ∈ cache.map := by
      rw [Std.DHashMap.mem_iff_contains, Std.DHashMap.contains_eq_isSome_get?]
      simp [h]
    have : cache.map.get ⟨w, expr⟩ this = refs := by
      rw [Std.DHashMap.get?_eq_some_get (h := this)] at h
      simpa using h
    have := by
      intro i hi
      rw [← this]
      apply cache.hbound
    some ⟨refs, this⟩
  | none => none

@[inline]
def Cache.cast (cache : Cache aig1) (h : aig1.decls.size ≤ aig2.decls.size) :
    Cache aig2 :=
  let ⟨map, hbound⟩ := cache
  have := by
    intro i k hk h2
    apply Nat.lt_of_lt_of_le
    · apply hbound
    · exact h
  ⟨map, this⟩

structure WithCache (α : Type u) (aig : AIG BVBit) where
  val : α
  cache : Cache aig

structure Return (aig : AIG BVBit) (w : Nat) where
  result : AIG.ExtendingRefVecEntry aig w
  cache : Cache result.val.aig

set_option maxHeartbeats 400000 in
def bitblast (aig : AIG BVBit) (input : WithCache (BVExpr w) aig) : Return aig w :=
  let ⟨expr, cache⟩ := input
  goCache aig expr cache
where
  goCache {w : Nat} (aig : AIG BVBit) (expr : BVExpr w) (cache : Cache aig) : Return aig w :=
    match cache.get? expr with
    | some vec =>
      ⟨⟨⟨aig, vec⟩, Nat.le_refl ..⟩, cache⟩
    | none =>
      let ⟨result, cache⟩ := go aig expr cache
      ⟨result, cache.insert expr result.val.vec⟩
  termination_by (sizeOf expr, 1)

  go {w : Nat} (aig : AIG BVBit) (expr : BVExpr w) (cache : Cache aig) : Return aig w :=
    match expr with
    -- | x@(.var a) =>
    | (.var a) =>
      let res := bitblast.blastVar aig ⟨a⟩
      have := AIG.LawfulVecOperator.le_size (f := bitblast.blastVar) ..
      let cache := cache.cast this
      ⟨⟨res, this⟩, cache⟩
    | .const val => sorry
    | .bin lhsExpr op rhsExpr =>
      let ⟨⟨⟨aig, lhs⟩, hlaig⟩, cache⟩ := goCache aig lhsExpr cache
      let ⟨⟨⟨aig, rhs⟩, hraig⟩, cache⟩ := goCache aig rhsExpr cache
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      match op with
      | .and => sorry
      | .or => sorry
      | .xor => sorry
      | .add =>
        let res := sorry
        have := by sorry
        ⟨⟨res, this⟩, cache.cast sorry⟩
      | .mul => sorry
      | .udiv => sorry
      | .umod => sorry
    | .un op expr =>
      let ⟨⟨⟨eaig, evec⟩, heaig⟩, cache⟩ := goCache aig expr cache
      match op with
      | .not => sorry
      | .rotateLeft distance => sorry
      | .rotateRight distance => sorry
      | .arithShiftRightConst distance => sorry
      | .reverse => sorry
      | .clz => sorry
    | .append lhs rhs h => sorry
    | .replicate n expr h => sorry
    | .extract start len expr => sorry
    | .shiftLeft lhs rhs => sorry
    | .shiftRight lhs rhs => sorry
    | .arithShiftRight lhs rhs => sorry
  termination_by (sizeOf expr, 0)


namespace bitblast

mutual

theorem goCache_decl_eq (aig : AIG BVBit) (expr : BVExpr w) (cache : Cache aig) :
    ∀ (idx : Nat) (h1) (h2), (goCache aig expr cache).result.val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  sorry

theorem go_decl_eq (aig : AIG BVBit) (expr : BVExpr w) (cache : Cache aig) :
    ∀ (idx : Nat) (h1) (h2), (go aig expr cache).result.val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  sorry

end

end bitblast

theorem bitblast_decl_eq (aig : AIG BVBit) (input : WithCache (BVExpr w) aig) :
    ∀ (idx : Nat) (h1) (h2), (bitblast aig input).result.val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  sorry

theorem bitblast_le_size (aig : AIG BVBit) (input : WithCache (BVExpr w) aig) :
    aig.decls.size ≤ (bitblast aig input).result.val.aig.decls.size := by
  sorry

theorem bitblast_lt_size_of_lt_aig_size (aig : AIG BVBit) (input : WithCache (BVExpr w) aig)
    (h : x < aig.decls.size) :
    x < (bitblast aig input).result.val.aig.decls.size := by
  sorry

end BVExpr

end Std.Tactic.BVDecide


/-!
This module contains the verification of the `BitVec` expressions (`BVExpr`) bitblaster from
`Impl.Expr`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr

namespace Cache

abbrev Inv (assign : Assignment) (aig : AIG BVBit) (cache : Cache aig) : Prop :=
  ∀ k (h1 : k ∈ cache.map), ∀ (i : Nat) (h2 : i < k.w),
    ⟦aig, ⟨(cache.map.get k h1)[i].gate, (cache.map.get k h1)[i].invert, cache.hbound ..⟩, assign.toAIGAssignment⟧
      =
    (k.expr.eval assign).getLsbD i

theorem Inv_cast (cache : Cache aig1) (hpref : IsPrefix aig1.decls aig2.decls)
    (hinv : Inv assign aig1 cache):
    Inv assign aig2 (cache.cast hpref.size_le) := by sorry

theorem Inv_insert (cache : Cache aig) (expr : BVExpr w) (refs : AIG.RefVec aig w)
    (hinv : Inv assign aig cache)
    (hrefs : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, refs.get idx hidx, assign.toAIGAssignment⟧ = (expr.eval assign).getLsbD idx) :
    Inv assign aig (cache.insert expr refs) := by sorry

end Cache

namespace bitblast

set_option maxHeartbeats 400000

mutual


theorem goCache_Inv_of_Inv (cache : Cache aig) (hinv : Cache.Inv assign aig cache) :
    ∀ (expr : BVExpr w),
        Cache.Inv assign (goCache aig expr cache).result.val.aig (goCache aig expr cache).cache := by
  intro expr
  generalize hres : goCache aig expr cache = res
  unfold goCache at hres
  split at hres
  · rw [← hres]
    exact hinv
  · rw [← hres]
    dsimp only
    apply Cache.Inv_insert
    · apply go_Inv_of_Inv
      exact hinv
    · sorry
termination_by expr => (sizeOf expr, 1, sizeOf aig)

theorem go_Inv_of_Inv (cache : Cache aig) (hinv : Cache.Inv assign aig cache) :
    ∀ (expr : BVExpr w),
        Cache.Inv assign (go aig expr cache).result.val.aig (go aig expr cache).cache := by
  intro expr
  generalize hres : go aig expr cache = res
  unfold go at hres
  split at hres
  · sorry
  · sorry
  next op lhsExpr rhsExpr =>
    dsimp only at hres
    match op with
    | .add =>
      dsimp only at hres
      rw [← hres]
      apply Cache.Inv_cast
      · sorry
      · apply goCache_Inv_of_Inv
        sorry
    | _ =>
      sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
termination_by expr => (sizeOf expr, 0, 0)

theorem goCache_denote_eq (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment)
    (cache : Cache aig) (hinv : Cache.Inv assign aig cache) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(goCache aig expr cache).result.val.aig, (goCache aig expr cache).result.val.vec.get idx hidx, assign.toAIGAssignment⟧
          =
        (expr.eval assign).getLsbD idx := by
  intro idx hidx
  generalize hres : goCache aig expr cache = res
  unfold goCache at hres
  split at hres
  · sorry
  · sorry


theorem go_denote_eq (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment)
    (cache : Cache aig) (hinv : Cache.Inv assign aig cache) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(go aig expr cache).result.val.aig, (go aig expr cache).result.val.vec.get idx hidx, assign.toAIGAssignment⟧
          =
        (expr.eval assign).getLsbD idx := by
  intro idx hidx
  generalize hres : go aig expr cache = res
  unfold go at hres
  split at hres
  · sorry
  · sorry
  · dsimp only at hres
    split at hres
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

end

end bitblast

end BVExpr

end Std.Tactic.BVDecide

#exit
