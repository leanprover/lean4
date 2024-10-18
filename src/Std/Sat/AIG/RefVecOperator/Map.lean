/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.RefVec
import Std.Sat.AIG.LawfulVecOperator

namespace Std
namespace Sat

namespace AIG
namespace RefVec

variable {α : Type} [Hashable α] [DecidableEq α] {aig : AIG α}

class LawfulMapOperator (α : Type) [Hashable α] [DecidableEq α]
    (f : (aig : AIG α) → Ref aig → Entrypoint α) [LawfulOperator α Ref f] : Prop
  where
  chainable : ∀ (aig : AIG α) (input1 input2 : Ref aig) (h) (assign),
                ⟦f (f aig input1).aig (input2.cast h), assign⟧
                  =
                ⟦f aig input2, assign⟧

namespace LawfulMapOperator

theorem denote_prefix_cast_ref {aig : AIG α} {input1 input2 : Ref aig}
    {f : (aig : AIG α) → Ref aig → Entrypoint α} [LawfulOperator α Ref f] [LawfulMapOperator α f]
    {h} :
    ⟦f (f aig input1).aig (input2.cast h), assign⟧
      =
    ⟦f aig input2, assign⟧ := by
  rw [LawfulMapOperator.chainable]

instance : LawfulMapOperator α mkNotCached where
  chainable := by
    intros
    simp only [Ref.gate_cast, denote_mkNotCached]
    rw [LawfulOperator.denote_mem_prefix (f := mkNotCached)]

end LawfulMapOperator

structure MapTarget (aig : AIG α) (len : Nat) where
  vec : RefVec aig len
  func : (aig : AIG α) → Ref aig → Entrypoint α
  [lawful : LawfulOperator α Ref func]
  [chainable : LawfulMapOperator α func]

attribute [instance] MapTarget.lawful
attribute [instance] MapTarget.chainable

@[specialize]
def map (aig : AIG α) (target : MapTarget aig len) : RefVecEntry α len :=
  go aig 0 (by omega) .empty target.vec target.func
where
  @[specialize]
  go {len : Nat} (aig : AIG α) (idx : Nat) (hidx : idx ≤ len) (s : RefVec aig idx)
      (input : RefVec aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
      [LawfulOperator α Ref f] [LawfulMapOperator α f] :
      RefVecEntry α len :=
    if hidx : idx < len then
      let res := f aig (input.get idx hidx)
      let aig := res.aig
      let newRef := res.ref
      have := by
        intros
        apply LawfulOperator.le_size_of_le_aig_size
        omega
      let input := input.cast this
      let s := s.cast this
      let s := s.push newRef
      go aig (idx + 1) (by omega) s input f
    else
      have : idx = len := by omega
      ⟨aig, this ▸ s⟩
  termination_by len - idx

theorem map.go_le_size {aig : AIG α} (idx : Nat) (hidx) (s : RefVec aig idx)
    (input : RefVec aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f] [LawfulMapOperator α f] :
    aig.decls.size ≤ (go aig idx hidx s input f).aig.decls.size := by
  unfold go
  split
  · next h =>
    dsimp only
    refine Nat.le_trans ?_ (by apply map.go_le_size)
    apply LawfulOperator.le_size
  · simp
  termination_by len - idx

theorem map_le_size {aig : AIG α} (target : MapTarget aig len) :
    aig.decls.size ≤ (map aig target).aig.decls.size := by
  unfold map
  apply map.go_le_size

theorem map.go_decl_eq {aig : AIG α} (i) (hi)
    (s : RefVec aig i) (input : RefVec aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f] [LawfulMapOperator α f] :
    ∀ (idx : Nat) (h1) (h2), (go aig i hi s input f).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig i hi s input f = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    rw [← hgo]
    intros
    rw [go_decl_eq]
    rw [LawfulOperator.decl_eq]
    apply LawfulOperator.lt_size_of_lt_aig_size
    assumption
  · dsimp only at hgo
    rw [← hgo]
    intros
    simp
termination_by len - i

theorem map_decl_eq {aig : AIG α} (target : MapTarget aig len) :
    ∀ idx (h1 : idx < aig.decls.size) (h2),
      (map aig target).1.decls[idx]'h2
        =
      aig.decls[idx]'h1 := by
  intros
  unfold map
  apply map.go_decl_eq

instance : LawfulVecOperator α MapTarget map where
  le_size := by intros; apply map_le_size
  decl_eq := by intros; apply map_decl_eq

namespace map

theorem go_get_aux {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefVec aig curr)
    (input : RefVec aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f] [LawfulMapOperator α f] :
    -- The hfoo here is a trick to make the dependent type gods happy.
    ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
      (go aig curr hcurr s input f).vec.get idx (by omega)
        =
      (s.get idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig curr hcurr s input f = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    rw [← hgo]
    intro hfoo
    rw [go_get_aux]
    rw [AIG.RefVec.get_push_ref_lt]
    · simp only [Ref.cast, Ref.mk.injEq]
      rw [AIG.RefVec.get_cast]
      · simp
      · assumption
    · apply go_le_size
  · dsimp only at hgo
    rw [← hgo]
    simp only [Nat.le_refl, get, Ref.cast_eq, Ref.mk.injEq, true_implies]
    have : curr = len := by omega
    subst this
    rfl
termination_by len - curr

theorem go_get {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefVec aig curr)
    (input : RefVec aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f] [LawfulMapOperator α f] :
    ∀ (idx : Nat) (hidx : idx < curr),
      (go aig curr hcurr s input f).vec.get idx (by omega)
        =
      (s.get idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_get_aux

theorem go_denote_mem_prefix {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len)
    (s : RefVec aig curr) (input : RefVec aig len)
    (f : (aig : AIG α) → Ref aig → Entrypoint α) [LawfulOperator α Ref f] [LawfulMapOperator α f]
    (start : Nat) (hstart) :
    ⟦
      (go aig curr hcurr s input f).aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply go_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start,hstart⟩)
  apply IsPrefix.of
  · intros
    apply go_decl_eq
  · intros
    apply go_le_size

attribute [local simp] LawfulMapOperator.denote_prefix_cast_ref in
theorem denote_go {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefVec aig curr)
    (input : RefVec aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f] [LawfulMapOperator α f] :
    ∀ (idx : Nat) (hidx1 : idx < len),
      curr ≤ idx
        →
      ⟦(go aig curr hcurr s input f).aig, (go aig curr hcurr s input f).vec.get idx hidx1, assign⟧
        =
      ⟦f aig (input.get idx hidx1), assign⟧ := by
  intro idx hidx1 hidx2
  generalize hgo : go aig curr hcurr s input f = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      rw [← hgo]
      rw [go_get]
      rw [AIG.RefVec.get_push_ref_eq']
      · simp only [← heq]
        rw [go_denote_mem_prefix]
        · simp
        · simp [Ref.hgate]
      · rw [heq]
    | inr hlt =>
      rw [← hgo]
      rw [denote_go]
      · simp [get_cast, -Ref.cast_eq]
      · omega
  · omega
termination_by len - curr

end map

@[simp]
theorem denote_map {aig : AIG α} (target : MapTarget aig len) :
    ∀ (idx : Nat) (hidx : idx < len),
      ⟦(map aig target).aig, (map aig target).vec.get idx hidx, assign⟧
        =
      ⟦target.func aig (target.vec.get idx hidx), assign⟧ := by
  intro idx hidx
  unfold map
  apply map.denote_go
  omega

end RefVec
end AIG

end Sat
end Std
