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

class LawfulZipOperator (α : Type) [Hashable α] [DecidableEq α]
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f] : Prop
  where
  chainable : ∀ (aig : AIG α) (input1 input2 : BinaryInput aig) (h) (assign),
                ⟦f (f aig input1).aig (input2.cast h), assign⟧
                  =
                ⟦f aig input2, assign⟧

namespace LawfulZipOperator

theorem denote_prefix_cast_ref {aig : AIG α} {input1 input2 : BinaryInput aig}
    {f : (aig : AIG α) → BinaryInput aig → Entrypoint α} [LawfulOperator α BinaryInput f]
    [LawfulZipOperator α f] {h} :
    ⟦f (f aig input1).aig (input2.cast h), assign⟧
      =
    ⟦f aig input2, assign⟧ := by
  rw [LawfulZipOperator.chainable]

instance : LawfulZipOperator α mkAndCached where
  chainable := by
    intros
    simp only [BinaryInput.cast, Ref.cast_eq, denote_mkAndCached]
    rw [LawfulOperator.denote_mem_prefix (f := mkAndCached)]
    rw [LawfulOperator.denote_mem_prefix (f := mkAndCached)]

instance : LawfulZipOperator α mkOrCached where
  chainable := by
    intros
    simp only [BinaryInput.cast, Ref.cast_eq, denote_mkOrCached]
    rw [LawfulOperator.denote_mem_prefix (f := mkOrCached)]
    rw [LawfulOperator.denote_mem_prefix (f := mkOrCached)]

instance : LawfulZipOperator α mkXorCached where
  chainable := by
    intros
    simp only [BinaryInput.cast, Ref.cast_eq, denote_mkXorCached]
    rw [LawfulOperator.denote_mem_prefix (f := mkXorCached)]
    rw [LawfulOperator.denote_mem_prefix (f := mkXorCached)]

instance : LawfulZipOperator α mkBEqCached where
  chainable := by
    intros
    simp only [BinaryInput.cast, Ref.cast_eq, denote_mkBEqCached]
    rw [LawfulOperator.denote_mem_prefix (f := mkBEqCached)]
    rw [LawfulOperator.denote_mem_prefix (f := mkBEqCached)]

instance : LawfulZipOperator α mkImpCached where
  chainable := by
    intros
    simp only [BinaryInput.cast, Ref.cast_eq, denote_mkImpCached]
    rw [LawfulOperator.denote_mem_prefix (f := mkImpCached)]
    rw [LawfulOperator.denote_mem_prefix (f := mkImpCached)]

end LawfulZipOperator

structure ZipTarget (aig : AIG α) (len : Nat) where
  input : BinaryRefVec aig len
  func : (aig : AIG α) → BinaryInput aig → Entrypoint α
  [lawful : LawfulOperator α BinaryInput func]
  [chainable : LawfulZipOperator α func]

attribute [instance] ZipTarget.lawful
attribute [instance] ZipTarget.chainable

@[specialize]
def zip (aig : AIG α) (target : ZipTarget aig len) : RefVecEntry α len :=
  go aig 0 .empty (by omega) target.input.lhs target.input.rhs target.func
where
  @[specialize]
  go (aig : AIG α) (idx : Nat) (s : RefVec aig idx) (hidx : idx ≤ len)
      (lhs rhs : RefVec aig len) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
      [LawfulOperator α BinaryInput f] [LawfulZipOperator α f] :
      RefVecEntry α len :=
    if hidx : idx < len then
      let res := f aig ⟨lhs.get idx hidx, rhs.get idx hidx⟩
      let aig := res.aig
      let newRef := res.ref
      have := by
        intros
        apply LawfulOperator.le_size_of_le_aig_size
        omega
      let s := s.cast this
      let s := s.push newRef
      go aig (idx + 1) s (by omega) (lhs.cast this) (rhs.cast this) f
    else
      have : idx = len := by omega
      ⟨aig, this ▸ s⟩
  termination_by len - idx

theorem zip.go_le_size {aig : AIG α} (idx : Nat) (hidx) (s : RefVec aig idx)
    (lhs rhs : RefVec aig len)
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
    [chainable : LawfulZipOperator α f] :
    aig.decls.size ≤ (go aig idx s hidx lhs rhs f).1.decls.size := by
  unfold go
  split
  · dsimp only
    refine Nat.le_trans ?_ (by apply zip.go_le_size)
    apply LawfulOperator.le_size
  · simp
  termination_by len - idx

theorem zip_le_size {aig : AIG α} (target : ZipTarget aig len) :
    aig.decls.size ≤ (zip aig target).1.decls.size := by
  unfold zip
  apply zip.go_le_size

theorem zip.go_decl_eq {aig : AIG α} (i) (hi) (lhs rhs : RefVec aig len)
    (s : RefVec aig i) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
    [LawfulOperator α BinaryInput f] [chainable : LawfulZipOperator α f] :
    ∀ (idx : Nat) (h1) (h2), (go aig i s hi lhs rhs f).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig i s hi lhs rhs f = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    rw [← hgo]
    intros
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

theorem zip_decl_eq {aig : AIG α} (target : ZipTarget aig len) :
    ∀ idx (h1 : idx < aig.decls.size) (h2),
      (zip aig target).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros
  unfold zip
  apply zip.go_decl_eq

instance : LawfulVecOperator α ZipTarget zip where
  le_size := by intros; apply zip_le_size
  decl_eq := by intros; apply zip_decl_eq

namespace zip

theorem go_get_aux {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefVec aig curr)
    (lhs rhs : RefVec aig len) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
    [LawfulOperator α BinaryInput f] [chainable : LawfulZipOperator α f] :
    -- The hfoo here is a trick to make the dependent type gods happy
    ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
      (go aig curr s hcurr lhs rhs f).vec.get idx (by omega)
        =
      (s.get idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig curr s hcurr lhs rhs f = res
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
    simp
termination_by len - curr

theorem go_get {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefVec aig curr)
    (lhs rhs : RefVec aig len) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
    [LawfulOperator α BinaryInput f] [chainable : LawfulZipOperator α f] :
    ∀ (idx : Nat) (hidx : idx < curr),
      (go aig curr s hcurr lhs rhs f).vec.get idx (by omega)
        =
      (s.get idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_get_aux

theorem go_denote_mem_prefix {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len)
    (s : RefVec aig curr) (lhs rhs : RefVec aig len)
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
    [chainable : LawfulZipOperator α f] (start : Nat) (hstart) :
    ⟦
      (go aig curr s hcurr lhs rhs f).aig,
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

attribute [local simp] LawfulZipOperator.denote_prefix_cast_ref in
theorem denote_go {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefVec aig curr)
    (lhs rhs : RefVec aig len) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
    [LawfulOperator α BinaryInput f] [chainable : LawfulZipOperator α f] :
    ∀ (idx : Nat) (hidx1 : idx < len),
      curr ≤ idx
        →
      ⟦
        (go aig curr s hcurr lhs rhs f).aig,
        (go aig curr s hcurr lhs rhs f).vec.get idx hidx1,
        assign
      ⟧
        =
      ⟦f aig ⟨lhs.get idx hidx1, rhs.get idx hidx1⟩, assign⟧ := by
  intro idx hidx1 hidx2
  generalize hgo : go aig curr s hcurr lhs rhs f = res
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
      · simp [-Ref.cast_eq]
      · omega
  · omega
termination_by len - curr

end zip

@[simp]
theorem denote_zip {aig : AIG α} (target : ZipTarget aig len) :
    ∀ (idx : Nat) (hidx : idx < len),
      ⟦(zip aig target).aig, (zip aig target).vec.get idx hidx, assign⟧
        =
      ⟦target.func aig ⟨target.input.lhs.get idx hidx, target.input.rhs.get idx hidx⟩, assign⟧ := by
  intros
  apply zip.denote_go
  omega

end RefVec
end AIG

end Sat
end Std
