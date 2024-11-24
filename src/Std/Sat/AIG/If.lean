/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.CachedGatesLemmas
import Std.Sat.AIG.LawfulVecOperator

/-!
Besides introducing a way to construct an if statement in an `AIG`, this module also demonstrates
a style of writing Lean code that minimizes the risk of linearity issues on the `AIG`.

The idea is to always keep one `aig` variable around that contains the `AIG` and continuously
shadow it. However, applying multiple operations to the `AIG` does often require `Ref.cast` to use
other inputs or `Ref`s created by previous operations in later ones. Applying a `Ref.cast` would
usually require keeping around the old `AIG` to state the theorem statement. Luckily in this
situation Lean is usually always able to infer the theorem statement on it's own. For this
reason the style goes as follows:
```
let res := someLawfulOperator aig input
let aig := res.aig
let ref := res.ref
have := LawfulOperator.le_size (f := mkIfCached) ..
let input1 := input1.cast this
let input2 := input2.cast this
-- ...
-- Next `LawfulOperator` application
```
This style also generalizes to applications of `LawfulVecOperator`s.
-/

namespace Std
namespace Sat

namespace AIG

variable {α : Type} [Hashable α] [DecidableEq α]

open AIG

def mkIfCached (aig : AIG α) (input : TernaryInput aig) : Entrypoint α :=
  -- if d then l else r = ((d && l) || (!d && r))
  let res := aig.mkAndCached ⟨input.discr, input.lhs⟩
  let aig := res.aig
  let lhsRef := res.ref
  let input := input.cast <| by apply AIG.LawfulOperator.le_size (f := mkAndCached)
  let res := aig.mkNotCached input.discr
  let aig := res.aig
  let notDiscr := res.ref
  let input := input.cast <| by apply AIG.LawfulOperator.le_size (f := mkNotCached)
  let res := aig.mkAndCached ⟨notDiscr, input.rhs⟩
  let aig := res.aig
  let rhsRef := res.ref
  let lhsRef := lhsRef.cast <| by
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := mkAndCached)
    apply AIG.LawfulOperator.le_size (f := mkNotCached)
  aig.mkOrCached ⟨lhsRef, rhsRef⟩

instance : LawfulOperator α TernaryInput mkIfCached where
  le_size := by
    intros
    unfold mkIfCached
    dsimp only
    apply LawfulOperator.le_size_of_le_aig_size (f := mkOrCached)
    apply LawfulOperator.le_size_of_le_aig_size (f := mkAndCached)
    apply LawfulOperator.le_size_of_le_aig_size (f := mkNotCached)
    apply LawfulOperator.le_size (f := mkAndCached)
  decl_eq := by
    intros
    unfold mkIfCached
    dsimp only
    rw [LawfulOperator.decl_eq (f := mkOrCached)]
    rw [LawfulOperator.decl_eq (f := mkAndCached)]
    rw [LawfulOperator.decl_eq (f := mkNotCached)]
    rw [LawfulOperator.decl_eq (f := mkAndCached)]
    · apply LawfulOperator.lt_size_of_lt_aig_size (f := mkAndCached)
      omega
    · apply LawfulOperator.lt_size_of_lt_aig_size (f := mkNotCached)
      apply LawfulOperator.lt_size_of_lt_aig_size (f := mkAndCached)
      omega
    · apply LawfulOperator.lt_size_of_lt_aig_size (f := mkAndCached)
      apply LawfulOperator.lt_size_of_lt_aig_size (f := mkNotCached)
      apply LawfulOperator.lt_size_of_lt_aig_size (f := mkAndCached)
      omega

theorem if_as_bool (d l r : Bool) : (if d then l else r) = ((d && l) || (!d && r))  := by
  revert d l r
  decide

@[simp]
theorem denote_mkIfCached {aig : AIG α} {input : TernaryInput aig} :
    ⟦aig.mkIfCached input, assign⟧
      =
    if ⟦aig, input.discr, assign⟧ then ⟦aig, input.lhs, assign⟧ else ⟦aig, input.rhs, assign⟧ := by
  rw [if_as_bool]
  unfold mkIfCached
  dsimp only
  simp only [TernaryInput.cast, Ref.cast_eq, id_eq, Int.reduceNeg, denote_mkOrCached,
    denote_projected_entry, denote_mkAndCached, denote_mkNotCached]
  congr 2
  · rw [LawfulOperator.denote_mem_prefix]
    rw [LawfulOperator.denote_mem_prefix]
    · simp
    · simp [Ref.hgate]
  · rw [LawfulOperator.denote_mem_prefix]
  · rw [LawfulOperator.denote_mem_prefix]
    rw [LawfulOperator.denote_mem_prefix]

namespace RefVec

structure IfInput (aig : AIG α) (w : Nat) where
  discr : Ref aig
  lhs : RefVec aig w
  rhs : RefVec aig w

def ite (aig : AIG α) (input : IfInput aig w) : RefVecEntry α w :=
  let ⟨discr, lhs, rhs⟩ := input
  go aig 0 (by omega) discr lhs rhs .empty
where
  go {w : Nat} (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (discr : Ref aig)
      (lhs rhs : RefVec aig w) (s : RefVec aig curr) : RefVecEntry α w :=
    if hcurr : curr < w then
      let input := ⟨discr, lhs.get curr hcurr, rhs.get curr hcurr⟩
      let res := mkIfCached aig input
      let aig := res.aig
      let ref := res.ref
      have := LawfulOperator.le_size (f := mkIfCached) ..
      let discr := discr.cast this
      let lhs := lhs.cast this
      let rhs := rhs.cast this
      let s := s.cast this
      let s := s.push ref
      go aig (curr + 1) (by omega) discr lhs rhs s
    else
      have : curr = w := by omega
      ⟨aig, this ▸ s⟩
termination_by w - curr

namespace ite

theorem go_le_size (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (discr : Ref aig)
    (lhs rhs : RefVec aig w) (s : RefVec aig curr) :
    aig.decls.size ≤ (go aig curr hcurr discr lhs rhs s).aig.decls.size := by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    apply LawfulOperator.le_size (f := mkIfCached)
  · simp
termination_by w - curr

theorem go_decl_eq (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (discr : Ref aig)
    (lhs rhs : RefVec aig w) (s : RefVec aig curr) :
    ∀ (idx : Nat) (h1) (h2),
      (go aig curr hcurr discr lhs rhs s).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig curr hcurr discr lhs rhs s = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intro idx h1 h2
    rw [go_decl_eq]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkIfCached)]
    apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkIfCached)
    assumption
  · simp [← hgo]
termination_by w - curr

end ite

instance : LawfulVecOperator α IfInput ite where
  le_size := by
    intros
    unfold ite
    apply ite.go_le_size
  decl_eq := by
    intros
    unfold ite
    rw [ite.go_decl_eq]

namespace ite

theorem go_get_aux {w : Nat} (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (discr : Ref aig)
    (lhs rhs : RefVec aig w) (s : RefVec aig curr) :
    ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
      (go aig curr hcurr discr lhs rhs s).vec.get idx (by omega)
        =
      (s.get idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig curr hcurr discr lhs rhs s = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intros
    rw [go_get_aux]
    rw [AIG.RefVec.get_push_ref_lt]
    · simp only [Ref.cast, Ref.mk.injEq]
      rw [AIG.RefVec.get_cast]
      · simp
      · assumption
    · apply go_le_size
  · rw [← hgo]
    simp only [Nat.le_refl, get, Ref.gate_cast, Ref.mk.injEq, true_implies]
    have : curr = w := by omega
    subst this
    simp
termination_by w - curr

theorem go_get {w : Nat} (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (discr : Ref aig)
    (lhs rhs : RefVec aig w) (s : RefVec aig curr) :
    ∀ (idx : Nat) (hidx : idx < curr),
      (go aig curr hcurr discr lhs rhs s).vec.get idx (by omega)
        =
      (s.get idx hidx).cast (by apply go_le_size) := by
  intro idx hidx
  apply go_get_aux

theorem go_denote_mem_prefix {w : Nat} (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w)
    (discr : Ref aig) (lhs rhs : RefVec aig w) (s : RefVec aig curr) (start : Nat) (hstart) :
    ⟦
      (go aig curr hcurr discr lhs rhs s).aig,
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

theorem denote_go {w : Nat} (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (discr : Ref aig)
    (lhs rhs : RefVec aig w) (s : RefVec aig curr) :
    ∀ (idx : Nat) (hidx1 : idx < w),
      curr ≤ idx
        →
      ⟦
        (go aig curr hcurr discr lhs rhs s).aig,
        (go aig curr hcurr discr lhs rhs s).vec.get idx hidx1,
        assign
      ⟧
        =
      if ⟦aig, discr, assign⟧ then
        ⟦aig, lhs.get idx hidx1, assign⟧
      else
        ⟦aig, rhs.get idx hidx1, assign⟧ := by
  intro idx hidx1 hidx2
  generalize hgo : go aig curr hcurr discr lhs rhs s = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      subst heq
      rw [← hgo]
      rw [go_get]
      rw [AIG.RefVec.get_push_ref_eq']
      · rw [go_denote_mem_prefix]
        · simp
        · simp [Ref.hgate]
      · omega
    | inr heq =>
      rw [← hgo]
      rw [denote_go]
      · rw [LawfulOperator.denote_mem_prefix (f := mkIfCached)]
        rw [LawfulOperator.denote_mem_prefix (f := mkIfCached)]
        rw [LawfulOperator.denote_mem_prefix (f := mkIfCached)]
        · simp
        · simp [Ref.hgate]
        · simp [Ref.hgate]
        · simp [Ref.hgate]
      · omega
  · omega
termination_by w - curr

end ite

@[simp]
theorem denote_ite {aig : AIG α} {input : IfInput aig w} :
  ∀ (idx : Nat) (hidx : idx < w),
    ⟦(ite aig input).aig, (ite aig input).vec.get idx hidx, assign⟧
      =
    if ⟦aig, input.discr, assign⟧ then
      ⟦aig, input.lhs.get idx hidx, assign⟧
    else
      ⟦aig, input.rhs.get idx hidx, assign⟧ := by
  intro idx hidx
  unfold ite
  dsimp only
  rw [ite.denote_go]
  omega
end RefVec

end AIG

end Sat
end Std
