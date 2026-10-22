/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Init.Data.RArray
public import Init.Data.List.Basic
import Init.Data.List.Find
import Init.Data.Nat.Order
import Init.Data.BitVec
import Init.ByCases
meta import Init.Data.List.Control
meta import Init.Data.Repr
meta import Init.Data.String.Defs

/-!
This module contains auxiliary declarations for defining the EPR to `BitVec` encoding. The key
entrypoints are:
- `toBvAux` for encoding individual constants and in particular equality into BitVec
- the various `toBvPredₙ` for encoding predicates of arity `n` into BitVec
-/

namespace Std.Tactic.BVDecide.EPR.BitVec

open Classical in
/--
The injection from a sort of type `α` with elements in `elem` into `BitVec`.
-/
public noncomputable def toBvAux {α : Type u} {w : Nat} (elems : List α)
    (h : elems.length < 2 ^ w) (x : α) : BitVec w :=
  BitVec.ofNatLT (elems.idxOf x) (lt_of_le_of_lt List.idxOf_le_length h)

open Classical in
/--
The key theorem for `toBvAux`: Instead of comparing a sort of type `α` in `α` we can compare their
`BitVec` representations.
-/
public theorem eq_eq_toBvAux_eq_of_mem {α : Type u} {w : Nat} (elems : List α)
    (h1 : elems.length < 2 ^ w) (x y : α) (h2 : x ∈ elems) (h3 : y ∈ elems) :
    (x = y) = (toBvAux elems h1 x = toBvAux elems h1 y) := by
  apply propext
  constructor
  · simp +contextual
  · intro h4
    have hy : elems.idxOf y < elems.length :=
      List.idxOf_lt_length_of_mem h3
    have hx := List.getElem_idxOf (List.idxOf_lt_length_of_mem h2)
    have hy := List.getElem_idxOf (List.idxOf_lt_length_of_mem h3)
    rw [← hx, ← hy]
    unfold toBvAux at h4
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNatLT] at h4
    simp [h4]

open Classical in
theorem toBvAux_eq_length_of_not_mem {elems : List α} (h : elems.length < 2 ^ w) {x : α}
    (hx : x ∉ elems) : toBvAux elems h x = BitVec.ofNatLT elems.length h := by
  unfold toBvAux
  simp [← BitVec.toNat_inj]
  exact List.idxOf_eq_length hx

open Classical in
theorem toBvAux_lt_ofNatLT_length_of_mem {w : Nat} {elems : List α}
    (h : elems.length < 2 ^ w) {x : α} (hx : x ∈ elems) :
    toBvAux elems h x < BitVec.ofNatLT elems.length h := by
  unfold toBvAux
  simp only [BitVec.lt_def, BitVec.toNat_ofNatLT]
  exact List.idxOf_lt_length_of_mem hx

public theorem toBvAux_lt_ofNat_length_of_mem {α : Type u} {w : Nat} {elems : List α}
    (h : elems.length < 2 ^ w) {x : α} (hx : x ∈ elems) :
    toBvAux elems h x < BitVec.ofNat w elems.length := by
  have := toBvAux_lt_ofNatLT_length_of_mem h hx
  simpa [BitVec.ofNatLT_eq_ofNat] using this

public theorem mem_iff_toBvAux_mem_map_toBvAux {α : Type u} {w : Nat} (elems : List α)
    (h1 : elems.length < 2 ^ w) (x : α) :
    x ∈ elems ↔ toBvAux elems h1 x ∈ elems.map (toBvAux elems h1) := by
  constructor
  · intro hx
    rw [List.mem_map]
    exists x
  · intro hbv
    by_cases hx : x ∈ elems
    · exact hx
    · rw [List.mem_map] at hbv
      rcases hbv with ⟨x', hx'1, hx'2⟩
      rw [toBvAux_eq_length_of_not_mem h1 hx] at hx'2
      have := toBvAux_lt_ofNatLT_length_of_mem h1 hx'1
      simp [hx'2] at this

public theorem mem_map_nil {α : Type u} {β : Type v} (x : β) (f : α → β) : (x ∈ List.map f []) = False := by
  simp

public theorem mem_map_singleton {α : Type u} {β : Type v} (x : β) (y : α) (f : α → β) :
    (x ∈ List.map f [y]) = (x = f y)  := by
  simp

public theorem mem_map_cons_cons {α : Type u} {β : Type v} (x : β) (y z : α) (ys : List α) (f : α → β) :
    (x ∈ List.map f (y :: z :: ys)) = (x = f y ∨ x ∈ List.map f (z :: ys))  := by
  simp

/--
The left inverse of `toBvAux`.
-/
public def toSortAux {α : Type u} {w : Nat} (elems : List α) (default : α) (x : BitVec w) : α :=
  elems.getD x.toNat default

open Classical in
theorem toSortAux_toBvAux_eq_of_mem {α : Type u} {w : Nat} (elems : List α) (h : elems.length < 2 ^ w)
    (default : α) {x : α} (hx : x ∈ elems) :
    toSortAux elems default (toBvAux elems h x) = x := by
  unfold toSortAux toBvAux
  simp [List.getElem_idxOf, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hx)]

/-
This macro generates for all arities from 0 to 16 the following declarations:
- `toBvPredₙ` which can be used to encode an `n`-ary predicate `p : α₁ → ... → αₙ → Prop`
  to an `n`-ary BitVec predicate: `p' : BitVec w₁ → ... → BitVec wₙ → BitVec 1`
- `toBvPredₙ_toBvAux_eq` which states that we can replace an application `p x₁ ... xₙ`
  with `p' (toBvAux x₁) ... (toBvAux xₙ) = 1#1`.
-/

open Lean in
set_option hygiene false in
local macro "declare_bv_pred" n:num : command => do
  let n := n.getNat
  let idx (base : String) (i : Nat) : Ident :=
    mkIdent <| Name.mkSimple (base ++ i.toSubscriptString)
  let predName := idx "toBvPred" n
  let thmName := mkIdent <| predName.getId.appendAfter "_toBvAux_eq"
  let mut defBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder := #[]
  let mut thmBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder := #[]
  let mut xBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder := #[]
  let mut sorts : Array Term := #[]
  let mut predArgs : Array Term := #[]
  let mut bvBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder := #[]
  let mut sortArgs : Array Term := #[]
  let mut xs : Array Ident := #[]
  let mut bvArgs : Array Term := #[]
  for i in List.range' 1 n do
    let (α, w, elems, default) := (idx "α" i, idx "w" i, idx "elems" i, idx "default" i)
    let (h, x, hx, bv) := (idx "h" i, idx "x" i, idx "hx" i, idx "bv" i)
    let u : TSyntax `level := ⟨idx "u" i⟩
    defBinders := defBinders ++ #[
      ← `(bracketedBinder| {$α : Type $u}), ← `(bracketedBinder| {$w : Nat}),
      ← `(bracketedBinder| ($elems : List $α)), ← `(bracketedBinder| ($default : $α))]
    thmBinders := thmBinders ++ #[
      ← `(bracketedBinder| {$α : Type $u}), ← `(bracketedBinder| {$w : Nat}),
      ← `(bracketedBinder| ($elems : List $α)),
      ← `(bracketedBinder| ($h : List.length $elems < 2 ^ $w)),
      ← `(bracketedBinder| ($default : $α))]
    xBinders := xBinders ++ #[
      ← `(bracketedBinder| ($x : $α)), ← `(bracketedBinder| ($hx : $x ∈ $elems))]
    sorts := sorts.push α
    predArgs := predArgs ++ #[elems, default]
    bvBinders := bvBinders.push <| ← `(bracketedBinder| ($bv : BitVec $w))
    sortArgs := sortArgs.push <| ← `(toSortAux $elems $default $bv)
    xs := xs.push x
    bvArgs := bvArgs.push <| ← `(toBvAux $elems $h $x)
  let predTy ← sorts.foldrM (fun s acc => `($s → $acc)) (← `(Prop))
  `(
    public noncomputable def $predName $defBinders* (p : $predTy) $bvBinders* : BitVec 1 :=
      @ite _ (p $sortArgs*) (Classical.propDecidable _) 1#1 0#1

    public theorem $thmName $thmBinders* (p : $predTy) $xBinders* :
        (p $xs*) = ($predName $predArgs* p $bvArgs* = 1#1) := by
      unfold $predName
      simp [toSortAux_toBvAux_eq_of_mem, *]
  )

declare_bv_pred 1
declare_bv_pred 2
declare_bv_pred 3
declare_bv_pred 4
declare_bv_pred 5
declare_bv_pred 6
declare_bv_pred 7
declare_bv_pred 8
declare_bv_pred 9
declare_bv_pred 10
declare_bv_pred 11
declare_bv_pred 12
declare_bv_pred 13
declare_bv_pred 14
declare_bv_pred 15
declare_bv_pred 16


/--
An opaque constant used to instantiate quantifiers during MBQI checks.
-/
public def instConst {α : Type u} (_hypIdx : Nat) (_quantIdx : Nat) (default : α) : α := default

end Std.Tactic.BVDecide.EPR.BitVec
