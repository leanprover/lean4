/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Init.Data.RArray
public import Init.Data.List.Basic
public import Std.Data.HashMap.Basic
import Init.Data.List.Find
import Init.Data.Nat.Order
import Init.Data.BitVec
import Init.ByCases
meta import Init.Data.List.Control
meta import Init.Data.Repr
meta import Init.Data.String.Defs
meta import Init.Data.Range.Polymorphic.PRange
meta import Init.Data.Range.Polymorphic.Iterators
meta import Init.Data.Range.Polymorphic.Nat
meta import Init.Data.Range

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

/--
This is the bound used for the BitVec representation of each sort element to achieve a basic, sound
encoding. Every element is bound by the overall size of its sort.
-/
public theorem toBvAux_lt_ofNat_length_of_mem {α : Type u} {w : Nat} {elems : List α}
    (h : elems.length < 2 ^ w) {x : α} (hx : x ∈ elems) :
    toBvAux elems h x < BitVec.ofNat w elems.length := by
  have := toBvAux_lt_ofNatLT_length_of_mem h hx
  simpa [BitVec.ofNatLT_eq_ofNat] using this

open Classical in
/--
Instead of bounding each element by the overall size of the sort we can use the first half of
Paradox style symmetry breaking by saying:
```
α₀ ≤ 0
α₁ ≤ 1
α₂ ≤ 2
...
```
-/
public theorem toBvAux_le_ofNat_of_getElem_eq {α : Type u} {w : Nat} {elems : List α}
    (h : elems.length < 2 ^ w) {x : α} {i : Nat} (hi : i < elems.length) (hx : elems[i] = x) :
    toBvAux elems h x ≤ BitVec.ofNat w i := by
  have hi' : i < 2 ^ w := Nat.lt_trans hi h
  simp only [BitVec.le_def, toBvAux, BitVec.toNat_ofNatLT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi']
  subst hx
  apply Classical.byContradiction
  intro hc
  have hlt : i < elems.idxOf elems[i] := Nat.lt_of_not_le hc
  have := List.not_of_lt_findIdx hlt
  simp at this

open Classical in
/--
As an additional level of symmetry breaking we can say that given a sort represented as a list
`[α₀, α₁, ...]` if `αᵢ` is not at index `i` (i.e. equal to some `αₙ` for `n  < i`) then no sort
member can have the BitVec representation `i`.
-/
public theorem toBvAux_ne_of_toBvAux_lt {α : Type u} {w : Nat} {elems : List α}
    (h : elems.length < 2 ^ w)
    {x : α} {i : Nat} (hi : i < elems.length) (hx : elems[i] = x) (y : α) :
    toBvAux elems h x < BitVec.ofNat w i → toBvAux elems h y ≠ BitVec.ofNat w i := by
  intro h1 h2
  have hi' : i < 2 ^ w := Nat.lt_trans hi h
  simp only [BitVec.lt_def, ← BitVec.toNat_inj, toBvAux, BitVec.toNat_ofNatLT, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi'] at h1 h2
  have hy' : y ∈ elems := by
    apply Classical.byContradiction
    intro hn
    rw [List.idxOf_eq_length hn] at h2
    exact Nat.lt_irrefl _ (h2 ▸ hi)
  have e := List.getElem_idxOf (List.idxOf_lt_length_of_mem hy')
  simp only [h2] at e
  have hxy : x = y := hx.symm.trans e
  subst hxy
  exact Nat.ne_of_lt h1 h2

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

meta def toBvPredNames (kind : String) (n : Nat) : Lean.Name × Lean.Name :=
  let pred := Lean.Name.mkSimple ("toBvPred" ++ kind ++ n.toSubscriptString)
  (pred, pred.appendAfter "_toBvAux_eq")

/-
This macro generates for an arity `n` the following declarations:
- `toBvPredPropₙ` which can be used to encode an `n`-ary predicate `p : α₁ → ... → αₙ → Prop`
  to an `n`-ary BitVec predicate: `p' : BitVec w₁ → ... → BitVec wₙ → Bool`
- `toBvPredPropₙ_toBvAux_eq` which states that we can replace an application `p x₁ ... xₙ`
  with `p' (toBvAux x₁) ... (toBvAux xₙ) = true`.
- the same but with `toBvPredBool` for predicates into `Bool`.
-/

open Lean in
set_option hygiene false in
local macro "declare_bv_pred" n:num : command => do
  let n := n.getNat
  let idx (base : String) (i : Nat) : Ident :=
    mkIdent <| Name.mkSimple (base ++ i.toSubscriptString)
  let (propPredName, propThmName) := toBvPredNames "Prop" n
  let (propPredName, propThmName) := (mkIdent propPredName, mkIdent propThmName)
  let (boolPredName, boolThmName) := toBvPredNames "Bool" n
  let (boolPredName, boolThmName) := (mkIdent boolPredName, mkIdent boolThmName)
  let mut defBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder := #[]
  let mut thmBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder := #[]
  let mut xBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder := #[]
  let mut sorts : Array Term := #[]
  let mut predArgs : Array Term := #[]
  let mut bvBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder := #[]
  let mut sortArgs : Array Term := #[]
  let mut xs : Array Ident := #[]
  let mut bvArgs : Array Term := #[]
  for i in 1...=n do
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
  let propPredTy ← sorts.foldrM (fun s acc => `($s → $acc)) (← `(Prop))
  let boolPredTy ← sorts.foldrM (fun s acc => `($s → $acc)) (← `(Bool))
  `(
    public noncomputable def $propPredName $defBinders* (p : $propPredTy) $bvBinders* : Bool :=
      @decide (p $sortArgs*) (Classical.propDecidable _)

    public theorem $propThmName $thmBinders* (p : $propPredTy) $xBinders* :
        (p $xs*) = ($propPredName $predArgs* p $bvArgs* = true) := by
      unfold $propPredName
      simp [toSortAux_toBvAux_eq_of_mem, *]

    public noncomputable def $boolPredName $defBinders* (p : $boolPredTy) $bvBinders* : Bool :=
      p $sortArgs*

    public theorem $boolThmName $thmBinders* (p : $boolPredTy) $xBinders* :
        (p $xs*) = ($boolPredName $predArgs* p $bvArgs*) := by
      unfold $boolPredName
      simp [toSortAux_toBvAux_eq_of_mem, *]
  )

open Lean in
set_option hygiene false in
local macro "declare_bv_preds" maxArity:num : command => do
  let ns ← Macro.getCurrNamespace
  let mut cmds : Array Syntax := #[]
  let mut propArities : Array Term := #[]
  let mut propDecls : Array Term := #[]
  let mut boolArities : Array Term := #[]
  let mut boolDecls : Array Term := #[]
  for i in 1...=maxArity.getNat do
    cmds := cmds.push <| ← `(command| declare_bv_pred $(quote i):num)
    let (propPred, propThm) := toBvPredNames "Prop" i
    let (propPred, propThm) : Term × Term := (quote (ns ++ propPred), quote (ns ++ propThm))
    propArities := propArities.push <| ← `(($propPred, $(quote i):num))
    propDecls := propDecls.push <| ← `(($propPred, $propThm))
    let (boolPred, boolThm) := toBvPredNames "Bool" i
    let (boolPred, boolThm) : Term × Term := (quote (ns ++ boolPred), quote (ns ++ boolThm))
    boolArities := boolArities.push <| ← `(($boolPred, $(quote i):num))
    boolDecls := boolDecls.push <| ← `(($boolPred, $boolThm))
  let tables ← `(
    public def maxToBvPredArity : Nat := $maxArity

    public def toBvPredPropArity : Std.HashMap Lean.Name Nat := Std.HashMap.ofList [$propArities,*]

    public def toBvPredPropDecls : Array (Lean.Name × Lean.Name) := #[$propDecls,*]

    public def toBvPredBoolArity : Std.HashMap Lean.Name Nat := Std.HashMap.ofList [$boolArities,*]

    public def toBvPredBoolDecls : Array (Lean.Name × Lean.Name) := #[$boolDecls,*]
  )
  return ⟨mkNullNode (cmds.push tables)⟩

declare_bv_preds 64

/--
An opaque constant used to instantiate quantifiers during MBQI checks.
-/
public def instConst {α : Type u} (_quantIdx : Nat) (default : α) : α := default

end Std.Tactic.BVDecide.EPR.BitVec
