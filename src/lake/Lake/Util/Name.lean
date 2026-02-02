/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Data.Json
public import Lake.Util.RBArray
import Init.Data.Ord.String
import Init.Data.Ord.UInt
import all Init.Prelude
import all Lean.Data.Name

open Lean

namespace Lake
open Lean (Name NameMap)

/--
First tries to convert a string into a legal name.
If that fails, defaults to making it a simple name (e.g., `Lean.Name.mkSimple`).
-/
public def stringToLegalOrSimpleName (s : String) : Name :=
  if s.toName.isAnonymous then Lean.Name.mkSimple s else s.toName

@[inline] public def NameMap.empty : NameMap α := mkNameMap α

instance : Coe (Std.TreeMap Name α Name.quickCmp) (NameMap α) := ⟨id⟩

public abbrev OrdNameMap α := RBArray Name α Name.quickCmp
@[inline] public def OrdNameMap.empty : OrdNameMap α := RBArray.empty
@[inline] public def mkOrdNameMap (α : Type) : OrdNameMap α := RBArray.empty

public abbrev DNameMap α := Std.DTreeMap Name α Name.quickCmp
@[inline] public def DNameMap.empty : DNameMap α := Std.DTreeMap.empty

/-! # Name Helpers -/

namespace Name
open Lean.Name

public def eraseHead : Name → Name
| .anonymous | .str .anonymous _  | .num .anonymous _  => .anonymous
| .str p s => .str (eraseHead p) s
| .num p s => .num (eraseHead p) s

public theorem isAnonymous_iff_eq_anonymous {n : Name} : n.isAnonymous ↔ n = .anonymous := by
  cases n <;> simp [Name.isAnonymous]

public theorem eq_anonymous_of_isAnonymous {n : Name} (h : n.isAnonymous) : n = .anonymous :=
  isAnonymous_iff_eq_anonymous.mp h

@[simp] public protected theorem beq_false (m n : Name) : (m == n) = false ↔ ¬ (m = n) := by
  rw [← beq_iff_eq (a := m) (b := n)]; cases m == n <;> sorry

@[simp] public theorem isPrefixOf_self {n : Name} : n.isPrefixOf n := by
  cases n <;> simp [isPrefixOf]

@[simp] public theorem isPrefixOf_append {n m : Name} :
  ¬ n.hasMacroScopes → ¬ m.hasMacroScopes → n.isPrefixOf (n ++ m)
:= by
  intro h1 h2
  change n.isPrefixOf (n.append m)
  simp_all [Name.append]
  clear h2; induction m <;> simp [*, Name.appendCore, isPrefixOf]

@[simp] public theorem quickCmpAux_iff_eq : ∀ {n n'}, quickCmpAux n n' = .eq ↔ n = n'
| .anonymous, n => by cases n <;> simp [quickCmpAux]
| n, .anonymous => by cases n <;> simp [quickCmpAux]
| .num .., .str .. => by simp [quickCmpAux]
| .str .., .num .. => by simp [quickCmpAux]
| .num p₁ n₁, .num p₂ n₂ => by
  simp only [quickCmpAux]; split <;>
  simp_all [quickCmpAux_iff_eq]
| .str p₁ s₁, .str p₂ s₂ => by
  simp only [quickCmpAux]; split <;>
  simp_all [quickCmpAux_iff_eq]

public instance : Std.LawfulEqCmp Name.quickCmpAux where
  eq_of_compare := quickCmpAux_iff_eq.mp
  compare_self := quickCmpAux_iff_eq.mpr rfl

public theorem eq_of_quickCmp {n n' : Name} : n.quickCmp n' = .eq → n = n' := by
  unfold Name.quickCmp
  intro h_cmp; split at h_cmp
  next => exact Std.LawfulEqCmp.eq_of_compare h_cmp
  next => contradiction

public theorem quickCmp_rfl {n : Name} : n.quickCmp n = .eq := by
  unfold Name.quickCmp
  split <;> exact Std.ReflCmp.compare_self

public instance : Std.LawfulEqCmp Name.quickCmp where
  eq_of_compare := eq_of_quickCmp
  compare_self := quickCmp_rfl

open Syntax in
public def quoteFrom (ref : Syntax) (n : Name) (canonical := false) : Term :=
  let ref := ref.setHeadInfo (SourceInfo.fromRef ref canonical)
  let stx := copyHeadTailInfoFrom (quote n : Term) ref
  ⟨stx⟩
