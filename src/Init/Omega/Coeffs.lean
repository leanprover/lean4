/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Omega.IntList

/-!
# `Coeffs` as a wrapper for `IntList`

Currently `omega` uses a dense representation for coefficients.
However, we can swap this out for a sparse representation.

This file sets up `Coeffs` as a type synonym for `IntList`,
and abbreviations for the functions in the `IntList` namespace which we need to use in the
`omega` algorithm.

There is an equivalent file setting up `Coeffs` as a type synonym for `AssocList Nat Int`,
currently in a private branch.
Not all the theorems about the algebraic operations on that representation have been proved yet.
When they are ready, we can replace the implementation in `omega` simply by importing
`Init.Omega.IntDict` instead of `Init.Omega.IntList`.

For small problems, the sparse representation is actually slightly slower,
so it is not urgent to make this replacement.
-/

namespace Lean.Omega

/-- Type synonym for `IntList := List Int`. -/
abbrev Coeffs := IntList

namespace Coeffs

/-- Identity, turning `Coeffs` into `List Int`. -/
abbrev toList (xs : Coeffs) : List Int := xs
/-- Identity, turning `List Int` into `Coeffs`. -/
abbrev ofList (xs : List Int) : Coeffs := xs
/-- Are the coefficients all zero? -/
abbrev isZero (xs : Coeffs) : Prop := ∀ x, x ∈ xs → x = 0
/-- Shim for `IntList.set`. -/
abbrev set (xs : Coeffs) (i : Nat) (y : Int) : Coeffs := IntList.set xs i y
/-- Shim for `IntList.get`. -/
abbrev get (xs : Coeffs) (i : Nat) : Int := IntList.get xs i
/-- Shim for `IntList.gcd`. -/
abbrev gcd (xs : Coeffs) : Nat := IntList.gcd xs
/-- Shim for `IntList.smul`. -/
abbrev smul (xs : Coeffs) (g : Int) : Coeffs := IntList.smul xs g
/-- Shim for `IntList.sdiv`. -/
abbrev sdiv (xs : Coeffs) (g : Int) : Coeffs := IntList.sdiv xs g
/-- Shim for `IntList.dot`. -/
abbrev dot (xs ys : Coeffs) : Int := IntList.dot xs ys
/-- Shim for `IntList.add`. -/
abbrev add (xs ys : Coeffs) : Coeffs := IntList.add xs ys
/-- Shim for `IntList.sub`. -/
abbrev sub (xs ys : Coeffs) : Coeffs := IntList.sub xs ys
/-- Shim for `IntList.neg`. -/
abbrev neg (xs : Coeffs) : Coeffs := IntList.neg xs
/-- Shim for `IntList.combo`. -/
abbrev combo (a : Int) (xs : Coeffs) (b : Int) (ys : Coeffs) : Coeffs := IntList.combo a xs b ys
/-- Shim for `List.length`. -/
abbrev length (xs : Coeffs) := List.length xs
/-- Shim for `IntList.leading`. -/
abbrev leading (xs : Coeffs) : Int := IntList.leading xs
/-- Shim for `List.map`. -/
abbrev map (f : Int → Int) (xs : Coeffs) : Coeffs := List.map f xs
/-- Shim for `.enum.find?`. -/
abbrev findIdx? (f : Int → Bool) (xs : Coeffs) : Option Nat :=
  List.findIdx? f xs
/-- Shim for `IntList.bmod`. -/
abbrev bmod (x : Coeffs) (m : Nat) : Coeffs := IntList.bmod x m
/-- Shim for `IntList.bmod_dot_sub_dot_bmod`. -/
abbrev bmod_dot_sub_dot_bmod (m : Nat) (a b : Coeffs) : Int :=
  IntList.bmod_dot_sub_dot_bmod m a b
theorem bmod_length (x : Coeffs) (m : Nat) : (bmod x m).length ≤ x.length :=
  IntList.bmod_length x m
theorem dvd_bmod_dot_sub_dot_bmod (m : Nat) (xs ys : Coeffs) :
    (m : Int) ∣ bmod_dot_sub_dot_bmod m xs ys := IntList.dvd_bmod_dot_sub_dot_bmod m xs ys

theorem get_of_length_le {i : Nat} {xs : Coeffs} (h : length xs ≤ i) : get xs i = 0 :=
  IntList.get_of_length_le h
theorem dot_set_left (xs ys : Coeffs) (i : Nat) (z : Int) :
    dot (set xs i z) ys = dot xs ys + (z - get xs i) * get ys i :=
  IntList.dot_set_left xs ys i z
theorem dot_sdiv_left (xs ys : Coeffs) {d : Int} (h : d ∣ xs.gcd) :
    dot (xs.sdiv d) ys = (dot xs ys) / d :=
  IntList.dot_sdiv_left xs ys h
theorem dot_smul_left (xs ys : Coeffs) (i : Int) : dot (i * xs) ys = i * dot xs ys :=
  IntList.dot_smul_left xs ys i
theorem dot_distrib_left (xs ys zs : Coeffs) : (xs + ys).dot zs = xs.dot zs + ys.dot zs :=
  IntList.dot_distrib_left xs ys zs
theorem sub_eq_add_neg (xs ys : Coeffs) : xs - ys = xs + -ys :=
  IntList.sub_eq_add_neg xs ys
theorem combo_eq_smul_add_smul (a : Int) (xs : Coeffs) (b : Int) (ys : Coeffs) :
    combo a xs b ys = (a * xs) + (b * ys) :=
  IntList.combo_eq_smul_add_smul a xs b ys
theorem gcd_dvd_dot_left (xs ys : Coeffs) : (gcd xs : Int) ∣ dot xs ys :=
  IntList.gcd_dvd_dot_left xs ys
theorem map_length {xs : Coeffs} : (xs.map f).length ≤ xs.length :=
  Nat.le_of_eq (List.length_map f)

theorem dot_nil_right {xs : Coeffs} : dot xs .nil = 0 := IntList.dot_nil_right
theorem get_nil : get .nil i = 0 := IntList.get_nil
theorem dot_neg_left (xs ys : IntList) : dot (-xs) ys = -dot xs ys :=
  IntList.dot_neg_left xs ys

end Coeffs

end Lean.Omega
