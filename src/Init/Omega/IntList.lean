/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Zip
import Init.Data.Int.DivMod.Bootstrap
import Init.Data.Nat.Gcd

namespace Lean.Omega

/--
A type synonym for `List Int`, used by `omega` for dense representation of coefficients.

We define algebraic operations,
interpreting `List Int` as a finitely supported function `Nat → Int`.
-/
abbrev IntList := List Int

namespace IntList

/-- Get the `i`-th element (interpreted as `0` if the list is not long enough). -/
def get (xs : IntList) (i : Nat) : Int := xs[i]?.getD 0

@[simp] theorem get_nil : get ([] : IntList) i = 0 := rfl
@[simp] theorem get_cons_zero : get (x :: xs) 0 = x := by simp [get]
@[simp] theorem get_cons_succ : get (x :: xs) (i+1) = get xs i := by simp [get]

theorem get_map {xs : IntList} (h : f 0 = 0) : get (xs.map f) i = f (xs.get i) := by
  simp only [get, List.getElem?_map]
  cases xs[i]? <;> simp_all

theorem get_of_length_le {xs : IntList} (h : xs.length ≤ i) : xs.get i = 0 := by
  rw [get, List.getElem?_eq_none_iff.mpr h]
  rfl

/-- Like `List.set`, but right-pad with zeroes as necessary first. -/
def set (xs : IntList) (i : Nat) (y : Int) : IntList :=
  match xs, i with
  | [], 0 => [y]
  | [], (i+1) => 0 :: set [] i y
  | _ :: xs, 0 => y :: xs
  | x :: xs, (i+1) => x :: set xs i y

@[simp] theorem set_nil_zero : set [] 0 y = [y] := rfl
@[simp] theorem set_nil_succ : set [] (i+1) y = 0 :: set [] i y := rfl
@[simp] theorem set_cons_zero : set (x :: xs) 0 y = y :: xs := rfl
@[simp] theorem set_cons_succ : set (x :: xs) (i+1) y = x :: set xs i y := rfl

/-- Returns the leading coefficient, i.e. the first non-zero entry. -/
def leading (xs : IntList) : Int := xs.find? (! · == 0) |>.getD 0

/-- Implementation of `+` on `IntList`. -/
def add (xs ys : IntList) : IntList :=
  List.zipWithAll (fun x y => x.getD 0 + y.getD 0) xs ys

instance : Add IntList := ⟨add⟩

theorem add_def (xs ys : IntList) :
    xs + ys = List.zipWithAll (fun x y => x.getD 0 + y.getD 0) xs ys :=
  rfl

@[simp] theorem add_get (xs ys : IntList) (i : Nat) : (xs + ys).get i = xs.get i + ys.get i := by
  simp only [get, add_def, List.getElem?_zipWithAll]
  cases xs[i]? <;> cases ys[i]? <;> simp

@[simp] theorem add_nil (xs : IntList) : xs + [] = xs := by simp [add_def]
@[simp] theorem nil_add (xs : IntList) : [] + xs = xs := by simp [add_def]
@[simp] theorem cons_add_cons (x) (xs : IntList) (y) (ys : IntList) :
    (x :: xs) + (y :: ys) = (x + y) :: (xs + ys) := by simp [add_def]

/-- Implementation of `*` on `IntList`. -/
def mul (xs ys : IntList) : IntList := List.zipWith (· * ·) xs ys

instance : Mul IntList := ⟨mul⟩

theorem mul_def (xs ys : IntList) : xs * ys = List.zipWith (· * ·) xs ys :=
  rfl

@[simp] theorem mul_get (xs ys : IntList) (i : Nat) : (xs * ys).get i = xs.get i * ys.get i := by
  simp only [get, mul_def, List.getElem?_zipWith]
  cases xs[i]? <;> cases ys[i]? <;> simp

@[simp] theorem mul_nil_left : ([] : IntList) * ys = [] := rfl
@[simp] theorem mul_nil_right : xs * ([] : IntList) = [] := List.zipWith_nil_right
@[simp] theorem mul_cons₂ : (x::xs : IntList) * (y::ys) = (x * y) :: (xs * ys) := rfl

/-- Implementation of negation on `IntList`. -/
def neg (xs : IntList) : IntList := xs.map fun x => -x

instance : Neg IntList := ⟨neg⟩

theorem neg_def (xs : IntList) : - xs = xs.map fun x => -x := rfl

@[simp] theorem neg_get (xs : IntList) (i : Nat) : (- xs).get i = - xs.get i := by
  simp only [get, neg_def, List.getElem?_map]
  cases xs[i]? <;> simp

@[simp] theorem neg_nil : (- ([] : IntList)) = [] := rfl
@[simp] theorem neg_cons : (- (x::xs : IntList)) = -x :: -xs := rfl

/-- Implementation of subtraction on `IntList`. -/
def sub (xs ys : IntList) : IntList :=
  List.zipWithAll (fun x y => x.getD 0 - y.getD 0) xs ys

instance : Sub IntList := ⟨sub⟩

theorem sub_def (xs ys : IntList) :
    xs - ys = List.zipWithAll (fun x y => x.getD 0 - y.getD 0) xs ys :=
  rfl

/-- Implementation of scalar multiplication by an integer on `IntList`. -/
def smul (xs : IntList) (i : Int) : IntList :=
  xs.map fun x => i * x

instance : HMul Int IntList IntList where
  hMul i xs := xs.smul i

theorem smul_def (xs : IntList) (i : Int) : i * xs = xs.map fun x => i * x := rfl

@[simp] theorem smul_get (xs : IntList) (a : Int) (i : Nat) : (a * xs).get i = a * xs.get i := by
  simp only [get, smul_def, List.getElem?_map]
  cases xs[i]? <;> simp

@[simp] theorem smul_nil {i : Int} : i * ([] : IntList) = [] := rfl
@[simp] theorem smul_cons {i : Int} : i * (x::xs : IntList) = i * x :: i * xs := rfl

/-- A linear combination of two `IntList`s. -/
def combo (a : Int) (xs : IntList) (b : Int) (ys : IntList) : IntList :=
  List.zipWithAll (fun x y => a * x.getD 0 + b * y.getD 0) xs ys

theorem combo_eq_smul_add_smul (a : Int) (xs : IntList) (b : Int) (ys : IntList) :
    combo a xs b ys = a * xs + b * ys := by
  dsimp [combo]
  induction xs generalizing ys with
  | nil => simp; rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp; rfl
    | cons y ys => simp_all

attribute [local simp] add_def mul_def in
theorem mul_distrib_left (xs ys zs : IntList) : (xs + ys) * zs = xs * zs + ys * zs := by
  induction xs generalizing ys zs with
  | nil =>
    cases ys with
    | nil => simp
    | cons _ _ =>
      cases zs with
      | nil => simp
      | cons _ _ => simp_all [Int.add_mul]
  | cons x xs ih₁ =>
    cases ys with
    | nil => simp_all
    | cons _ _ =>
      cases zs with
      | nil => simp
      | cons _ _ => simp_all [Int.add_mul]

theorem mul_neg_left (xs ys : IntList) : (-xs) * ys = -(xs * ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp_all [Int.neg_mul]

attribute [local simp] add_def neg_def sub_def in
theorem sub_eq_add_neg (xs ys : IntList) : xs - ys = xs + (-ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp_all [Int.sub_eq_add_neg]

@[simp] theorem mul_smul_left {i : Int} {xs ys : IntList} : (i * xs) * ys = i * (xs * ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp_all [Int.mul_assoc]

/-- The sum of the entries of an `IntList`. -/
def sum (xs : IntList) : Int := xs.foldr (· + ·) 0

@[simp] theorem sum_nil : sum ([] : IntList) = 0 := rfl
@[simp] theorem sum_cons : sum (x::xs : IntList) = x + sum xs := rfl

attribute [local simp] sum add_def in
theorem sum_add (xs ys : IntList) : (xs + ys).sum = xs.sum + ys.sum := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp_all [Int.add_assoc, Int.add_left_comm]

@[simp]
theorem sum_neg (xs : IntList) : (-xs).sum = -(xs.sum) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp_all [Int.neg_add]

@[simp]
theorem sum_smul (i : Int) (xs : IntList) : (i * xs).sum = i * (xs.sum) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp_all [Int.mul_add]

/-- The dot product of two `IntList`s. -/
def dot (xs ys : IntList) : Int := (xs * ys).sum

example : IntList.dot [a, b, c] [x, y, z] = IntList.dot [a, b, c, d] [x, y, z] := rfl
example : IntList.dot [a, b, c] [x, y, z] = IntList.dot [a, b, c] [x, y, z, w] := rfl

@[local simp] theorem dot_nil_left : dot ([] : IntList) ys = 0 := rfl
@[simp] theorem dot_nil_right : dot xs ([] : IntList) = 0 := by simp [dot]
@[simp] theorem dot_cons₂ : dot (x::xs) (y::ys) = x * y + dot xs ys := rfl

-- theorem dot_comm (xs ys : IntList) : dot xs ys = dot ys xs := by
--   rw [dot, dot, mul_comm]

@[simp] theorem dot_set_left (xs ys : IntList) (i : Nat) (z : Int) :
    dot (xs.set i z) ys = dot xs ys + (z - xs.get i) * ys.get i := by
  induction xs generalizing i ys with
  | nil =>
    induction i generalizing ys with
    | zero => cases ys <;> simp
    | succ i => cases ys <;> simp_all
  | cons x xs ih =>
    induction i generalizing ys with
    | zero =>
      cases ys with
      | nil => simp
      | cons y ys =>
        simp only [Nat.zero_eq, set_cons_zero, dot_cons₂, get_cons_zero, Int.sub_mul]
        rw [Int.add_right_comm, Int.add_comm (x * y), Int.sub_add_cancel]
    | succ i =>
      cases ys with
      | nil => simp
      | cons y ys => simp_all [Int.add_assoc]

theorem dot_distrib_left (xs ys zs : IntList) : (xs + ys).dot zs = xs.dot zs + ys.dot zs := by
  simp [dot, mul_distrib_left, sum_add]

@[simp] theorem dot_neg_left (xs ys : IntList) : (-xs).dot ys = -(xs.dot ys) := by
  simp [dot, mul_neg_left]

@[simp] theorem dot_smul_left (xs ys : IntList) (i : Int) : (i * xs).dot ys = i * xs.dot ys := by
  simp [dot]

theorem dot_of_left_zero (w : ∀ x, x ∈ xs → x = 0) : dot xs ys = 0 := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      rw [dot_cons₂, w x (by simp), ih]
      · simp
      · intro x m
        apply w
        exact List.mem_cons_of_mem _ m

/-- Division of an `IntList` by a integer. -/
def sdiv (xs : IntList) (g : Int) : IntList := xs.map fun x => x / g

@[simp] theorem sdiv_nil : sdiv [] g = [] := rfl
@[simp] theorem sdiv_cons : sdiv (x::xs) g = (x / g) :: sdiv xs g := rfl

/-- The gcd of the absolute values of the entries of an `IntList`. -/
def gcd (xs : IntList) : Nat := xs.foldr (fun x g => Nat.gcd x.natAbs g) 0

@[simp] theorem gcd_nil : gcd [] = 0 := rfl
@[simp] theorem gcd_cons : gcd (x :: xs) = Nat.gcd x.natAbs (gcd xs) := rfl

theorem gcd_cons_div_left : (gcd (x::xs) : Int) ∣ x := by
  simp only [gcd, List.foldr_cons, Int.ofNat_dvd_left]
  apply Nat.gcd_dvd_left

theorem gcd_cons_div_right : gcd (x::xs) ∣ gcd xs := by
  simp only [gcd, List.foldr_cons]
  apply Nat.gcd_dvd_right

theorem gcd_cons_div_right' : (gcd (x::xs) : Int) ∣ (gcd xs : Int) := by
  rw [Int.ofNat_dvd_left, Int.natAbs_ofNat]
  exact gcd_cons_div_right

theorem gcd_dvd (xs : IntList) {a : Int} (m : a ∈ xs) : (xs.gcd : Int) ∣ a := by
  rw [Int.ofNat_dvd_left]
  induction m with
  | head =>
    simp only [gcd_cons]
    apply Nat.gcd_dvd_left
  | tail b m ih =>   -- FIXME: why is the argument of tail implicit?
    simp only [gcd_cons]
    exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) ih

theorem dvd_gcd (xs : IntList) (c : Nat) (w : ∀ {a : Int}, a ∈ xs → (c : Int) ∣ a) :
    c ∣ xs.gcd := by
  simp only [Int.ofNat_dvd_left] at w
  induction xs with
  | nil => have := Nat.dvd_zero c; simp
  | cons x xs ih =>
    simp
    apply Nat.dvd_gcd
    · apply w
      simp
    · apply ih
      intro b m
      apply w
      exact List.mem_cons_of_mem x m

theorem gcd_eq_iff {xs : IntList} {g : Nat} :
    xs.gcd = g ↔
      (∀ {a : Int}, a ∈ xs → (g : Int) ∣ a) ∧
        (∀ (c : Nat), (∀ {a : Int}, a ∈ xs → (c : Int) ∣ a) → c ∣ g) := by
  constructor
  · rintro rfl
    exact ⟨gcd_dvd _, dvd_gcd _⟩
  · rintro ⟨hi, hg⟩
    apply Nat.dvd_antisymm
    · apply hg
      intro i m
      exact gcd_dvd xs m
    · exact dvd_gcd xs g hi

attribute [simp] Int.zero_dvd

@[simp] theorem gcd_eq_zero {xs : IntList} : xs.gcd = 0 ↔ ∀ x, x ∈ xs → x = 0 := by
  simp [gcd_eq_iff, Nat.dvd_zero]

@[simp] theorem dot_mod_gcd_left (xs ys : IntList) : dot xs ys % xs.gcd = 0 := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      rw [dot_cons₂, Int.add_emod,
        ← Int.emod_emod_of_dvd (x * y) (gcd_cons_div_left),
        ← Int.emod_emod_of_dvd (dot xs ys) (Int.ofNat_dvd.mpr gcd_cons_div_right)]
      simp_all

theorem gcd_dvd_dot_left (xs ys : IntList) : (xs.gcd : Int) ∣ dot xs ys :=
  Int.dvd_of_emod_eq_zero (dot_mod_gcd_left xs ys)

theorem dot_eq_zero_of_left_eq_zero {xs ys : IntList} (h : ∀ x, x ∈ xs → x = 0) : dot xs ys = 0 := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      rw [dot_cons₂, h x List.mem_cons_self, ih (fun x m => h x (List.mem_cons_of_mem _ m)),
        Int.zero_mul, Int.add_zero]

@[simp] theorem nil_dot (xs : IntList) : dot [] xs = 0 := rfl

theorem dot_sdiv_left (xs ys : IntList) {d : Int} (h : d ∣ xs.gcd) :
    dot (xs.sdiv d) ys = (dot xs ys) / d := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      have wx : d ∣ x := Int.dvd_trans h (gcd_cons_div_left)
      have wxy : d ∣ x * y := Int.dvd_trans wx (Int.dvd_mul_right x y)
      have w : d ∣ (IntList.gcd xs : Int) := Int.dvd_trans h (gcd_cons_div_right')
      simp_all [Int.add_ediv_of_dvd_left, Int.mul_ediv_assoc']

/-- Apply "balanced mod" to each entry in an `IntList`. -/
abbrev bmod (x : IntList) (m : Nat) : IntList := x.map (Int.bmod · m)

theorem bmod_length (x : IntList) (m) : (bmod x m).length ≤ x.length :=
  Nat.le_of_eq (List.length_map _)

/--
The difference between the balanced mod of a dot product,
and the dot product with balanced mod applied to each entry of the left factor.
-/
abbrev bmod_dot_sub_dot_bmod (m : Nat) (a b : IntList) : Int :=
    (Int.bmod (dot a b) m) - dot (bmod a m) b

theorem dvd_bmod_dot_sub_dot_bmod (m : Nat) (xs ys : IntList) :
    (m : Int) ∣ bmod_dot_sub_dot_bmod m xs ys := by
  dsimp [bmod_dot_sub_dot_bmod]
  rw [Int.dvd_iff_emod_eq_zero]
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      simp only [IntList.dot_cons₂, List.map_cons]
      specialize ih ys
      rw [Int.sub_emod, Int.bmod_emod] at ih
      rw [Int.sub_emod, Int.bmod_emod, Int.add_emod, Int.add_emod (Int.bmod x m * y),
        ← Int.sub_emod, ← Int.sub_sub, Int.sub_eq_add_neg, Int.sub_eq_add_neg,
        Int.add_assoc (x * y % m), Int.add_comm (IntList.dot _ _ % m), ← Int.add_assoc,
        Int.add_assoc, Int.add_neg_eq_sub, Int.add_neg_eq_sub, Int.add_emod, ih, Int.add_zero,
        Int.emod_emod, Int.mul_emod, Int.mul_emod (Int.bmod x m), Int.bmod_emod, Int.sub_self,
        Int.zero_emod]

end IntList

end Lean.Omega
