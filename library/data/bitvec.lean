/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich

Basic operations on bitvectors.

This is a work-in-progress, and contains additions to other theories.
-/
import data.tuple

@[reducible] def bitvec (n : ℕ) := tuple bool n

namespace bitvec
open nat
open tuple

local infix `++ₜ`:65 := tuple.append

-- Create a zero bitvector
@[reducible] protected def zero (n : ℕ) : bitvec n := repeat ff n

-- Create a bitvector with the constant one.
@[reducible] protected def one : Π (n : ℕ), bitvec n
| 0        := []
| (succ n) := repeat ff n ++ₜ [tt]

protected def cong {a b : ℕ} (h : a = b) : bitvec a → bitvec b
| ⟨x, p⟩ := ⟨x, h ▸ p⟩

-- bitvec specific version of tuple.append
def append {m n} : bitvec m → bitvec n → bitvec (m + n) := tuple.append

section shift
  variable {n : ℕ}

  def shl (x : bitvec n) (i : ℕ) : bitvec n :=
  bitvec.cong (by simp) $
    dropn i x ++ₜ repeat ff (min n i)

  local attribute [ematch] nat.add_sub_assoc sub_le le_of_not_ge sub_eq_zero_of_le
  def fill_shr (x : bitvec n) (i : ℕ) (fill : bool) : bitvec n :=
  bitvec.cong (begin [smt] by_cases (i ≤ n), eblast end) $
    repeat fill (min n i) ++ taken (n-i) x

  -- unsigned shift right
  def ushr (x : bitvec n) (i : ℕ) : bitvec n :=
  fill_shr x i ff

  -- signed shift right
  def sshr : Π {m : ℕ}, bitvec m → ℕ → bitvec m
  | 0        _ _ := []
  | (succ m) x i := head x :: fill_shr (tail x) i (head x)

end shift

section bitwise
  variable {n : ℕ}

  def not : bitvec n → bitvec n := map bnot
  def and : bitvec n → bitvec n → bitvec n := map₂ band
  def or  : bitvec n → bitvec n → bitvec n := map₂ bor
  def xor : bitvec n → bitvec n → bitvec n := map₂ bxor

end bitwise

section arith
  variable {n : ℕ}

  protected def xor3 (x y c : bool) := bxor (bxor x y) c
  protected def carry (x y c : bool) :=
  x && y || x && c || y && c

  protected def neg (x : bitvec n) : bitvec n :=
  let f := λ y c, (y || c, bxor y c) in
  prod.snd (map_accumr f x ff)

  -- Add with carry (no overflow)
  def adc (x y : bitvec n) (c : bool) : bitvec (n+1) :=
  let f := λ x y c, (bitvec.carry x y c, bitvec.xor3 x y c) in
  let ⟨c, z⟩ := tuple.map_accumr₂ f x y c in
  c :: z

  protected def add (x y : bitvec n) : bitvec n := tail (adc x y ff)

  protected def borrow (x y b : bool) :=
  bnot x && y || bnot x && b || y && b

  -- Subtract with borrow
  def sbb (x y : bitvec n) (b : bool) : bool × bitvec n :=
  let f := λ x y c, (bitvec.borrow x y c, bitvec.xor3 x y c) in
  tuple.map_accumr₂ f x y b

  protected def sub (x y : bitvec n) : bitvec n := prod.snd (sbb x y ff)

  instance : has_zero (bitvec n) := ⟨bitvec.zero n⟩
  instance : has_one (bitvec n)  := ⟨bitvec.one n⟩
  instance : has_add (bitvec n)  := ⟨bitvec.add⟩
  instance : has_sub (bitvec n)  := ⟨bitvec.sub⟩
  instance : has_neg (bitvec n)  := ⟨bitvec.neg⟩

  protected def mul (x y : bitvec n) : bitvec n :=
  let f := λ r b, cond b (r + r + y) (r + r) in
  list.foldl f 0 (to_list x)

  instance : has_mul (bitvec n)  := ⟨bitvec.mul⟩
end arith

section comparison
  variable {n : ℕ}

  def uborrow (x y : bitvec n) : bool := prod.fst (sbb x y ff)

  def ult (x y : bitvec n) : Prop := uborrow x y
  def ugt (x y : bitvec n) : Prop := ult y x

  def ule (x y : bitvec n) : Prop := ¬ (ult y x)
  def uge (x y : bitvec n) : Prop := ule y x

  def sborrow : Π {n : ℕ}, bitvec n → bitvec n → bool
  | 0        _ _ := ff
  | (succ n) x y :=
    match (head x, head y) with
    | (tt, ff) := tt
    | (ff, tt) := ff
    | _        := uborrow (tail x) (tail y)
    end

  def slt (x y : bitvec n) : Prop := sborrow x y
  def sgt (x y : bitvec n) : Prop := slt y x
  def sle (x y : bitvec n) : Prop := ¬ (slt y x)
  def sge (x y : bitvec n) : Prop := sle y x

end comparison

section conversion
  variable {α : Type}

  protected def of_nat : Π (n : ℕ), nat → bitvec n
  | 0        x := nil
  | (succ n) x := of_nat n (x / 2) ++ₜ [to_bool (x % 2 = 1)]

  protected def of_int : Π (n : ℕ), int → bitvec (succ n)
  | n (int.of_nat m)          := ff :: bitvec.of_nat n m
  | n (int.neg_succ_of_nat m) := tt :: not (bitvec.of_nat n m)

  def bits_to_nat (v : list bool) : nat :=
  list.foldl (λ r b, r + r + cond b 1 0) 0 v

  protected def to_nat {n : nat} (v : bitvec n) : nat :=
  bits_to_nat (to_list v)

  protected def to_int : Π {n : nat}, bitvec n → int
  | 0        _ := 0
  | (succ n) v :=
    cond (head v)
      (int.neg_succ_of_nat $ bitvec.to_nat $ not $ tail v)
      (int.of_nat $ bitvec.to_nat $ tail v)

end conversion

private def to_string {n : nat} : bitvec n → string
| ⟨bs, p⟩ :=
  "0b" ++ (bs^.reverse^.for (λ b, if b then #"1" else #"0"))

instance (n : nat) : has_to_string (bitvec n) :=
⟨to_string⟩
end bitvec

instance {n} {x y : bitvec n} : decidable (bitvec.ult x y) := bool.decidable_eq _ _
instance {n} {x y : bitvec n} : decidable (bitvec.ugt x y) := bool.decidable_eq _ _
