/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joe Hendrix

Basic operations on bitvectors.

This is a work-in-progress, and contains additions to other theories.
-/
import data.tuple

def bitvec (n : ℕ) := tuple bool n

namespace bitvec
open nat
open tuple

instance (n : nat) : decidable_eq (bitvec n) :=
begin unfold bitvec, apply_instance end

-- Create a zero bitvector
def zero {n : ℕ} : bitvec n := tuple.repeat ff

-- Create a bitvector with the constant one.
def one {n : ℕ} : bitvec (succ n) := tuple.append (tuple.repeat ff : bitvec n) [ tt ]

section shift

  -- shift left
  def shl {n : ℕ} : bitvec n → ℕ → bitvec n
    | x i :=
       if le : i ≤ n then
         let eq := nat.sub_add_cancel le in
         cast (congr_arg bitvec eq) (tuple.append (dropn i x) (zero : bitvec i))
       else
         zero

  -- unsigned shift right
  def ushr {n : ℕ} : bitvec n → ℕ → bitvec n
    | x i :=
      if le : i ≤ n then
        let y : bitvec (n-i) := @firstn _ _ _ (sub_le n i) x in
        let eq := calc (i+(n-i)) = (n - i) + i : nat.add_comm i (n - i)
                            ...  = n           : nat.sub_add_cancel le in
        cast (congr_arg bitvec eq) (tuple.append zero y)
      else
        zero

  -- signed shift right
  def sshr {m : ℕ} : bitvec (succ m) → ℕ → bitvec (succ m)
    | x i :=
      let n := succ m in
      if le : i ≤ n then
        let z : bitvec i := repeat (head x) in
        let y : bitvec (n-i) := @firstn _ _ (n - i) (sub_le n i) x in
        let eq := calc (i+(n-i)) = (n-i) + i : nat.add_comm i (n - i)
                            ...  = n         : nat.sub_add_cancel le in
        cast (congr_arg bitvec eq) (tuple.append z y)
      else
        zero

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

  protected def xor3 (x:bool) (y:bool) (c:bool) := bxor (bxor x y) c
  protected def carry (x:bool) (y:bool) (c:bool) :=
    x && y || x && c || y && c

  def neg : bitvec n → bitvec n
  | x :=
    let f := λy c, (y || c, bxor y c) in
    prod.snd (map_accumr f x ff)

  -- Add with carry (no overflow)
  def adc : bitvec n → bitvec n → bool → bitvec (n+1)
  | x y c :=
    let f := λx y c, (bitvec.carry x y c, bitvec.xor3 x y c) in
    let z := tuple.map_accumr₂ f x y c in
    prod.fst z :: prod.snd z

  def add : bitvec n → bitvec n → bitvec n
  | x y := tail (adc x y ff)

  protected def borrow (x:bool) (y:bool) (b:bool) :=
    bnot x && y || bnot x && b || y && b

  -- Subtract with borrow
  def sbb : bitvec n → bitvec n → bool → bool × bitvec n
  | x y b :=
    let f := λx y c, (bitvec.borrow x y c, bitvec.xor3 x y c) in
    tuple.map_accumr₂ f x y b

  def sub : bitvec n → bitvec n → bitvec n
  | x y := prod.snd (sbb x y ff)

  instance : has_zero (bitvec n) := ⟨zero⟩
  /- Remark: we used to have the instance has_one only for (bitvec (succ n)).
     Now, we define it for all n to make sure we don't have to solve unification problems such as:
     succ ?n =?= (bit0 (bit1 one)) -/
  instance : has_one (bitvec n) :=
  match n with
  | 0            := ⟨zero⟩
  | (nat.succ n) := ⟨one⟩
  end
  instance : has_add (bitvec n)  := ⟨add⟩
  instance : has_sub (bitvec n)  := ⟨sub⟩
  instance : has_neg (bitvec n)  := ⟨neg⟩

  def mul : bitvec n → bitvec n → bitvec n
  | x y :=
    let f := λr b, cond b (r + r + y) (r + r) in
    list.foldl f 0 (to_list x)

  instance : has_mul (bitvec n)  := ⟨mul⟩
end arith

section comparison
  variable {n : ℕ}

  def uborrow : bitvec n → bitvec n → bool := λx y, prod.fst (sbb x y ff)

  def ult (x y : bitvec n) : Prop := uborrow x y = tt
  def ugt (x y : bitvec n) : Prop := ult y x

  def ule (x y : bitvec n) : Prop := ¬ (ult y x)
  def uge : bitvec n → bitvec n → Prop := λx y, ule y x

  def sborrow : bitvec (succ n) → bitvec (succ n) → bool := λx y,
     bool.cases_on
       (head x)
       (bool.cases_on (head y) (uborrow (tail x) (tail y)) tt)
       (bool.cases_on (head y) ff (uborrow (tail x) (tail y)))

  def slt : bitvec (succ n) → bitvec (succ n) → Prop := λx y,
     sborrow x y = tt

  def sgt : bitvec (succ n) → bitvec (succ n) → Prop := λx y, slt y x
  def sle : bitvec (succ n) → bitvec (succ n) → Prop := λx y, ¬ (slt y x)
  def sge : bitvec (succ n) → bitvec (succ n) → Prop := λx y, sle y x

end comparison

section from_bitvec
  variable {α : Type}

  -- Convert a bitvector to another number.
  def from_bitvec [has_add α] [has_zero α] [has_one α] {n : nat} (v : bitvec n) : α :=
  let f : α → bool → α := λr b, cond b (r + r + 1) (r + r) in
  list.foldl f (0 : α) (to_list v)
end from_bitvec

private def to_string {n : nat} : bitvec n → string
| ⟨bs, p⟩ :=
  "0b" ++ (bs^.reverse^.for (λ b, if b then #"1" else #"0"))

instance (n : nat) : has_to_string (bitvec n) :=
⟨to_string⟩
end bitvec
