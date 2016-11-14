/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joe Hendrix

Basic operations on bitvectors.

This is a work-in-progress, and contains additions to other theories.
-/
import data.tuple

definition bitvec (n : ℕ) := tuple bool n

namespace bitvec

open nat
open tuple

-- Create a zero bitvector
definition zero { n : ℕ } : bitvec n := tuple.repeat ff

-- Create a bitvector with the constant one.
definition one {n : ℕ} : bitvec (succ n) := tuple.append (tuple.repeat ff : bitvec n) [ tt ]

section shift

  -- shift left
  definition shl {n:ℕ} : bitvec n → ℕ → bitvec n
    | x i :=
       if le : i ≤ n then
         let eq := nat.sub_add_cancel le in
         cast (congr_arg bitvec eq) (tuple.append (dropn i x) (zero : bitvec i))
       else
         zero

  -- unsigned shift right
  definition ushr {n:ℕ} : bitvec n → ℕ → bitvec n
    | x i :=
      if le : i ≤ n then
        let y : bitvec (n-i) := @firstn _ _ _ (sub_le n i) x in
        let eq := calc (i+(n-i)) = (n - i) + i : nat.add_comm i (n - i)
                            ...  = n           : nat.sub_add_cancel le in
        cast (congr_arg bitvec eq) (tuple.append zero y)
      else
        zero

  -- signed shift right
  definition sshr {m:ℕ} : bitvec (succ m) → ℕ → bitvec (succ m)
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
  variable { n : ℕ }

  definition not : bitvec n → bitvec n := map bnot
  definition and : bitvec n → bitvec n → bitvec n := map₂ band
  definition or  : bitvec n → bitvec n → bitvec n := map₂ bor
  definition xor : bitvec n → bitvec n → bitvec n := map₂ bxor

end bitwise

section arith

  variable { n : ℕ }

  protected definition xor3 (x:bool) (y:bool) (c:bool) := bxor (bxor x y) c
  protected definition carry (x:bool) (y:bool) (c:bool) :=
    x && y || x && c || y && c

  definition neg : bitvec n → bitvec n
  | x :=
    let f := λy c, (y || c, bxor y c) in
    prod.snd (mapAccumR f x ff)

  -- Add with carry (no overflow)
  definition adc : bitvec n → bitvec n → bool → bitvec (n+1)
  | x y c :=
    let f := λx y c, (bitvec.carry x y c, bitvec.xor3 x y c) in
    let z := tuple.mapAccumR₂ f x y c in
    prod.fst z :: prod.snd z

  definition add : bitvec n → bitvec n → bitvec n
  | x y := tail (adc x y ff)

  protected definition borrow (x:bool) (y:bool) (b:bool) :=
    bnot x && y || bnot x && b || y && b

  -- Subtract with borrow
  definition sbb : bitvec n → bitvec n → bool → bool × bitvec n
  | x y b :=
    let f := λx y c, (bitvec.borrow x y c, bitvec.xor3 x y c) in
    tuple.mapAccumR₂ f x y b

  definition sub : bitvec n → bitvec n → bitvec n
  | x y := prod.snd (sbb x y ff)

  instance : has_zero (bitvec n) := has_zero.mk zero
  instance : has_one (bitvec (succ n)) := has_one.mk one
  instance : has_add (bitvec n)  := has_add.mk  add
  instance : has_sub (bitvec n)  := has_sub.mk  sub
  instance : has_neg (bitvec n)  := has_neg.mk  neg

  definition mul : bitvec n → bitvec n → bitvec n
  | x y :=
    let f := λr b, cond b (r + r + y) (r + r) in
    list.foldl f 0 (to_list x)

  instance : has_mul (bitvec n)  := has_mul.mk  mul
end arith

section comparison
  variable {n : ℕ}

  definition uborrow : bitvec n → bitvec n → bool := λx y, prod.fst (sbb x y ff)

  definition ult (x y : bitvec n) : Prop := uborrow x y = tt
  definition ugt (x y : bitvec n) : Prop := ult y x

  definition ule (x y : bitvec n) : Prop := ¬ (ult y x)
  definition uge : bitvec n → bitvec n → Prop := λx y, ule y x

  definition sborrow : bitvec (succ n) → bitvec (succ n) → bool := λx y,
     bool.cases_on
       (head x)
       (bool.cases_on (head y) (uborrow (tail x) (tail y)) tt)
       (bool.cases_on (head y) ff (uborrow (tail x) (tail y)))

  definition slt : bitvec (succ n) → bitvec (succ n) → Prop := λx y,
     sborrow x y = tt

  definition sgt : bitvec (succ n) → bitvec (succ n) → Prop := λx y, slt y x
  definition sle : bitvec (succ n) → bitvec (succ n) → Prop := λx y, ¬ (slt y x)
  definition sge : bitvec (succ n) → bitvec (succ n) → Prop := λx y, sle y x

end comparison

section from_bitvec
  variable {A : Type}

  -- Convert a bitvector to another number.
  definition from_bitvec [p : has_add A] [q0 : has_zero A] [q1 : has_one A] {n:nat} (v:bitvec n) : A :=
    let f : A → bool → A := λr b, cond b (r + r + 1) (r + r) in
    list.foldl f (0 : A) (to_list v)
end from_bitvec


end bitvec
