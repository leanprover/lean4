/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/

prelude
import init.data.int.basic init.data.nat.bitwise

universe u

namespace int

  def div2 : ℤ → ℤ
  | (of_nat n) := n.div2
  | -[1+ n] := -[1+ n.div2]

  def bodd : ℤ → bool
  | (of_nat n) := n.bodd
  | -[1+ n] := bnot (n.bodd)

  def bit (b : bool) : ℤ → ℤ := cond b bit1 bit0

  def test_bit : ℤ → ℕ → bool
  | (m : ℕ) n := nat.test_bit m n
  | -[1+ m] n := bnot (nat.test_bit m n)

  def nat_bitwise (f : bool → bool → bool) (m n : ℕ) : ℤ :=
  cond (f ff ff) -[1+ nat.bitwise (λx y, bnot (f x y)) m n] (nat.bitwise f m n)

  def bitwise (f : bool → bool → bool) : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat_bitwise f m n
  | (m : ℕ) -[1+ n] := nat_bitwise (λ x y, f x (bnot y)) m n
  | -[1+ m] (n : ℕ) := nat_bitwise (λ x y, f (bnot x) y) m n
  | -[1+ m] -[1+ n] := nat_bitwise (λ x y, f (bnot x) (bnot y)) m n

  def lnot : ℤ → ℤ
  | (m : ℕ) := -[1+ m]
  | -[1+ m] := m

  def lor : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.lor m n
  | (m : ℕ) -[1+ n] := -[1+ nat.ldiff n m]
  | -[1+ m] (n : ℕ) := -[1+ nat.ldiff m n]
  | -[1+ m] -[1+ n] := -[1+ nat.land m n]

  def land : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.land m n
  | (m : ℕ) -[1+ n] := nat.ldiff m n
  | -[1+ m] (n : ℕ) := nat.ldiff n m
  | -[1+ m] -[1+ n] := -[1+ nat.lor m n]

  def ldiff : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.ldiff m n
  | (m : ℕ) -[1+ n] := nat.land m n
  | -[1+ m] (n : ℕ) := -[1+ nat.lor m n]
  | -[1+ m] -[1+ n] := nat.ldiff n m

  def lxor : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.lxor m n
  | (m : ℕ) -[1+ n] := -[1+ nat.lxor m n]
  | -[1+ m] (n : ℕ) := -[1+ nat.lxor m n]
  | -[1+ m] -[1+ n] := nat.lxor m n

  def shiftl : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.shiftl m n
  | (m : ℕ) -[1+ n] := nat.shiftr m (nat.succ n)
  | -[1+ m] (n : ℕ) := -[1+ nat.shiftl' tt m n]
  | -[1+ m] -[1+ n] := -[1+ nat.shiftr m (nat.succ n)]

  def shiftr (m n : ℤ) : ℤ := shiftl m (-n)

end int
