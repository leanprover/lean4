/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The integers, with addition, multiplication, and subtraction.
-/
prelude
import init.data.nat.lemmas init.data.nat.gcd init.meta.transfer init.data.list
open nat

/- the type, coercions, and notation -/

@[derive decidable_eq]
inductive int : Type
| of_nat : nat → int
| neg_succ_of_nat : nat → int

notation `ℤ` := int

instance : has_coe nat int := ⟨int.of_nat⟩

notation `-[1+ ` n `]` := int.neg_succ_of_nat n

protected def int.repr : int → string
| (int.of_nat n)          := repr n
| (int.neg_succ_of_nat n) := "-" ++ repr (succ n)

instance : has_repr int :=
⟨int.repr⟩

instance : has_to_string int :=
⟨int.repr⟩

namespace int

protected lemma coe_nat_eq (n : ℕ) : ↑n = int.of_nat n := rfl

protected def zero : ℤ := of_nat 0
protected def one  : ℤ := of_nat 1

instance : has_zero ℤ := ⟨int.zero⟩
instance : has_one ℤ := ⟨int.one⟩

lemma of_nat_zero : of_nat (0 : nat) = (0 : int) := rfl

lemma of_nat_one : of_nat (1 : nat) = (1 : int) := rfl

/- definitions of basic functions -/

def neg_of_nat : ℕ → ℤ
| 0        := 0
| (succ m) := -[1+ m]

def sub_nat_nat (m n : ℕ) : ℤ :=
match (n - m : nat) with
| 0        := of_nat (m - n)  -- m ≥ n
| (succ k) := -[1+ k]         -- m < n, and n - m = succ k
end

protected def neg : ℤ → ℤ
| (of_nat n) := neg_of_nat n
| -[1+ n]    := succ n

protected def add : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m + n)
| (of_nat m) -[1+ n]    := sub_nat_nat m (succ n)
| -[1+ m]    (of_nat n) := sub_nat_nat n (succ m)
| -[1+ m]    -[1+ n]    := -[1+ succ (m + n)]

protected def mul : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m * n)
| (of_nat m) -[1+ n]    := neg_of_nat (m * succ n)
| -[1+ m]    (of_nat n) := neg_of_nat (succ m * n)
| -[1+ m]    -[1+ n]    := of_nat (succ m * succ n)

instance : has_neg ℤ := ⟨int.neg⟩
instance : has_add ℤ := ⟨int.add⟩
instance : has_mul ℤ := ⟨int.mul⟩

lemma of_nat_add (n m : ℕ) : of_nat (n + m) = of_nat n + of_nat m := rfl
lemma of_nat_mul (n m : ℕ) : of_nat (n * m) = of_nat n * of_nat m := rfl
lemma of_nat_succ (n : ℕ) : of_nat (succ n) = of_nat n + 1 := rfl

lemma neg_of_nat_zero : -(of_nat 0) = 0 := rfl
lemma neg_of_nat_of_succ (n : ℕ) : -(of_nat (succ n)) = -[1+ n] := rfl
lemma neg_neg_of_nat_succ (n : ℕ) : -(-[1+ n]) = of_nat (succ n) := rfl

lemma of_nat_eq_coe (n : ℕ) : of_nat n = ↑n := rfl
lemma neg_succ_of_nat_coe (n : ℕ) : -[1+ n] = -↑(n + 1) := rfl

protected lemma coe_nat_add (m n : ℕ) : (↑(m + n) : ℤ) = ↑m + ↑n := rfl
protected lemma coe_nat_mul (m n : ℕ) : (↑(m * n) : ℤ) = ↑m * ↑n := rfl
protected lemma coe_nat_zero : ↑(0 : ℕ) = (0 : ℤ) := rfl
protected lemma coe_nat_one : ↑(1 : ℕ) = (1 : ℤ) := rfl
protected lemma coe_nat_succ (n : ℕ) : (↑(succ n) : ℤ) = ↑n + 1 := rfl

protected lemma coe_nat_add_out (m n : ℕ) : ↑m + ↑n = (m + n : ℤ) := rfl
protected lemma coe_nat_mul_out (m n : ℕ) : ↑m * ↑n = (↑(m * n) : ℤ) := rfl
protected lemma coe_nat_add_one_out (n : ℕ) : ↑n + (1 : ℤ) = ↑(succ n) := rfl

/- injectivity of the constructor functions -/

protected lemma of_nat_inj {m n : ℕ} (h : of_nat m = of_nat n) : m = n :=
int.no_confusion h id

protected lemma coe_nat_inj {m n : ℕ} (h : (↑m : ℤ) = ↑n) : m = n :=
int.of_nat_inj h

lemma of_nat_eq_of_nat_iff (m n : ℕ) : of_nat m = of_nat n ↔ m = n :=
iff.intro int.of_nat_inj (congr_arg _)

protected lemma coe_nat_eq_coe_nat_iff (m n : ℕ) : (↑m : ℤ) = ↑n ↔ m = n :=
of_nat_eq_of_nat_iff m n

lemma neg_succ_of_nat_inj {m n : ℕ} (h : neg_succ_of_nat m = neg_succ_of_nat n) : m = n :=
int.no_confusion h id

lemma neg_succ_of_nat_inj_iff {m n : ℕ} : neg_succ_of_nat m = neg_succ_of_nat n ↔ m = n :=
⟨neg_succ_of_nat_inj, assume H, by simp [H]⟩

lemma neg_succ_of_nat_eq (n : ℕ) : -[1+ n] = -(n + 1) := rfl

/- basic properties of sub_nat_nat -/

lemma sub_nat_nat_elim (m n : ℕ) (P : ℕ → ℕ → ℤ → Prop)
  (hp : ∀i n, P (n + i) n (of_nat i))
  (hn : ∀i m, P m (m + i + 1) (-[1+ i])) :
  P m n (sub_nat_nat m n) :=
begin
  have H : ∀k, n - m = k → P m n (nat.cases_on k (of_nat (m - n)) (λa, -[1+ a])),
  { intro k, cases k,
    { intro e,
      cases (nat.le.dest (nat.le_of_sub_eq_zero e)) with k h,
      rw [h.symm, nat.add_sub_cancel_left],
      apply hp },
    { intro heq,
      have h : m ≤ n,
      { exact nat.le_of_lt (nat.lt_of_sub_eq_succ heq) },
      rw [nat.sub_eq_iff_eq_add h] at heq,
      rw [heq, add_comm],
      apply hn } },
  delta sub_nat_nat,
  exact H _ rfl
end

private lemma sub_nat_nat_add_left {m n : ℕ} :
  sub_nat_nat (m + n) m = of_nat n :=
begin
  dunfold sub_nat_nat,
  rw [nat.sub_eq_zero_of_le],
  dunfold sub_nat_nat._match_1,
  rw [nat.add_sub_cancel_left],
  apply nat.le_add_right
end

private lemma sub_nat_nat_add_right {m n : ℕ} :
  sub_nat_nat m (m + n + 1) = neg_succ_of_nat n :=
calc sub_nat_nat._match_1 m (m + n + 1) (m + n + 1 - m) =
        sub_nat_nat._match_1 m (m + n + 1) (m + (n + 1) - m) : by simp
  ... = sub_nat_nat._match_1 m (m + n + 1) (n + 1) : by rw [nat.add_sub_cancel_left]
  ... = neg_succ_of_nat n : rfl

private lemma sub_nat_nat_add_add (m n k : ℕ) : sub_nat_nat (m + k) (n + k) = sub_nat_nat m n :=
sub_nat_nat_elim m n (λm n i, sub_nat_nat (m + k) (n + k) = i)
  (assume i n, have n + i + k = (n + k) + i, by simp,
    begin rw [this], exact sub_nat_nat_add_left end)
  (assume i m, have m + i + 1 + k = (m + k) + i + 1, by simp,
    begin rw [this], exact sub_nat_nat_add_right end)

/- nat_abs -/

@[simp] def nat_abs : ℤ → ℕ
| (of_nat m) := m
| -[1+ m]    := succ m

lemma nat_abs_of_nat (n : ℕ) : nat_abs ↑n = n := rfl

lemma eq_zero_of_nat_abs_eq_zero : Π {a : ℤ}, nat_abs a = 0 → a = 0
| (of_nat m) H := congr_arg of_nat H
| -[1+ m']   H := absurd H (succ_ne_zero _)

lemma nat_abs_pos_of_ne_zero {a : ℤ} (h : a ≠ 0) : nat_abs a > 0 :=
(eq_zero_or_pos _).resolve_left $ mt eq_zero_of_nat_abs_eq_zero h

lemma nat_abs_zero : nat_abs (0 : int) = (0 : nat) := rfl

lemma nat_abs_one : nat_abs (1 : int) = (1 : nat) := rfl

lemma nat_abs_mul_self : Π {a : ℤ}, ↑(nat_abs a * nat_abs a) = a * a
| (of_nat m) := rfl
| -[1+ m']   := rfl

@[simp] lemma nat_abs_neg (a : ℤ) : nat_abs (-a) = nat_abs a :=
by {cases a with n n, cases n; refl, refl}

lemma nat_abs_eq : Π (a : ℤ), a = nat_abs a ∨ a = -(nat_abs a)
| (of_nat m) := or.inl rfl
| -[1+ m']   := or.inr rfl

lemma eq_coe_or_neg (a : ℤ) : ∃n : ℕ, a = n ∨ a = -n := ⟨_, nat_abs_eq a⟩

/- sign -/

def sign : ℤ → ℤ
| (n+1:ℕ) := 1
| 0       := 0
| -[1+ n] := -1

@[simp] theorem sign_zero : sign 0 = 0 := rfl
@[simp] theorem sign_one : sign 1 = 1 := rfl
@[simp] theorem sign_neg_one : sign (-1) = -1 := rfl

/- Quotient and remainder -/

-- There are three main conventions for integer division,
-- referred here as the E, F, T rounding conventions.
-- All three pairs satisfy the identity x % y + (x / y) * y = x
-- unconditionally.

-- E-rounding: This pair satisfies 0 ≤ mod x y < nat_abs y for y ≠ 0
protected def div : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := of_nat (m / n)
| (m : ℕ) -[1+ n] := -of_nat (m / succ n)
| -[1+ m] 0       := 0
| -[1+ m] (n+1:ℕ) := -[1+ m / succ n]
| -[1+ m] -[1+ n] := of_nat (succ (m / succ n))

protected def mod : ℤ → ℤ → ℤ
| (m : ℕ) n := (m % nat_abs n : ℕ)
| -[1+ m] n := sub_nat_nat (nat_abs n) (succ (m % nat_abs n))

-- F-rounding: This pair satisfies fdiv x y = floor (x / y)
def fdiv : ℤ → ℤ → ℤ
| 0       _       := 0
| (m : ℕ) (n : ℕ) := of_nat (m / n)
| (m+1:ℕ) -[1+ n] := -[1+ m / succ n]
| -[1+ m] 0       := 0
| -[1+ m] (n+1:ℕ) := -[1+ m / succ n]
| -[1+ m] -[1+ n] := of_nat (succ m / succ n)

def fmod : ℤ → ℤ → ℤ
| 0       _       := 0
| (m : ℕ) (n : ℕ) := of_nat (m % n)
| (m+1:ℕ) -[1+ n] := sub_nat_nat (m % succ n) n
| -[1+ m] (n : ℕ) := sub_nat_nat n (succ (m % n))
| -[1+ m] -[1+ n] := -of_nat (succ m % succ n)

-- T-rounding: This pair satisfies quot x y = round_to_zero (x / y)
def quot : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m / n)
| (of_nat m) -[1+ n]    := -of_nat (m / succ n)
| -[1+ m]    (of_nat n) := -of_nat (succ m / n)
| -[1+ m]    -[1+ n]    := of_nat (succ m / succ n)

def rem : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m % n)
| (of_nat m) -[1+ n]    := of_nat (m % succ n)
| -[1+ m]    (of_nat n) := -of_nat (succ m % n)
| -[1+ m]    -[1+ n]    := -of_nat (succ m % succ n)

instance : has_div ℤ := ⟨int.div⟩
instance : has_mod ℤ := ⟨int.mod⟩

/- gcd -/

def gcd (m n : ℤ) : ℕ := gcd (nat_abs m) (nat_abs n)

/-- Relator between integers and pairs of natural numbers -/

inductive rel_int_nat_nat : ℤ → ℕ × ℕ → Prop
| pos : ∀{m p}, rel_int_nat_nat (of_nat p) (m + p, m)
| neg : ∀{m n}, rel_int_nat_nat (neg_succ_of_nat n) (m, m + n + 1)

protected lemma rel_sub_nat_nat {a b : ℕ} : rel_int_nat_nat (sub_nat_nat a b) (a, b) :=
sub_nat_nat_elim a b (λa b i, rel_int_nat_nat i (a, b))
  (assume i n, rel_int_nat_nat.pos) (assume i n, rel_int_nat_nat.neg)

instance right_total_rel_int_nat_nat : relator.right_total rel_int_nat_nat
| (n, m) := ⟨_, int.rel_sub_nat_nat⟩

instance left_total_rel_int_nat_nat : relator.left_total rel_int_nat_nat
| (of_nat n) := ⟨(0 + n, 0), rel_int_nat_nat.pos⟩
| (neg_succ_of_nat n) := ⟨(0, 0 + n + 1), rel_int_nat_nat.neg⟩

instance bi_total_rel_int_nat_nat : relator.bi_total rel_int_nat_nat :=
⟨int.left_total_rel_int_nat_nat, int.right_total_rel_int_nat_nat⟩

protected lemma rel_neg_of_nat {m} : ∀{n}, rel_int_nat_nat (neg_of_nat n) (m, m + n)
| 0 := rel_int_nat_nat.pos
| (nat.succ n) := rel_int_nat_nat.neg

protected lemma rel_eq : (rel_int_nat_nat ⇒ (rel_int_nat_nat ⇒ iff))
  eq (λa b, a.1 + b.2 = b.1 + a.2)
| ._ ._ (@rel_int_nat_nat.pos m p) ._ ._ (@rel_int_nat_nat.pos m' p') :=
  calc of_nat p = of_nat p'
        ↔ (m + m') + p = (m + m') + p' : by rw [of_nat_eq_of_nat_iff, add_left_cancel_iff]
    ... ↔ (m + p) + m' = (m' + p') + m : by simp
| ._ ._ (@rel_int_nat_nat.pos m p) ._ ._ (@rel_int_nat_nat.neg m' n') :=
  calc of_nat p = -[1+ n'] ↔ (m' + m) + (n' + p + 1) = (m' + m) + 0 :
     begin rw [add_left_cancel_iff], apply iff.intro; intro; contradiction end
   ... ↔ (m + p) + (m' + n' + 1) = m' + m : by simp
| ._ ._ (@rel_int_nat_nat.neg m n) ._ ._ (@rel_int_nat_nat.pos m' p') :=
  calc -[1+ n] = of_nat p' ↔ (m + m') + 0 = (m + m') + (n + p' + 1) :
     begin rw [add_left_cancel_iff], apply iff.intro; intro; contradiction end
   ... ↔ m + m' = m' + p' + (m + n + 1) : by simp
| ._ ._ (@rel_int_nat_nat.neg m n) ._ ._ (@rel_int_nat_nat.neg m' n') :=
  calc -[1+ n] = -[1+ n'] ↔ (m + m' + 1) + n' = (m + m' + 1) + n :
      by rw [neg_succ_of_nat_inj_iff, add_left_cancel_iff, eq_comm]
    ... ↔ m + (m' + n' + 1) = m' + (m + n + 1) : by simp

/- should this be more general, i.e. ∀{n}, rel_int_nat_nat 0 (n, n) ? -/
protected lemma rel_zero : rel_int_nat_nat 0 (0, 0) :=
rel_int_nat_nat.pos

protected lemma rel_one : rel_int_nat_nat 1 (1, 0) :=
rel_int_nat_nat.pos

protected lemma rel_neg : (rel_int_nat_nat ⇒ rel_int_nat_nat) has_neg.neg (λa, (a.2, a.1))
| ._ ._ (@rel_int_nat_nat.pos m p) := int.rel_neg_of_nat
| ._ ._ (@rel_int_nat_nat.neg m n) := rel_int_nat_nat.pos

protected lemma rel_add : (rel_int_nat_nat ⇒ (rel_int_nat_nat ⇒ rel_int_nat_nat))
  has_add.add (λa b, (a.1 + b.1, a.2 + b.2))
| ._ ._ (@rel_int_nat_nat.pos m p) ._ ._ (@rel_int_nat_nat.pos m' p') :=
  have eq : m + p + (m' + p') = m + m' + (p + p'),
    by simp,
  show rel_int_nat_nat (of_nat (p + p')) (m + p + (m' + p'), m + m'),
    begin rw [eq], apply rel_int_nat_nat.pos end
| ._ ._ (@rel_int_nat_nat.pos m p) ._ ._ (@rel_int_nat_nat.neg m' n') :=
  have eq1 : m + p + m' = p + (m + m'),
    by simp,
  have eq2 : m + (m' + n' + 1) = (n' + 1) + (m + m'),
    by simp,
  show rel_int_nat_nat (sub_nat_nat p (n' + 1)) (m + p + m', m + (m' + n' + 1)),
    begin
      rw [eq1, eq2, (sub_nat_nat_add_add _ _ (m + m')).symm],
      apply int.rel_sub_nat_nat
    end
| ._ ._ (@rel_int_nat_nat.neg m n) ._ ._ (@rel_int_nat_nat.pos m' p') :=
  have eq1 : m + (m' + p') = p' + (m + m'),
    by simp,
  have eq2 : (m + n + 1) + m' = (n + 1) + (m + m'),
    by simp,
  show rel_int_nat_nat (sub_nat_nat p' (n + 1)) (m + (m' + p'), (m + n + 1) + m'),
    begin
      rw [eq1, eq2, (sub_nat_nat_add_add _ _ (m + m')).symm],
      apply int.rel_sub_nat_nat
    end
| ._ ._ (@rel_int_nat_nat.neg m n) ._ ._ (@rel_int_nat_nat.neg m' n') :=
  have eq :  (m + n + 1) + (m' + n' + 1) = (m + m') + (n + n' + 1) + 1,
    by simp,
  show rel_int_nat_nat -[1+ (n + n' + 1)] (m + m', (m + n + 1) + (m' + n' + 1)),
    begin rw [eq], apply rel_int_nat_nat.neg end

protected lemma rel_mul : (rel_int_nat_nat ⇒ (rel_int_nat_nat ⇒ rel_int_nat_nat))
  has_mul.mul (λa b, (a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1))
| ._ ._ (@rel_int_nat_nat.pos m p) ._ ._ (@rel_int_nat_nat.pos m' p') :=
  have e : (m + p) * (m' + p') + m * m' = (m + p) * m' + m * (m' + p') + p * p',
    by simp [mul_add, add_mul],
  show rel_int_nat_nat (of_nat (p * p'))
      ((m + p) * (m' + p') + m * m', (m + p) * m' + m * (m' + p')),
    begin rw [e], exact rel_int_nat_nat.pos end
| ._ ._ (@rel_int_nat_nat.pos m p) ._ ._ (@rel_int_nat_nat.neg m' n') :=
  have e : (m + p) * (m' + n' + 1) + m * m' = (m + p) * m' + m * (m' + n' + 1) + (p * (n' + 1)),
    by simp [mul_add, add_mul],
  show rel_int_nat_nat (of_nat p * -[1+ n'])
      ((m + p) * m' + m * (m' + n' + 1), (m + p) * (m' + n' + 1) + m * m'),
    begin rw [e], exact int.rel_neg_of_nat end
| ._ ._ (@rel_int_nat_nat.neg m n) ._ ._ (@rel_int_nat_nat.pos m' p') :=
  have e : m * m' + (m + n + 1) * (m' + p') = m * (m' + p') + (m + n + 1) * m' + ((n + 1) * p'),
    by simp [mul_add, add_mul],
  show rel_int_nat_nat (-[1+ n] * of_nat p')
      (m * (m' + p') + (m + n + 1) * m',  m * m' + (m + n + 1) * (m' + p')),
    begin rw [e], exact int.rel_neg_of_nat end
| ._ ._ (@rel_int_nat_nat.neg m n) ._ ._ (@rel_int_nat_nat.neg m' n') :=
  have e : m * m' + (m + n + 1) * (m' + n' + 1) =
      m * (m' + n' + 1) + (m + n + 1) * m' + ((n + 1) * (n' + 1)),
    by simp [mul_add, add_mul],
  show rel_int_nat_nat (-[1+ n] * -[1+ n'])
      (m * m' + (m + n + 1) * (m' + n' + 1), m * (m' + n' + 1) + (m + n + 1) * m'),
    begin rw [e], exact rel_int_nat_nat.pos end

/-
   int is a ring
-/

protected meta def transfer_core : tactic unit := do
  transfer.transfer [`relator.rel_forall_of_total, `relator.rel_not,
    `int.rel_eq, `int.rel_zero, `int.rel_one,
    `int.rel_add, `int.rel_neg, `int.rel_mul]

protected meta def transfer (distrib := tt) : tactic unit :=
if distrib then `[int.transfer_core, simp [add_mul, mul_add]]
else `[int.transfer_core, simp]

local attribute [simp] mul_assoc mul_comm mul_left_comm

instance : comm_ring int :=
{ add            := int.add,
  add_assoc      := by int.transfer,
  zero           := int.zero,
  zero_add       := by int.transfer,
  add_zero       := by int.transfer,
  neg            := int.neg,
  add_left_neg   := by int.transfer,
  add_comm       := by int.transfer,
  mul            := int.mul,
  mul_assoc      := by int.transfer tt,
  one            := int.one,
  one_mul        := by int.transfer,
  mul_one        := by int.transfer,
  left_distrib   := by int.transfer tt,
  right_distrib  := by int.transfer tt,
  mul_comm       := by int.transfer}

/- Extra instances to short-circuit type class resolution -/
instance : has_sub int            := by apply_instance
instance : add_comm_monoid int    := by apply_instance
instance : add_monoid int         := by apply_instance
instance : monoid int             := by apply_instance
instance : comm_monoid int        := by apply_instance
instance : comm_semigroup int     := by apply_instance
instance : semigroup int          := by apply_instance
instance : add_comm_semigroup int := by apply_instance
instance : add_semigroup int      := by apply_instance
instance : comm_semiring int      := by apply_instance
instance : semiring int           := by apply_instance
instance : ring int               := by apply_instance
instance : distrib int            := by apply_instance

instance : zero_ne_one_class ℤ :=
{ zero := 0, one := 1, zero_ne_one := by int.transfer }

lemma of_nat_sub {n m : ℕ} (h : m ≤ n) : of_nat (n - m) = of_nat n - of_nat m :=
show of_nat (n - m) = of_nat n + neg_of_nat m, from match m, h with
| 0, h := rfl
| succ m, h := show of_nat (n - succ m) = sub_nat_nat n (succ m),
  by delta sub_nat_nat; rw sub_eq_zero_of_le h; refl
end

lemma neg_succ_of_nat_coe' (n : ℕ) : -[1+ n] = -↑n - 1 :=
by rw [sub_eq_add_neg, ← neg_add]; refl

protected lemma coe_nat_sub {n m : ℕ} : n ≤ m → (↑(m - n) : ℤ) = ↑m - ↑n := of_nat_sub

protected lemma sub_nat_nat_eq_coe {m n : ℕ} : sub_nat_nat m n = ↑m - ↑n :=
sub_nat_nat_elim m n (λm n i, i = ↑m - ↑n)
  (λi n, by simp [int.coe_nat_add]; refl)
  (λi n, by simp [int.coe_nat_add, int.coe_nat_one, int.neg_succ_of_nat_eq];
            apply congr_arg; rw[add_left_comm]; simp)

def to_nat : ℤ → ℕ
| (n : ℕ) := n
| -[1+ n] := 0

theorem to_nat_sub (m n : ℕ) : to_nat (m - n) = m - n :=
by rw [← int.sub_nat_nat_eq_coe]; exact sub_nat_nat_elim m n
  (λm n i, to_nat i = m - n)
  (λi n, by rw [nat.add_sub_cancel_left]; refl)
  (λi n, by rw [add_assoc, nat.sub_eq_zero_of_le (nat.le_add_right _ _)]; refl)

-- Since mod x y is always nonnegative when y ≠ 0, we can make a nat version of it
def nat_mod (m n : ℤ) : ℕ := (m % n).to_nat

theorem sign_mul_nat_abs : ∀ (a : ℤ), sign a * nat_abs a = a
| (n+1:ℕ) := one_mul _
| 0       := rfl
| -[1+ n] := (neg_eq_neg_one_mul _).symm

end int
