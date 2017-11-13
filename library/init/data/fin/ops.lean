/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.nat init.data.fin.basic

namespace fin
open nat
variable {n : nat}

protected def succ : fin n → fin (succ n)
| ⟨a, h⟩ := ⟨nat.succ a, succ_lt_succ h⟩

def of_nat {n : nat} (a : nat) : fin (succ n) :=
⟨a % succ n, nat.mod_lt _ (nat.zero_lt_succ _)⟩

private lemma mlt {n b : nat} : ∀ {a}, n > a → b % n < n
| 0     h := nat.mod_lt _ h
| (a+1) h :=
  have n > 0, from lt.trans (nat.zero_lt_succ _) h,
  nat.mod_lt _ this

protected def add : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(a + b) % n, mlt h⟩

protected def mul : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(a * b) % n, mlt h⟩

private lemma sublt {a b n : nat} (h : a < n) : a - b < n :=
lt_of_le_of_lt (nat.sub_le a b) h

protected def sub : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨a - b, sublt h⟩

private lemma modlt {a b n : nat} (h₁ : a < n) (h₂ : b < n) : a % b < n :=
begin
  cases b with b,
  {simp [mod_zero], assumption},
  {have h : a % (succ b) < succ b,
   apply nat.mod_lt _ (nat.zero_lt_succ _),
   exact lt.trans h h₂}
end

protected def mod : fin n → fin n → fin n
| ⟨a, h₁⟩ ⟨b, h₂⟩ := ⟨a % b, modlt h₁ h₂⟩

private lemma divlt {a b n : nat} (h : a < n) : a / b < n :=
lt_of_le_of_lt (nat.div_le_self a b) h

protected def div : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨a / b, divlt h⟩

instance : has_zero (fin (succ n)) := ⟨⟨0, succ_pos n⟩⟩
instance : has_one (fin (succ n))  := ⟨of_nat 1⟩
instance : has_add (fin n)         := ⟨fin.add⟩
instance : has_sub (fin n)         := ⟨fin.sub⟩
instance : has_mul (fin n)         := ⟨fin.mul⟩
instance : has_mod (fin n)         := ⟨fin.mod⟩
instance : has_div (fin n)         := ⟨fin.div⟩

lemma of_nat_zero : @of_nat n 0 = 0 := rfl

lemma add_def (a b : fin n) : (a + b).val = (a.val + b.val) % n :=
show (fin.add a b).val = (a.val + b.val) % n, from
by cases a; cases b; simp [fin.add]

lemma mul_def (a b : fin n) : (a * b).val = (a.val * b.val) % n :=
show (fin.mul a b).val = (a.val * b.val) % n, from
by cases a; cases b; simp [fin.mul]

lemma sub_def (a b : fin n) : (a - b).val = a.val - b.val :=
show (fin.sub a b).val = a.val - b.val, from
by cases a; cases b; simp [fin.sub]

lemma mod_def (a b : fin n) : (a % b).val = a.val % b.val :=
show (fin.mod a b).val = a.val % b.val, from
by cases a; cases b; simp [fin.mod]

lemma div_def (a b : fin n) : (a / b).val = a.val / b.val :=
show (fin.div a b).val = a.val / b.val, from
by cases a; cases b; simp [fin.div]

lemma lt_def (a b : fin n) : (a < b) = (a.val < b.val) :=
show (fin.lt a b) = (a.val < b.val), from
by cases a; cases b; simp [fin.lt]

lemma le_def (a b : fin n) : (a ≤ b) = (a.val ≤ b.val) :=
show (fin.le a b) = (a.val ≤ b.val), from
by cases a; cases b; simp [fin.le]

lemma val_zero : (0 : fin (succ n)).val = 0 := rfl

def pred {n : nat} : ∀ i : fin (succ n), i ≠ 0 → fin n
| ⟨a, h₁⟩ h₂ := ⟨a.pred,
  begin
    have this : a ≠ 0,
    { have aux₁ := vne_of_ne h₂,
      dsimp at aux₁, rw val_zero at aux₁, exact aux₁ },
    exact nat.pred_lt_pred this h₁
  end⟩

end fin
