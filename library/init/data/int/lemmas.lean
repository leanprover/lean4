/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro

Definitions and properties of div and mod, following the SSReflect library.

Following SSReflect and the SMTlib standard, we define a % b so that 0 ≤ a % b < |b| when b ≠ 0.
-/
prelude
import init.data.int.order init.data.nat.div

namespace int

/- /  -/

theorem of_nat_div (m n : nat) : of_nat (m / n) = (of_nat m) / (of_nat n) := rfl

theorem neg_succ_of_nat_div (m : nat) {b : ℤ} (H : b > 0) :
  -[1+m] / b = -(m / b + 1) :=
match b, eq_succ_of_zero_lt H with ._, ⟨n, rfl⟩ := rfl end

set_option type_context.unfold_lemmas true
@[simp] protected theorem div_neg : ∀ (a b : ℤ), a / -b = -(a / b)
| (m : ℕ) 0       := show of_nat (m / 0) = -(m / 0 : ℕ), by rw nat.div_zero; refl
| (m : ℕ) (n+1:ℕ) := rfl
| 0       -[1+ n] := rfl
| (m+1:ℕ) -[1+ n] := (neg_neg _).symm
| -[1+ m] 0       := rfl
| -[1+ m] (n+1:ℕ) := rfl
| -[1+ m] -[1+ n] := rfl


theorem div_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : b > 0) : a / b = -((-a - 1) / b + 1) :=
match a, b, eq_neg_succ_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩ :=
  by change (- -[1+ m] : ℤ) with (m+1 : ℤ); rw add_sub_cancel; refl
end

protected theorem div_nonneg {a b : ℤ} (Ha : a ≥ 0) (Hb : b ≥ 0) : a / b ≥ 0 :=
match a, b, eq_coe_of_zero_le Ha, eq_coe_of_zero_le Hb with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩ := coe_zero_le _
end

protected theorem div_nonpos {a b : ℤ} (Ha : a ≥ 0) (Hb : b ≤ 0) : a / b ≤ 0 :=
nonpos_of_neg_nonneg $ by rw -int.div_neg; exact int.div_nonneg Ha (neg_nonneg_of_nonpos Hb)

theorem div_neg' {a b : ℤ} (Ha : a < 0) (Hb : b > 0) : a / b < 0 :=
match a, b, eq_neg_succ_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩ := neg_succ_lt_zero _
end

@[simp] protected theorem zero_div : ∀ (b : ℤ), 0 / b = 0
| 0       := rfl
| (n+1:ℕ) := rfl
| -[1+ n] := rfl

@[simp] protected theorem div_zero : ∀ (a : ℤ), a / 0 = 0
| 0       := rfl
| (n+1:ℕ) := rfl
| -[1+ n] := rfl

@[simp] protected theorem div_one : ∀ (a : ℤ), a / 1 = a
| 0       := rfl
| (n+1:ℕ) := congr_arg of_nat (nat.div_one _)
| -[1+ n] := congr_arg neg_succ_of_nat (nat.div_one _)

theorem div_eq_zero_of_lt {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a / b = 0 :=
match a, b, eq_coe_of_zero_le H1, eq_succ_of_zero_lt (lt_of_le_of_lt H1 H2), H2  with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩, H2 :=
  congr_arg of_nat $ nat.div_eq_of_lt $ lt_of_coe_nat_lt_coe_nat H2
end

theorem div_eq_zero_of_lt_abs {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < abs b) : a / b = 0 :=
match b, abs b, abs_eq_nat_abs b, H2 with
| (n : ℕ), ._, rfl, H2 := div_eq_zero_of_lt H1 H2
| -[1+ n], ._, rfl, H2 := neg_inj $ by rw -int.div_neg; exact div_eq_zero_of_lt H1 H2
end

protected theorem add_mul_div_right (a b : ℤ) {c : ℤ} (H : c ≠ 0) :
  (a + b * c) / c = a / c + b :=
have ∀ {k n : ℕ} {a : ℤ}, (a + n * k.succ) / k.succ = a / k.succ + n, from
λ k n a, match a with
| (m : ℕ) := congr_arg of_nat $ nat.add_mul_div_right _ _ k.succ_pos
| -[1+ m] := show ((n * k.succ:ℕ) - m.succ : ℤ) / k.succ =
                  n - (m / k.succ + 1 : ℕ), begin
  cases lt_or_ge m (n*k.succ) with h h,
  { rw [-int.coe_nat_sub h,
        -int.coe_nat_sub ((nat.div_lt_iff_lt_mul _ _ k.succ_pos).2 h)],
    apply congr_arg of_nat,
    rw [mul_comm, nat.mul_sub_div], rwa mul_comm },
  { change (↑(n * nat.succ k) - (m + 1) : ℤ) / ↑(nat.succ k) =
           ↑n - ((m / nat.succ k : ℕ) + 1),
    rw [-sub_sub, -sub_sub, -neg_sub (m:ℤ), -neg_sub _ (n:ℤ),
        -int.coe_nat_sub h,
        -int.coe_nat_sub ((nat.le_div_iff_mul_le _ _ k.succ_pos).2 h),
        -neg_succ_of_nat_coe', -neg_succ_of_nat_coe'],
    { apply congr_arg neg_succ_of_nat,
      rw [mul_comm, nat.sub_mul_div], rwa mul_comm } }
  end
end,
have ∀ {a b c : ℤ}, c > 0 → (a + b * c) / c = a / c + b, from
λ a b c H, match c, eq_succ_of_zero_lt H, b with
| ._, ⟨k, rfl⟩, (n : ℕ) := this
| ._, ⟨k, rfl⟩, -[1+ n] :=
  show (a - n.succ * k.succ) / k.succ = (a / k.succ) - n.succ, from
  eq_sub_of_add_eq $ by rw [-this, sub_add_cancel]
end,
match lt_trichotomy c 0 with
| or.inl hlt          := neg_inj $ by rw [-int.div_neg, neg_add, -int.div_neg, -neg_mul_neg];
                         apply this (neg_pos_of_neg hlt)
| or.inr (or.inl heq) := absurd heq H
| or.inr (or.inr hgt) := this hgt
end

protected theorem add_mul_div_left (a : ℤ) {b : ℤ} (c : ℤ) (H : b ≠ 0) :
    (a + b * c) / b = a / b + c :=
by rw [mul_comm, int.add_mul_div_right _ _ H]

@[simp] protected theorem mul_div_cancel (a : ℤ) {b : ℤ} (H : b ≠ 0) : a * b / b = a :=
by have := int.add_mul_div_right 0 a H;
   rwa [zero_add, int.zero_div, zero_add] at this

@[simp] protected theorem mul_div_cancel_left {a : ℤ} (b : ℤ) (H : a ≠ 0) : a * b / a = b :=
by rw [mul_comm, int.mul_div_cancel _ H]

@[simp] protected theorem div_self {a : ℤ} (H : a ≠ 0) : a / a = 1 :=
by have := int.mul_div_cancel 1 H; rwa one_mul at this

/- mod -/

theorem of_nat_mod (m n : nat) : (m % n : ℤ) = of_nat (m % n) := rfl

theorem neg_succ_of_nat_mod (m : ℕ) {b : ℤ} (bpos : b > 0) :
  -[1+m] % b = b - 1 - m % b :=
by rw [sub_sub, add_comm]; exact
match b, eq_succ_of_zero_lt bpos with ._, ⟨n, rfl⟩ := rfl end

@[simp] theorem mod_neg : ∀ (a b : ℤ), a % -b = a % b
| (m : ℕ) n := @congr_arg ℕ ℤ _ _ (λ i, ↑(m % i)) (nat_abs_neg _)
| -[1+ m] n := @congr_arg ℕ ℤ _ _ (λ i, sub_nat_nat i (nat.succ (m % i))) (nat_abs_neg _)

@[simp] theorem mod_abs (a b : ℤ) : a % (abs b) = a % b :=
abs_by_cases (λ i, a % i = a % b) rfl (mod_neg _ _)

@[simp] theorem zero_mod (b : ℤ) : 0 % b = 0 :=
congr_arg of_nat $ nat.zero_mod _

@[simp] theorem mod_zero : ∀ (a : ℤ), a % 0 = a
| (m : ℕ) := congr_arg of_nat $ nat.mod_zero _
| -[1+ m] := congr_arg neg_succ_of_nat $ nat.mod_zero _

@[simp] theorem mod_one : ∀ (a : ℤ), a % 1 = 0
| (m : ℕ) := congr_arg of_nat $ nat.mod_one _
| -[1+ m] := show (1 - (m % 1).succ : ℤ) = 0, by rw nat.mod_one; refl

theorem mod_eq_of_lt {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a % b = a :=
match a, b, eq_coe_of_zero_le H1, eq_coe_of_zero_le (le_trans H1 (le_of_lt H2)), H2 with
| ._, ._, ⟨m, rfl⟩, ⟨n, rfl⟩, H2 :=
  congr_arg of_nat $ nat.mod_eq_of_lt (lt_of_coe_nat_lt_coe_nat H2)
end

theorem mod_nonneg : ∀ (a : ℤ) {b : ℤ}, b ≠ 0 → a % b ≥ 0
| (m : ℕ) n H := coe_zero_le _
| -[1+ m] n H :=
  sub_nonneg_of_le $ coe_nat_le_coe_nat_of_le $ nat.mod_lt _ (nat_abs_pos_of_ne_zero H)

theorem mod_lt_of_pos (a : ℤ) {b : ℤ} (H : b > 0) : a % b < b :=
match a, b, eq_succ_of_zero_lt H with
| (m : ℕ), ._, ⟨n, rfl⟩ := coe_nat_lt_coe_nat_of_lt (nat.mod_lt _ (nat.succ_pos _))
| -[1+ m], ._, ⟨n, rfl⟩ := sub_lt_self _ (coe_nat_lt_coe_nat_of_lt $ nat.succ_pos _)
end

theorem mod_lt (a : ℤ) {b : ℤ} (H : b ≠ 0) : a % b < abs b :=
by rw -mod_abs; exact mod_lt_of_pos _ (abs_pos_of_ne_zero H)

lemma mod_add_div_aux (m n : ℕ) : (n - (m % n + 1) - (n * (m / n) + n) : ℤ) = -[1+ m] :=
begin
  rw [-sub_sub, neg_succ_of_nat_coe, sub_sub (n:ℤ)],
  apply eq_neg_of_eq_neg,
  rw [neg_sub, sub_sub_self, add_right_comm],
  exact @congr_arg ℕ ℤ _ _ (λi, (i + 1 : ℤ)) (nat.mod_add_div _ _).symm
end

theorem mod_add_div : ∀ (a b : ℤ), a % b + b * (a / b) = a
| (m : ℕ) 0       := congr_arg of_nat (nat.mod_add_div _ _)
| (m : ℕ) (n+1:ℕ) := congr_arg of_nat (nat.mod_add_div _ _)
| 0       -[1+ n] := rfl
| (m+1:ℕ) -[1+ n] := show (_ + -(n+1) * -((m + 1) / (n + 1) : ℕ) : ℤ) = _,
  by rw [neg_mul_neg]; exact congr_arg of_nat (nat.mod_add_div _ _)
| -[1+ m] 0       := by rw [mod_zero, int.div_zero]; refl
| -[1+ m] (n+1:ℕ) := mod_add_div_aux m n.succ
| -[1+ m] -[1+ n] := mod_add_div_aux m n.succ

theorem mod_def (a b : ℤ) : a % b = a - b * (a / b) :=
eq_sub_of_add_eq (mod_add_div _ _)

@[simp] theorem add_mul_mod_self {a b c : ℤ} : (a + b * c) % c = a % c :=
if cz : c = 0 then by rw [cz, mul_zero, add_zero] else
by rw [mod_def, mod_def, int.add_mul_div_right _ _ cz,
       mul_add, mul_comm, add_sub_add_right_eq_sub]

@[simp] theorem add_mul_mod_self_left (a b c : ℤ) : (a + b * c) % b = a % b :=
by rw [mul_comm, add_mul_mod_self]

@[simp] theorem add_mod_self {a b : ℤ} : (a + b) % b = a % b :=
by have := add_mul_mod_self_left a b 1; rwa mul_one at this

@[simp] theorem add_mod_self_left {a b : ℤ} : (a + b) % a = b % a :=
by rw [add_comm, add_mod_self]

@[simp] theorem mod_add_mod (m n k : ℤ) : (m % n + k) % n = (m + k) % n :=
by have := (add_mul_mod_self_left (m % n + k) n (m / n)).symm;
   rwa [add_right_comm, mod_add_div] at this

@[simp] theorem add_mod_mod (m n k : ℤ) : (m + n % k) % k = (m + n) % k :=
by rw [add_comm, mod_add_mod, add_comm]

theorem add_mod_eq_add_mod_right {m n k : ℤ} (i : ℤ) (H : m % n = k % n) :
  (m + i) % n = (k + i) % n :=
by rw [-mod_add_mod, -mod_add_mod k, H]

theorem add_mod_eq_add_mod_left {m n k : ℤ} (i : ℤ) (H : m % n = k % n) :
  (i + m) % n = (i + k) % n :=
by rw [add_comm, add_mod_eq_add_mod_right _ H, add_comm]

theorem mod_eq_mod_of_add_mod_eq_add_mod_right {m n k i : ℤ}
    (H : (m + i) % n = (k + i) % n) :
  m % n = k % n :=
by have := add_mod_eq_add_mod_right (-i) H;
   rwa [add_neg_cancel_right, add_neg_cancel_right] at this

theorem mod_eq_mod_of_add_mod_eq_add_mod_left {m n k i : ℤ} :
  (i + m) % n = (i + k) % n → m % n = k % n :=
by rw [add_comm, add_comm i]; apply mod_eq_mod_of_add_mod_eq_add_mod_right

@[simp] theorem mul_mod_left (a b : ℤ) : (a * b) % b = 0 :=
by rw [-zero_add (a * b), add_mul_mod_self, zero_mod]

@[simp] theorem mul_mod_right (a b : ℤ) : (a * b) % a = 0 :=
by rw [mul_comm, mul_mod_left]

@[simp] theorem mod_self {a : ℤ} : a % a = 0 :=
by have := mul_mod_left 1 a; rwa one_mul at this

/- properties of / and % -/

@[simp] theorem mul_div_mul_of_pos {a : ℤ} (b c : ℤ) (H : a > 0) : a * b / (a * c) = b / c :=
suffices ∀ (m k : ℕ) (b : ℤ), (m.succ * b / (m.succ * k) : ℤ) = b / k, from
match a, eq_succ_of_zero_lt H, c, eq_coe_or_neg c with
| ._, ⟨m, rfl⟩, ._, ⟨k, or.inl rfl⟩ := this _ _ _
| ._, ⟨m, rfl⟩, ._, ⟨k, or.inr rfl⟩ :=
  by rw [-neg_mul_eq_mul_neg, int.div_neg, int.div_neg];
     apply congr_arg has_neg.neg; apply this
end,
λ m k b, match b, k with
| (n : ℕ), k   := congr_arg of_nat (nat.mul_div_mul _ _ m.succ_pos)
| -[1+ n], 0   := by rw [int.coe_nat_zero, mul_zero, int.div_zero, int.div_zero]
| -[1+ n], k+1 := congr_arg neg_succ_of_nat $
  show (m.succ * n + m) / (m.succ * k.succ) = n / k.succ, begin
    apply nat.div_eq_of_lt_le,
    { refine le_trans _ (nat.le_add_right _ _),
      rw -nat.mul_div_mul _ _ m.succ_pos,
      apply nat.div_mul_le_self },
    { change m.succ * n.succ ≤ _,
      rw [mul_left_comm],
      apply nat.mul_le_mul_left,
      apply (nat.div_lt_iff_lt_mul _ _ k.succ_pos).1,
      apply nat.lt_succ_self }
  end
end

@[simp] theorem mul_div_mul_of_pos_left (a : ℤ) {b : ℤ} (c : ℤ) (H : b > 0) :
  a * b / (c * b) = a / c :=
by rw [mul_comm, mul_comm c, mul_div_mul_of_pos _ _ H]

@[simp] theorem mul_mod_mul_of_pos {a : ℤ} (b c : ℤ) (H : a > 0) : a * b % (a * c) = a * (b % c) :=
by rw [mod_def, mod_def, mul_div_mul_of_pos _ _ H, mul_sub_left_distrib, mul_assoc]

theorem lt_div_add_one_mul_self (a : ℤ) {b : ℤ} (H : b > 0) : a < (a / b + 1) * b :=
by rw [add_mul, one_mul, mul_comm]; apply lt_add_of_sub_left_lt;
   rw [-mod_def]; apply mod_lt_of_pos _ H

theorem abs_div_le_abs : ∀ (a b : ℤ), abs (a / b) ≤ abs a :=
suffices ∀ (a : ℤ) (n : ℕ), abs (a / n) ≤ abs a, from
λ a b, match b, eq_coe_or_neg b with
| ._, ⟨n, or.inl rfl⟩ := this _ _
| ._, ⟨n, or.inr rfl⟩ := by rw [int.div_neg, abs_neg]; apply this
end,
λ a n, by rw [abs_eq_nat_abs, abs_eq_nat_abs]; exact
coe_nat_le_coe_nat_of_le (match a, n with
| (m : ℕ), n := nat.div_le_self _ _
| -[1+ m], 0 := nat.zero_le _
| -[1+ m], n+1 := nat.succ_le_succ (nat.div_le_self _ _)
end)

theorem div_le_self {a : ℤ} (b : ℤ) (Ha : a ≥ 0) : a / b ≤ a :=
by have := le_trans (le_abs_self _) (abs_div_le_abs a b);
   rwa [abs_of_nonneg Ha] at this

theorem mul_div_cancel_of_mod_eq_zero {a b : ℤ} (H : a % b = 0) : b * (a / b) = a :=
by have := mod_add_div a b; rwa [H, zero_add] at this 

theorem div_mul_cancel_of_mod_eq_zero {a b : ℤ} (H : a % b = 0) : a / b * b = a :=
by rw [mul_comm, mul_div_cancel_of_mod_eq_zero H]

/- dvd -/

lemma coe_nat_dvd_coe_nat_of_dvd {m n : ℕ} (h : m ∣ n) : (↑m : ℤ) ∣ ↑n :=
dvd.elim h $ λk e, dvd.intro k $ by rw [e, int.coe_nat_mul]

lemma dvd_of_coe_nat_dvd_coe_nat {m n : ℕ} (h : (↑m : ℤ) ∣ ↑n) : m ∣ n :=
dvd.elim h $ λa ae,
  m.eq_zero_or_pos.elim
  (λm0, by rw[m0, int.coe_nat_zero, zero_mul] at ae;
           rw [int.coe_nat_inj ae]; apply dvd_zero)
  (λm0l, let ⟨k, ke⟩ := int.eq_coe_of_zero_le $ nonneg_of_mul_nonneg_left
      (by rw -ae; apply int.coe_zero_le : 0 ≤ (m:ℤ) * a)
      (int.coe_nat_le_coe_nat_of_le m0l) in
    by rw [ke, -int.coe_nat_mul] at ae; exact dvd.intro _ (int.coe_nat_inj ae).symm)

lemma coe_nat_dvd_coe_nat_iff (m n : ℕ) : (↑m : ℤ) ∣ ↑n ↔ m ∣ n :=
⟨dvd_of_coe_nat_dvd_coe_nat, coe_nat_dvd_coe_nat_of_dvd⟩

theorem dvd_antisymm {a b : ℤ} (H1 : a ≥ 0) (H2 : b ≥ 0) : a ∣ b → b ∣ a → a = b :=
begin
  rw [-abs_of_nonneg H1, -abs_of_nonneg H2, abs_eq_nat_abs, abs_eq_nat_abs],
  rw [coe_nat_dvd_coe_nat_iff, coe_nat_dvd_coe_nat_iff, int.coe_nat_eq_coe_nat_iff],
  apply nat.dvd_antisymm
end

theorem dvd_of_mod_eq_zero {a b : ℤ} (H : b % a = 0) : a ∣ b :=
⟨b / a, (mul_div_cancel_of_mod_eq_zero H).symm⟩

theorem mod_eq_zero_of_dvd : ∀ {a b : ℤ}, a ∣ b → b % a = 0
| a ._ ⟨c, rfl⟩ := mul_mod_right _ _

theorem dvd_iff_mod_eq_zero (a b : ℤ) : a ∣ b ↔ b % a = 0 :=
⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

instance decidable_dvd : @decidable_rel ℤ (∣) :=
take a n, decidable_of_decidable_of_iff (by apply_instance) (dvd_iff_mod_eq_zero _ _).symm

protected theorem div_mul_cancel {a b : ℤ} (H : b ∣ a) : a / b * b = a :=
div_mul_cancel_of_mod_eq_zero (mod_eq_zero_of_dvd H)

protected theorem mul_div_cancel' {a b : ℤ} (H : a ∣ b) : a * (b / a) = b :=
by rw [mul_comm, int.div_mul_cancel H]

protected theorem mul_div_assoc (a : ℤ) : ∀ {b c : ℤ}, c ∣ b → (a * b) / c = a * (b / c)
| ._ c ⟨d, rfl⟩ := if cz : c = 0 then by simp [cz] else
  by rw [mul_left_comm, int.mul_div_cancel_left _ cz, int.mul_div_cancel_left _ cz]

theorem div_dvd_div : ∀ {a b c : ℤ} (H1 : a ∣ b) (H2 : b ∣ c), b / a ∣ c / a
| a ._ ._ ⟨b, rfl⟩ ⟨c, rfl⟩ := if az : a = 0 then by simp [az] else
  by rw [int.mul_div_cancel_left _ az, mul_assoc, int.mul_div_cancel_left _ az];
     apply dvd_mul_right

protected theorem div_eq_iff_eq_mul_right {a b : ℤ} (c : ℤ) (H : b ≠ 0) (H' : b ∣ a) :
  a / b = c ↔ a = b * c :=
⟨λ H1, by rw [-H1, int.mul_div_cancel' H'],
 λ H1, by rw [H1, int.mul_div_cancel_left _ H]⟩

protected theorem div_eq_iff_eq_mul_left {a b : ℤ} (c : ℤ) (H : b ≠ 0) (H' : b ∣ a) :
  a / b = c ↔ a = c * b :=
by rw mul_comm; exact int.div_eq_iff_eq_mul_right _ H H'

protected theorem eq_mul_of_div_eq_right {a b c : ℤ} (H1 : b ∣ a) (H2 : a / b = c) :
  a = b * c :=
by rw [-H2, int.mul_div_cancel' H1]

protected theorem div_eq_of_eq_mul_right {a b c : ℤ} (H1 : b ≠ 0) (H2 : a = b * c) :
  a / b = c :=
by rw [H2, int.mul_div_cancel_left _ H1]

protected theorem eq_mul_of_div_eq_left {a b c : ℤ} (H1 : b ∣ a) (H2 : a / b = c) :
  a = c * b :=
by rw [mul_comm, int.eq_mul_of_div_eq_right H1 H2]

protected theorem div_eq_of_eq_mul_left {a b c : ℤ} (H1 : b ≠ 0) (H2 : a = c * b) :
  a / b = c :=
int.div_eq_of_eq_mul_right H1 (by rw [mul_comm, H2])

theorem neg_div_of_dvd : ∀ {a b : ℤ} (H : b ∣ a), -a / b = -(a / b)
| ._ b ⟨c, rfl⟩ := if bz : b = 0 then by simp [bz] else
  by rw [neg_mul_eq_mul_neg, int.mul_div_cancel_left _ bz, int.mul_div_cancel_left _ bz]

protected theorem sign_eq_div_abs (a : ℤ) : sign a = a / (abs a) :=
if az : a = 0 then by simp [az] else
(int.div_eq_of_eq_mul_left (mt eq_zero_of_abs_eq_zero az)
  (sign_mul_abs _).symm).symm

theorem le_of_dvd {a b : ℤ} (bpos : b > 0) (H : a ∣ b) : a ≤ b :=
match a, b, eq_succ_of_zero_lt bpos, H with
| (m : ℕ), ._, ⟨n, rfl⟩, H := coe_nat_le_coe_nat_of_le $
  nat.le_of_dvd n.succ_pos $ dvd_of_coe_nat_dvd_coe_nat H
| -[1+ m], ._, ⟨n, rfl⟩, _ :=
  le_trans (le_of_lt $ neg_succ_lt_zero _) (coe_zero_le _)
end

theorem eq_one_of_dvd_one {a : ℤ} (H : a ≥ 0) (H' : a ∣ 1) : a = 1 :=
match a, eq_coe_of_zero_le H, H' with
| ._, ⟨n, rfl⟩, H' := congr_arg coe $
  nat.eq_one_of_dvd_one $ dvd_of_coe_nat_dvd_coe_nat H'
end

theorem eq_one_of_mul_eq_one_right {a b : ℤ} (H : a ≥ 0) (H' : a * b = 1) : a = 1 :=
eq_one_of_dvd_one H ⟨b, H'.symm⟩

theorem eq_one_of_mul_eq_one_left {a b : ℤ} (H : b ≥ 0) (H' : a * b = 1) : b = 1 :=
eq_one_of_mul_eq_one_right H (by rw [mul_comm, H'])

/- / and ordering -/

protected theorem div_mul_le (a : ℤ) {b : ℤ} (H : b ≠ 0) : a / b * b ≤ a :=
le_of_sub_nonneg $ by rw [mul_comm, -mod_def]; apply mod_nonneg _ H

protected theorem div_le_of_le_mul {a b c : ℤ} (H : c > 0) (H' : a ≤ b * c) : a / c ≤ b :=
le_of_mul_le_mul_right (le_trans (int.div_mul_le _ (ne_of_gt H)) H') H

protected theorem mul_lt_of_lt_div {a b c : ℤ} (H : c > 0) (H3 : a < b / c) : a * c < b :=
lt_of_not_ge $ mt (int.div_le_of_le_mul H) (not_le_of_gt H3)

protected theorem mul_le_of_le_div {a b c : ℤ} (H1 : c > 0) (H2 : a ≤ b / c) : a * c ≤ b :=
le_trans (mul_le_mul_of_nonneg_right H2 (le_of_lt H1)) (int.div_mul_le _ (ne_of_gt H1))

protected theorem le_div_of_mul_le {a b c : ℤ} (H1 : c > 0) (H2 : a * c ≤ b) : a ≤ b / c :=
le_of_lt_add_one $ lt_of_mul_lt_mul_right
  (lt_of_le_of_lt H2 (lt_div_add_one_mul_self _ H1)) (le_of_lt H1)

protected theorem le_div_iff_mul_le {a b c : ℤ} (H : c > 0) : a ≤ b / c ↔ a * c ≤ b :=
⟨int.mul_le_of_le_div H, int.le_div_of_mul_le H⟩

protected theorem div_le_div {a b c : ℤ} (H : c > 0) (H' : a ≤ b) : a / c ≤ b / c :=
int.le_div_of_mul_le H (le_trans (int.div_mul_le _ (ne_of_gt H)) H')

protected theorem div_lt_of_lt_mul {a b c : ℤ} (H : c > 0) (H' : a < b * c) : a / c < b :=
lt_of_not_ge $ mt (int.mul_le_of_le_div H) (not_le_of_gt H')

protected theorem lt_mul_of_div_lt {a b c : ℤ} (H1 : c > 0) (H2 : a / c < b) : a < b * c :=
lt_of_not_ge $ mt (int.le_div_of_mul_le H1) (not_le_of_gt H2)

protected theorem div_lt_iff_lt_mul {a b c : ℤ} (H : c > 0) : a / c < b ↔ a < b * c :=
⟨int.lt_mul_of_div_lt H, int.div_lt_of_lt_mul H⟩

protected theorem le_mul_of_div_le {a b c : ℤ} (H1 : b ≥ 0) (H2 : b ∣ a) (H3 : a / b ≤ c) :
  a ≤ c * b :=
by rw -int.div_mul_cancel H2; exact mul_le_mul_of_nonneg_right H3 H1

protected theorem lt_div_of_mul_lt {a b c : ℤ} (H1 : b ≥ 0) (H2 : b ∣ c) (H3 : a * b < c) :
  a < c / b :=
lt_of_not_ge $ mt (int.le_mul_of_div_le H1 H2) (not_le_of_gt H3)

protected theorem lt_div_iff_mul_lt {a b : ℤ} (c : ℤ) (H : c > 0) (H' : c ∣ b) :
  a < b / c ↔ a * c < b :=
⟨int.mul_lt_of_lt_div H, int.lt_div_of_mul_lt (le_of_lt H) H'⟩

theorem div_pos_of_pos_of_dvd {a b : ℤ} (H1 : a > 0) (H2 : b ≥ 0) (H3 : b ∣ a) : a / b > 0 :=
int.lt_div_of_mul_lt H2 H3 (by rwa zero_mul)

theorem div_eq_div_of_mul_eq_mul {a b c d : ℤ} (H1 : b ∣ a) (H2 : d ∣ c) (H3 : b ≠ 0)
    (H4 : d ≠ 0) (H5 : a * d = b * c) :
  a / b = c / d :=
int.div_eq_of_eq_mul_right H3 $
by rw -int.mul_div_assoc _ H2; exact
(int.div_eq_of_eq_mul_left H4 H5.symm).symm

end int
