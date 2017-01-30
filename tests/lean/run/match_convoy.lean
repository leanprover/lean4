definition foo (a b : bool) : bool :=
match a, b with
| tt, ff := tt
| tt, tt := tt
| ff, tt := tt
| ff, ff := ff
end

example : foo tt tt = tt := rfl
example : foo tt ff = tt := rfl
example : foo ff tt = tt := rfl
example : foo ff ff = ff := rfl

inductive vec (A : Type) : nat → Type
| nil {} : vec nat.zero
| cons   : ∀ {n}, A → vec n → vec (nat.succ n)

open vec

definition boo (n : nat) (v : vec bool n) : vec bool n :=
match n, v : ∀ (n : _), vec bool n → _ with
| 0,   nil      := nil
| n+1, cons a v := cons (bnot a) v
end


constant bag_setoid : ∀ A, setoid (list A)
attribute [instance] bag_setoid

noncomputable definition bag (A : Type) : Type :=
quotient (bag_setoid A)

constant subcount : ∀ {A}, list A → list A → bool
constant list.count : ∀ {A}, A → list A → nat
constant all_of_subcount_eq_tt : ∀ {A} {l₁ l₂ : list A}, subcount l₁ l₂ = tt → ∀ a, list.count a l₁ ≤ list.count a l₂
constant ex_of_subcount_eq_ff : ∀ {A} {l₁ l₂ : list A}, subcount l₁ l₂ = ff → ∃ a, ¬ list.count a l₁ ≤ list.count a l₂
noncomputable definition count {A} (a : A) (b : bag A) : nat :=
quotient.lift_on b (λ l, list.count a l)
  (λ l₁ l₂ h, sorry)
noncomputable definition subbag {A} (b₁ b₂ : bag A) := ∀ a, count a b₁ ≤ count a b₂
infix ⊆ := subbag

attribute [instance]
noncomputable definition decidable_subbag {A} (b₁ b₂ : bag A) : decidable (b₁ ⊆ b₂) :=
quotient.rec_on_subsingleton₂ b₁ b₂ (λ l₁ l₂,
  match subcount l₁ l₂, rfl : ∀ (b : _), subcount l₁ l₂ = b → _ with
  | tt, H := is_true (all_of_subcount_eq_tt H)
  | ff, H := is_false (λ h,
            exists.elim (ex_of_subcount_eq_ff H)
            (λ w hw, absurd (h w) hw))
  end)

attribute [instance]
noncomputable definition decidable_subbag2 {A} (b₁ b₂ : bag A) : decidable (b₁ ⊆ b₂) :=
quotient.rec_on_subsingleton₂ b₁ b₂ (λ l₁ l₂,
  match psigma.mk (subcount l₁ l₂) rfl : (Σ' (b : _), subcount l₁ l₂ = b) → _ with
  | psigma.mk tt H := is_true (all_of_subcount_eq_tt H)
  | psigma.mk ff H := is_false (λ h,
            exists.elim (ex_of_subcount_eq_ff H)
            (λ w hw, absurd (h w) hw))
  end)

local notation ⟦ a , b ⟧ := psigma.mk a b

attribute [instance]
noncomputable definition decidable_subbag3 {A} (b₁ b₂ : bag A) : decidable (b₁ ⊆ b₂) :=
quotient.rec_on_subsingleton₂ b₁ b₂ (λ l₁ l₂,
  match ⟦subcount l₁ l₂, rfl⟧ : (Σ' (b : _), subcount l₁ l₂ = b) → _ with
  | ⟦tt, H⟧ := is_true (all_of_subcount_eq_tt H)
  | ⟦ff, H⟧ := is_false (λ h,
            exists.elim (ex_of_subcount_eq_ff H)
            (λ w hw, absurd (h w) hw))
  end)
