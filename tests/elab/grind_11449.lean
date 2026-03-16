opaque double : Nat → Nat
def P (n : Nat) : Prop := n >= 0
theorem pax (n : Nat) : P n := by grind [P]
def T (n : Nat) : Type := Vector Nat n

inductive Foo' (α β : Type u) : (n : Nat) → P n -> Type u
  | even (a : α) (n : Nat) (v : T n) (h : P n) : Foo' α β (double n) (pax _)
  | odd  (b : β) (n : Nat) (v : T n) : Foo' α β (Nat.succ (double n)) (pax _)

example (α β : Type) (a₁ a₂ : α)
    (n₁ n₂ : Nat)
    (v₁ : T n₁) (v₂ : T n₂)
    (h₁ : P n₁) (h₂ : P n₂)
    (h_1 : double n₁ = double n₂)
    (h_2 : Foo'.even (β := β) a₁ n₁ v₁ h₁ ≍ Foo'.even (β := β) a₂ n₂ v₂ h₂) :
    a₁ = a₂ ∧ n₁ = n₂ ∧ v₁ ≍ v₂ ∧ h₁ ≍ h₂ := by
  grind

example (α β : Type) (a : α) (b : β)
    (n₁ n₂ : Nat)
    (v₁ : T n₁) (v₂ : T n₂)
    (h₁ : P n₁)
    (h_1 : double n₁ = (double n₂).succ)
    (h_2 : Foo'.even (β := β) a n₁ v₁ h₁ ≍ Foo'.odd (α := α) b n₂ v₂)
    : False := by
  grind

inductive Parity : Nat -> Type
  | even (n) : Parity (double n)
  | odd  (n) : Parity (Nat.succ (double n))

example
  (motive : (x : Nat) → Parity x → Sort u_1)
  (h_2 : (j : Nat) → motive (double j) (Parity.even j))
  (j n : Nat)
  (heq_1 : double n = double j)
  (heq_2 : Parity.even n ≍ Parity.even j):
  h_2 n ≍ h_2 j := by
grind

opaque q : Nat → Nat → Prop
axiom qax : q a b → double a = double b
attribute [grind →] qax

example
  (motive : (x : Nat) → Parity x → Sort u_1)
  (h_2 : (j : Nat) → motive (double j) (Parity.even j))
  (j n : Nat)
  (heq_1 : q j n)
  (heq_2 : Parity.even n ≍ Parity.even j):
  h_2 n ≍ h_2 j := by
grind
