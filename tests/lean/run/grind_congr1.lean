set_option warningAsError false
set_option grind.debug true
set_option grind.debug.proofs true

example (a b : Nat) (f : Nat → Nat) : (h₁ : a = b) → f a = f b := by
  grind

example (a b : Nat) (f : Nat → Nat) : (h₁ : a = b) → (h₂ : f a ≠ f b) → False := by
  grind

example (a b : Nat) (f : Nat → Nat) : a = b → f (f a) ≠ f (f b) → False := by
  grind

example (a b c : Nat) (f : Nat → Nat) : a = b → c = b → f (f a) ≠ f (f c) → False := by
  grind

example (a b c : Nat) (f : Nat → Nat → Nat) : a = b → c = b → f (f a b) a ≠ f (f c c) c → False := by
  grind

example (a b c : Nat) (f : Nat → Nat → Nat) : a = b → c = b → f (f a b) a = f (f c c) c := by
  grind

example (a b c d : Nat) : a = b → b = c → c = d → a = d := by
  grind

example (a b c d : Nat) : a ≍ b → b = c → c ≍ d → a ≍ d := by
  grind

example (a b c d : Nat) : a = b → b = c → c ≍ d → a ≍ d := by
  grind

opaque f {α : Type} : α → α → α := fun a _ => a
opaque g : Nat → Nat

example (a b c : Nat) : a = b → g a ≍ g b := by
  grind

example (a b c : Nat) : a = b → c = b → f (f a b) (g c) = f (f c a) (g b) := by
  grind

example (a b c d e x y : Nat) : a = b → a = x → b = y → c = d → c = e → c = b → a = e := by
  grind

namespace Ex1
opaque f (a b : Nat) : a > b → Nat
opaque g : Nat → Nat

example (a₁ a₂ b₁ b₂ c d : Nat)
        (H₁ : a₁ > b₁)
        (H₂ : a₂ > b₂) :
        a₁ = c → a₂ = c →
        b₁ = d → d  = b₂ →
        g (g (f a₁ b₁ H₁)) = g (g (f a₂ b₂ H₂)) := by
  grind
end Ex1

namespace Ex2
def f (α : Type) (a : α) : α := a

example (a : α) (b : β) : (h₁ : α = β) → (h₂ : a ≍ b) → f α a ≍ f β b := by
  grind

end Ex2

example (f g : (α : Type) → α → α) (a : α) (b : β) : (h₁ : α = β) → (h₂ : a ≍ b) → (h₃ : f = g) → f α a ≍ g β b := by
  grind

set_option trace.grind.debug.proof true in
example (f : {α : Type} → α → Nat → Bool → Nat) (a b : Nat) : f a 0 true = v₁ → f b 0 true = v₂ → a = b → v₁ = v₂ := by
  grind

set_option trace.grind.debug.proof true in
example (f : {α : Type} → α → Nat → Bool → Nat) (a b : Nat) : f a b x = v₁ → f a b y = v₂ → x = y → v₁ = v₂ := by
  grind

set_option trace.grind.debug.proof true in
theorem ex1 (f : {α : Type} → α → Nat → Bool → Nat) (a b c : Nat) : f a b x = v₁ → f c b y = v₂ → a = c → x = y → v₁ = v₂ := by
  grind

#print ex1


example (n1 n2 n3 : Nat) (v1 w1 : Vector Nat n1) (w1' : Vector Nat n3) (v2 w2 : Vector Nat n2) :
        n1 = n3 → v1 = w1 → w1 ≍ w1' → v2 = w2 → v1 ++ v2 ≍ w1' ++ w2 := by
  grind

example (n1 n2 n3 : Nat) (v1 w1 : Vector Nat n1) (w1' : Vector Nat n3) (v2 w2 : Vector Nat n2) :
        n1 ≍ n3 → v1 = w1 → w1 ≍ w1' → v2 ≍ w2 → v1 ++ v2 ≍ w1' ++ w2 := by
  grind

theorem ex2 (n1 n2 n3 : Nat) (v1 w1 v : Vector Nat n1) (w1' : Vector Nat n3) (v2 w2 w : Vector Nat n2) :
        n1 ≍ n3 → v1 = w1 → w1 ≍ w1' → v2 ≍ w2 → w1' ++ w2 ≍ v ++ w → v1 ++ v2 ≍ v ++ w := by
  grind

#print ex2
