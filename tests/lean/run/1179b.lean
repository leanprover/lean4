inductive Foo : Nat → Type _
| nil : Foo 0
| cons (t: Foo l) : Foo l

def Foo.bar (t₁: Foo l₁) (t₂ : Foo l₂) : Bool :=
  match t₂ with
  | cons s₁ => t₁.bar s₁
  | _ => false

attribute [simp] Foo.bar

example (h : t₂ = .nil) : Foo.bar t₁ t₂ = false := by
  unfold Foo.bar
  split
  · contradiction
  · rfl

set_option pp.proofs true
#print Foo.bar.match_1
