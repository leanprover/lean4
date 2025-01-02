grind_pattern Array.size_set => Array.set a i v h
grind_pattern Array.get_set_eq  => a.set i v h
grind_pattern Array.get_set_ne => (a.set i v hi)[j]

set_option grind.debug true
set_option trace.grind.ematch.pattern true
set_option trace.grind.ematch.instance true

example (as bs cs : Array α) (v₁ v₂ : α)
        (i₁ i₂ j : Nat)
        (h₁ : i₁ < as.size)
        (h₂ : bs = as.set i₁ v₁)
        (h₃ : i₂ < bs.size)
        (h₃ : cs = bs.set i₂ v₂)
        (h₄ : i₁ ≠ j ∧ i₂ ≠ j)
        (h₅ : j < cs.size)
        (h₆ : j < as.size)
        : cs[j] = as[j] := by
  grind

example (as bs cs : Array α) (v₁ v₂ : α)
        (i₁ i₂ j : Nat)
        (h₁ : i₁ < as.size)
        (h₂ : as.set i₁ v₁ = bs)
        (h₃ : i₂ < bs.size)
        (h₃ : bs.set i₂ v₂ = cs)
        (h₄ : i₁ ≠ j ∧ j ≠ i₂)
        (h₅ : j < cs.size)
        (h₆ : j < as.size)
        : cs[j] = as[j] := by
  grind

example (as bs cs : Array α) (v₁ v₂ : α)
        (i₁ i₂ j : Nat)
        (h₁ : i₁ < as.size)
        (h₂ : as.set i₁ v₁ = bs)
        (h₃ : i₂ < bs.size)
        (h₃ : bs.set i₂ v₂ = cs)
        (h₄ : j ≠ i₁ ∧ j ≠ i₂)
        (h₅ : j < cs.size)
        (h₆ : j < as.size)
        : cs[j] = as[j] := by
  grind

example (as bs cs ds : Array α) (v₁ v₂ v₃ : α)
        (i₁ i₂ i₃ j : Nat)
        (h₁ : i₁ < as.size)
        (h₂ : as.set i₁ v₁ = bs)
        (h₃ : i₂ < bs.size)
        (h₃ : bs.set i₂ v₂ = cs)
        (h₄ : i₃ < cs.size)
        (h₅ : ds = cs.set i₃ v₃)
        (h₆ : j ≠ i₁ ∧ j ≠ i₂ ∧ i₃ ≠ j)
        (h₇ : j < ds.size)
        (h₈ : j < as.size)
        : ds[j] = as[j] := by
  grind

opaque f (a b : α) : α := a
theorem fx : f x (f x x) = x := sorry
grind_pattern fx => f x (f x x)

/--
info: [grind.ematch.instance] fx: f a (f a a) = a
-/
#guard_msgs (info) in
example : a = b₁ → c = f b₁ b₂ → f a c ≠ a → a = b₂ → False := by
  grind
