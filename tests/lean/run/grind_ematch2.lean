attribute [grind =] Array.size_set Array.get_set_eq Array.get_set_ne

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
@[grind =] theorem fx : f x (f x x) = x := sorry

/--
info: [grind.ematch.instance] fx: f a (f a a) = a
-/
#guard_msgs (info) in
example : a = b₁ → c = f b₁ b₂ → f a c ≠ a → a = b₂ → False := by
  grind


namespace pattern_normalization
opaque g : Nat → Nat
@[grind_norm] theorem gthm : g x = x := sorry
opaque f : Nat → Nat → Nat
theorem fthm : f (g x) x = x := sorry
-- The following pattern should be normalized by `grind`. Otherwise, we will not find any instance during E-matching.
/--
info: [grind.ematch.pattern] fthm: [f #0 #0]
-/
#guard_msgs (info) in
grind_pattern fthm => f (g x) x

/--
info: [grind.assert] f x y = b
[grind.assert] y = x
[grind.assert] ¬b = x
[grind.ematch.instance] fthm: f (g y) y = y
[grind.assert] f y y = y
-/
#guard_msgs (info) in
set_option trace.grind.assert true in
example : f (g x) y = b → y = x → b = x := by
  grind

end pattern_normalization
