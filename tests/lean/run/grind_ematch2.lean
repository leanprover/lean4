reset_grind_attrs%

attribute [grind =] Array.size_set Array.getElem_set_self Array.getElem_set_ne

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

/--
info: [grind.ematch.instance] Array.size_set: (cs.set i₃ v₃ ⋯).size = cs.size
[grind.ematch.instance] Array.size_set: (bs.set i₂ v₂ ⋯).size = bs.size
[grind.ematch.instance] Array.size_set: (as.set i₁ v₁ ⋯).size = as.size
[grind.ematch.instance] Array.getElem_set_ne: ∀ (pj : j < cs.size), i₃ ≠ j → (cs.set i₃ v₃ ⋯)[j] = cs[j]
[grind.ematch.instance] Array.getElem_set_ne: ∀ (pj : j < bs.size), i₂ ≠ j → (bs.set i₂ v₂ ⋯)[j] = bs[j]
[grind.ematch.instance] Array.getElem_set_ne: ∀ (pj : j < as.size), i₁ ≠ j → (as.set i₁ v₁ ⋯)[j] = as[j]
-/
#guard_msgs (info) in
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
