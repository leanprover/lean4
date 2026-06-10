namespace Relation

variable {r : α → α → Prop}

@[grind]
inductive ReflTransGen (r : α → α → Prop) (a : α) : α → Prop
  | refl : ReflTransGen r a a
  | tail {b c : α} : ReflTransGen r a b → r b c → ReflTransGen r a c

@[grind =]
theorem reflTransGen_iff_eq (h : ∀ b, ¬r a b) : ReflTransGen r a b ↔ b = a where
  mp h := by induction h with grind
  mpr := by grind

variable (r) in
inductive EqvGen : α → α → Prop
  | rel x y : r x y → EqvGen x y
  | refl x : EqvGen x x
  | symm x y : EqvGen x y → EqvGen y x
  | trans x y z : EqvGen x y → EqvGen y z → EqvGen x z

def Join (r : α → α → Prop) : α → α → Prop := fun a b ↦ ∃ c, r a c ∧ r b c

abbrev ChurchRosser (r : α → α → Prop) := ∀ {x y}, EqvGen r x y → Join (ReflTransGen r) x y

abbrev Reducible (r : α → α → Prop) (x : α) : Prop := ∃ y, r x y

abbrev Normal (r : α → α → Prop) (x : α) : Prop := ¬ Reducible r x

/--
warning: generated tactic cannot close the goal
  · instantiate approx
    instantiate approx
    instantiate approx
    instantiate approx
    cases #14e8
    · cases #d806
      cases #f38a
      · cases #e48b <;> instantiate only [#9242]
      · cases #e48b8a1c9d724d48 <;> instantiate only [#9242]
    · instantiate approx
      cases #d806c9c25a5bb198
      · cases #f38a <;> cases #5525352b0f5c2899 <;> instantiate only [#3442]
      · instantiate approx
        cases #f38ab3f9c8353d60
        · instantiate approx
          cases #ae986558d4efb01d
          · instantiate only [#3442]
          · cases #e48b8a1c9d724d48 <;> instantiate only [#9242]
        · instantiate approx
          instantiate approx
          instantiate approx
          cases #ae986558d4efb01d
          · instantiate only [#3442]
          · cases #e48b8a1c9d724d48 <;> instantiate only [#9242]
Initial goal
case grind
α : Sort u_1
r : α → α → Prop
x y : α
cr : ChurchRosser r
nx : Normal r x
ny : Normal r y
xy : EqvGen r x y
w✝ : α
left✝ : ReflTransGen r x w✝
right✝ : ReflTransGen r y w✝
h✝ : ¬x = y
⊢ False
---
info: Try these:
  [apply] grind only [= reflTransGen_iff_eq, ReflTransGen.tail, EqvGen.trans, ReflTransGen.refl, #14e8, #d806, #f38a,
    #e48b, #9242, #e48b8a1c9d724d48, #d806c9c25a5bb198, #5525352b0f5c2899, #3442, #f38ab3f9c8353d60, #ae986558d4efb01d]
  [apply] grind only [= reflTransGen_iff_eq, ReflTransGen.tail, EqvGen.trans, ReflTransGen.refl]
  [apply] grind =>
    instantiate approx
    instantiate approx
    instantiate approx
    instantiate approx
    cases #14e8
    · cases #d806
      cases #f38a
      · cases #e48b <;> instantiate only [#9242]
      · cases #e48b8a1c9d724d48 <;> instantiate only [#9242]
    · instantiate approx
      cases #d806c9c25a5bb198
      · cases #f38a <;> cases #5525352b0f5c2899 <;> instantiate only [#3442]
      · instantiate approx
        cases #f38ab3f9c8353d60
        · instantiate approx
          cases #ae986558d4efb01d
          · instantiate only [#3442]
          · cases #e48b8a1c9d724d48 <;> instantiate only [#9242]
        · instantiate approx
          instantiate approx
          instantiate approx
          cases #ae986558d4efb01d
          · instantiate only [#3442]
          · cases #e48b8a1c9d724d48 <;> instantiate only [#9242]
-/
#guard_msgs (warning, info) in
example (cr : ChurchRosser r) (nx : Normal r x) (ny : Normal r y) (xy : EqvGen r x y) : x = y := by
  have ⟨_, _, _⟩ := cr xy
  grind? [EqvGen]

end Relation
