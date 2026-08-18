module

/-! https://github.com/leanprover/lean4/issues/13877

Inaccessible hypothesis names must not break `grind?`. Terms that differ only in
inaccessible variables have identical anchors. `grind?` now disambiguates `cases`
anchors using ordinal references (e.g., `#a56e/2`), and the generated scripts must
replay successfully regardless of hypothesis names. -/

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

-- Used to produce an empty `grind only` suggestion and a script that could not
-- close the goal because the destructuring uses inaccessible names.
/--
info: Try these:
  [apply] grind only [= reflTransGen_iff_eq, EqvGen.rel, #9242, #14e8, #d806, #f38a, #e48b, #5525, #3442, #ae98, EqvGen]
  [apply] grind only [= reflTransGen_iff_eq, EqvGen.rel, EqvGen]
  [apply] grind [EqvGen] =>
    instantiate only [= reflTransGen_iff_eq, EqvGen.rel]
    instantiate only [#9242]
    cases #14e8
    · cases #d806 <;> cases #f38a <;> cases #e48b <;> instantiate only [#9242]
    · instantiate only [= reflTransGen_iff_eq]
      cases #d806
      · cases #f38a <;> cases #5525 <;> instantiate only [#3442]
      · cases #f38a
        · cases #ae98/2
          · instantiate only [#3442]
          · cases #e48b <;> instantiate only [#9242]
        · cases #ae98/2
          · instantiate only [#3442]
          · cases #e48b <;> instantiate only [#9242]
-/
#guard_msgs in
example (cr : ChurchRosser r) (nx : Normal r x) (ny : Normal r y) (xy : EqvGen r x y) : x = y := by
  have ⟨_, _, _⟩ := cr xy
  grind? [EqvGen]

example (cr : ChurchRosser r) (nx : Normal r x) (ny : Normal r y) (xy : EqvGen r x y) : x = y := by
  have ⟨_, _, _⟩ := cr xy
  grind [EqvGen] =>
    instantiate only [= reflTransGen_iff_eq, EqvGen.rel]
    instantiate only [#9242]
    cases #14e8
    · cases #d806 <;> cases #f38a <;> cases #e48b <;> instantiate only [#9242]
    · instantiate only [= reflTransGen_iff_eq]
      cases #d806
      · cases #f38a <;> cases #5525 <;> instantiate only [#3442]
      · cases #f38a
        · cases #ae98/2
          · instantiate only [#3442]
          · cases #e48b <;> instantiate only [#9242]
        · cases #ae98/2
          · instantiate only [#3442]
          · cases #e48b <;> instantiate only [#9242]

-- Same example with an accessible name.
example (cr : ChurchRosser r) (nx : Normal r x) (ny : Normal r y) (xy : EqvGen r x y) : x = y := by
  have ⟨z, _, _⟩ := cr xy
  grind? [EqvGen]

end Relation
