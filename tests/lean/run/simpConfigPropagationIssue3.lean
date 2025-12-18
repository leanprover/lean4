/-- `OrientedCmp cmp` asserts that `cmp` is determined by the relation `cmp x y = .lt`. -/
class OrientedCmp (cmp : α → α → Ordering) : Prop where
  /-- The comparator operation is symmetric, in the sense that if `cmp x y` equals `.lt` then
  `cmp y x = .gt` and vice versa. -/
  symm (x y) : (cmp x y).swap = cmp y x

namespace OrientedCmp

theorem cmp_eq_gt [OrientedCmp cmp] : cmp x y = .gt ↔ cmp y x = .lt := by
  rw [← Ordering.swap_inj, symm]; exact .rfl

end OrientedCmp

/-- `TransCmp cmp` asserts that `cmp` induces a transitive relation. -/
class TransCmp (cmp : α → α → Ordering) : Prop extends OrientedCmp cmp where
  /-- The comparator operation is transitive. -/
  le_trans : cmp x y ≠ .gt → cmp y z ≠ .gt → cmp x z ≠ .gt

namespace TransCmp
variable [TransCmp cmp]
open OrientedCmp

theorem ge_trans (h₁ : cmp x y ≠ .lt) (h₂ : cmp y z ≠ .lt) : cmp x z ≠ .lt := by
  have := @TransCmp.le_trans _ cmp _ z y x
  simp [cmp_eq_gt] at *
  -- `simp` did not fire at `this`
  exact this h₂ h₁
