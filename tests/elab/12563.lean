/-!
# Make the `unusedSectionVars`, `omit` and `loopingSimpArgs` linters honour the `linter.all` option

When e.g. `linter.unusedSectionVars` is not set explicitly, but the `linter.all` option is set,
the linter should behave accordingly; similarly for `linter.omit` and `linter.loopingSimpArgs`.
-/

/-! ## `linter.unusedSectionVars` -/

namespace UnusedSectionVars

section

set_option linter.unusedSectionVars true

variable {α : Type} [ToString α]

/--
warning: automatically included section variable(s) unused in theorem `UnusedSectionVars.myTheorem1`:
  [ToString α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ToString α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
-/
#guard_msgs in
theorem myTheorem1 (a : α) : a = a := rfl

end

section

set_option linter.all true

variable {α : Type} [ToString α]

/--
warning: automatically included section variable(s) unused in theorem `UnusedSectionVars.myTheorem2`:
  [ToString α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ToString α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
-/
#guard_msgs in
theorem myTheorem2 (a : α) : a = a := rfl

end

section

set_option linter.unusedSectionVars false

variable {α : Type} [ToString α]

theorem myTheorem3 (a : α) : a = a := rfl

end

section

set_option linter.all false

variable {α : Type} [ToString α]

theorem myTheorem4 (a : α) : a = a := rfl

end

end UnusedSectionVars

/-! ## `linter.omit` -/

namespace Omit

section

set_option linter.omit true

variable (α : Type)

/--
warning: `omit` should be avoided in favor of restructuring your `variable` declarations

Note: This linter can be disabled with `set_option linter.omit false`
-/
#guard_msgs in
omit α

end

section

set_option linter.all true

variable (α : Type)

/--
warning: `omit` should be avoided in favor of restructuring your `variable` declarations

Note: This linter can be disabled with `set_option linter.omit false`
-/
#guard_msgs in
omit α

end

section

set_option linter.omit false

variable (α : Type)

omit α

end

section

set_option linter.all false

variable (α : Type)

omit α

end

end Omit

/-! ## `linter.loopingSimpArgs` -/

namespace LoopingSimpArgs

set_option linter.unusedSimpArgs false -- can be removed after merging #12560

axiom testSorry : α

opaque a : Nat

theorem aa : a = id a := testSorry

section

set_option linter.loopingSimpArgs true

/--
warning: Possibly looping simp theorem: `aa`

Note: Possibly caused by: `id`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Note: This linter can be disabled with `set_option linter.loopingSimpArgs false`
-/
#guard_msgs in
example : True := by simp -failIfUnchanged only [aa, id]

end

section

set_option linter.all true

/--
warning: Possibly looping simp theorem: `aa`

Note: Possibly caused by: `id`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Note: This linter can be disabled with `set_option linter.loopingSimpArgs false`
-/
#guard_msgs in
example : True := by simp -failIfUnchanged only [aa, id]

end
section

set_option linter.loopingSimpArgs false

#guard_msgs in
example : True := by simp -failIfUnchanged only [aa, id]

end

section

set_option linter.all false

#guard_msgs in
example : True := by simp -failIfUnchanged only [aa, id]

end

end LoopingSimpArgs
