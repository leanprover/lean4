
import Lean
/-!
# Make sure 'ext' attribute works in conjunction with local/scoped
-/

section Ex0

@[local ext] structure S (α β : Type _) where
  a : α
  b : β

-- Used to fail
attribute [local ext] S

-- Used to work, still works
attribute [local ext] S.ext

/--
info: S.ext.{u_1, u_2} {α : Type u_1} {β : Type u_2} {x y : S α β} (a : x.a = y.a) (b : x.b = y.b) : x = y
-/
#guard_msgs in #check S.ext

/--
info: S.ext_iff.{u_1, u_2} {α : Type u_1} {β : Type u_2} {x y : S α β} : x = y ↔ x.a = y.a ∧ x.b = y.b
-/
#guard_msgs in #check S.ext_iff

end Ex0


section Ex1

section

@[local ext] structure S1 (α β : Type _) where
  a : α
  b : β

/--
info: S1.ext.{u_1, u_2} {α : Type u_1} {β : Type u_2} {x y : S1 α β} (a : x.a = y.a) (b : x.b = y.b) : x = y
-/
#guard_msgs in #check S1.ext

example (x y : S1 Unit Unit) : x = y := by ext

end

/--
error: no applicable extensionality theorem found for
  S1 Unit Unit
-/
#guard_msgs in example (x y : S1 Unit Unit) : x = y := by ext

end Ex1


section Ex2

structure S2 (α β : Type _) where
  a : α
  b : β

section

@[local ext] private theorem S2_ext {x y : S2 α β} (a : x.a = y.a) (b : x.b = y.b) : x = y := by
  cases x
  cases y
  subst_vars
  rfl

example (x y : S2 Unit Unit) : x = y := by ext

end

/--
error: no applicable extensionality theorem found for
  S2 Unit Unit
-/
#guard_msgs in example (x y : S2 Unit Unit) : x = y := by ext

/--
info: S2_ext_iff.{u_1, u_2} {α : Type u_1} {β : Type u_2} {x y : S2 α β} : x = y ↔ x.a = y.a ∧ x.b = y.b
-/
#guard_msgs in #check S2_ext_iff

end Ex2


section Ex3

-- TODO: allow 'scoped' here? The limitation is in attribute processing itself, not the 'ext' attribute.
/-- error: scoped attributes must be used inside namespaces -/
#guard_msgs in
@[scoped ext] structure S3' (α β : Type _) where
  a : α
  b : β

structure S3 (α β : Type _) where
  a : α
  b : β

namespace S3
attribute [scoped ext] S3

/--
info: S3.ext.{u_1, u_2} {α : Type u_1} {β : Type u_2} {x y : S3 α β} (a : x.a = y.a) (b : x.b = y.b) : x = y
-/
#guard_msgs in #check S3.ext

example (x y : S3 Unit Unit) : x = y := by
  ext

end S3

/--
error: no applicable extensionality theorem found for
  S3 Unit Unit
-/
#guard_msgs in
example (x y : S3 Unit Unit) : x = y := by
  ext

open scoped S3 in
example (x y : S3 Unit Unit) : x = y := by
  ext

end Ex3
