/--
error: `List` is a recursive datatype
-/
#guard_msgs in
attribute [grind_cases] List

/--
error: `Prod.mk` is not an inductive datatype or an alias for one
-/
#guard_msgs in
attribute [grind_cases] Prod.mk

/--
error: `List.append` is a definition, but it is not an alias/abbreviation for an inductive datatype
-/
#guard_msgs in
attribute [grind_cases] List.append

attribute [grind_cases] Prod

def Foo (α : Type u) := Sum α α

attribute [grind_cases] Foo

attribute [grind_cases] And

attribute [grind_cases] False

attribute [grind_cases] Empty

-- TODO: delete everything above

/--
error: invalid `[grind cases eager]`, `List` is not a non-recursive inductive datatype or an alias for one
-/
#guard_msgs (error) in
attribute [grind cases eager] List

attribute [grind cases] List

attribute [grind] Prod

/--
error: invalid `[grind cases]`, `id` is not an inductive datatype or an alias for one
-/
#guard_msgs (error) in
attribute [grind cases] id

/--
error: invalid `[grind cases eager]`, `id` is not a non-recursive inductive datatype or an alias for one
-/
#guard_msgs (error) in
attribute [grind cases eager] id

example : True := by
  grind [-List]

/--
error: `Array` is not marked with the `[grind]` attribute
-/
#guard_msgs (error) in
example : True := by
  grind [-Array]
