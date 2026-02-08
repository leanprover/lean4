module
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
