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
