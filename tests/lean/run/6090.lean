/-!
# Make sure `#check` heeds `pp.raw`
https://github.com/leanprover/lean4/issues/6090
-/

section
/-- info: id.{u} {α : Sort u} (a : α) : α -/
#guard_msgs in #check id
/-- info: @id : {α : Sort u_1} → α → α -/
#guard_msgs in #check @id
-- '#print' was unaffected, but throw in a test anyway.
/--
info: def id.{u} : {α : Sort u} → α → α :=
fun {α} a => a
-/
#guard_msgs in #print id

set_option pp.raw true

/-- info: id.{u} : forall {α : Sort.{u}}, α -> α -/
#guard_msgs in #check id
/-- info: id.{u_1} : forall {α : Sort.{u_1}}, α -> α -/
#guard_msgs in #check @id
-- '#print' was unaffected, but throw in a test anyway.
/--
info: def id.{u} : forall {α : Sort.{u}}, α -> α :=
fun {α : Sort.{u}} (a : α) => a
-/
#guard_msgs in #print id
end
