import Lean.Elab.Command

/-!
# Pretty-printing of the `grind` attribute
-/

elab "#pp " c:command : command => do
  Lean.logInfo c

/--
info: @[grind =]
example :=
  0
-/
#guard_msgs in
#pp @[grind =] example := 0

/--
info: @[grind _=_]
example :=
  0
-/
#guard_msgs in
#pp  @[grind _=_] example := 0

/--
info: @[grind =_]
example :=
  0
-/
#guard_msgs in
#pp @[grind =_] example := 0

/--
info: @[grind →]
example :=
  0
-/
#guard_msgs in
#pp @[grind →] example := 0

/--
info: @[grind ←]
example :=
  0
-/
#guard_msgs in
#pp @[grind ←] example := 0

/--
info: @[grind ←=]
example :=
  0
-/
#guard_msgs in
#pp @[grind ←=] example := 0

/--
info: @[grind]
example :=
  0
-/
#guard_msgs in
#pp @[grind] example := 0

/--
info: @[grind ← gen]
example :=
  0
-/
#guard_msgs in
#pp @[grind ← gen] example := 0

/-- info: example := by grind [a] on_failure 3 -/
#guard_msgs in
#pp example := by grind [a] on_failure 3

/-- info: example := by grind [← a] on_failure 3 -/
#guard_msgs in
#pp example := by grind [← a] on_failure 3
