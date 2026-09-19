/-!
`#guard_msgs` nested under `… in` must not wipe errors from the outer command (#15196).
-/

/-- error: Unknown option `foo` -/
#guard_msgs (substring := true) in
set_option foo true in
#guard_msgs in
example := True

/-- error: Unknown attribute `[foo]` -/
#guard_msgs (substring := true) in
attribute [foo] foo in
#guard_msgs in
example := True
