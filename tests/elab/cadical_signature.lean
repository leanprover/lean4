import Lean.Cadical

/-!
Check that linking Cadical works.
-/

/-- info: true -/
#guard_msgs in
#eval Lean.Cadical.Internal.signature.startsWith "cadical-"
