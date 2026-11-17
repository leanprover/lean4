/-!
Tests that tactic blocks of a deprecated declaration preceded by `in` are still elaborated
incrementally, even though the command in front of `in` is elaborated without deprecation checks.
-/

set_option warn.classDefReducibility false

class C where
  x : Nat

@[deprecated "no replacement" (since := "2025-01-01")] def deprecatedInst : C := ⟨1⟩

attribute [local instance] deprecatedInst in
@[deprecated "no replacement" (since := "2025-01-01")] theorem deprecatedThm : C.x = C.x := by
  rfl
  dbg_trace "d 0"
  dbg_trace "d 1"
  dbg_trace "d 2"
              --^ sync
              --^ insert: ".5"

-- RESET
set_option warn.classDefReducibility false

class C where
  x : Nat

@[deprecated "no replacement" (since := "2025-01-01")] def deprecatedInst : C := ⟨1⟩

attribute [local instance] deprecatedInst in
set_option maxHeartbeats 100000 in
@[deprecated "no replacement" (since := "2025-01-01")] theorem deprecatedThm : C.x = C.x := by
  rfl
  dbg_trace "n 0"
  dbg_trace "n 1"
  dbg_trace "n 2"
              --^ sync
              --^ insert: ".5"
              --^ collectDiagnostics
