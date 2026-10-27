module

import Lean

/-!
Tests that fallback axioms for rejected unsafe definitions remain unsafe.
-/

open Lean

set_option Elab.async false

run_meta do
  try
    addDecl <| .defnDecl {
      name := `unsafeFallbackFalse
      levelParams := []
      type := mkConst ``False
      value := mkConst ``True.intro
      hints := .opaque
      safety := .unsafe
    }
  catch _ => pure ()

run_meta do
  let name := `unsafeFallbackOpaque
  try
    addDecl <| .opaqueDecl {
      name
      levelParams := []
      type := mkConst ``False
      value := mkConst ``True.intro
      isUnsafe := true
    }
  catch _ => pure ()
  let some info := (← getEnv).find? name | throwError "fallback axiom was not added"
  unless info.isUnsafe do
    throwError "fallback axiom was not marked unsafe"

/--
error: (kernel) invalid declaration, it uses unsafe declaration 'unsafeFallbackFalse'
-/
#guard_msgs in
theorem unsafeFallbackExploit : False := unsafeFallbackFalse
