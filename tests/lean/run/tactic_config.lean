import Lean
/-!
# Tests for tactic configuration elaboration
-/

open Lean

/-!
Simple tactic configuration
-/
structure MyTacticConfig where
  x : Nat := 0
  y : Bool := false
  deriving Repr

declare_config_elab elabMyTacticConfig MyTacticConfig

elab "my_tactic" cfg:Parser.Tactic.optConfig : tactic => do
  let config ← elabMyTacticConfig cfg
  logInfo m!"config is {repr config}"

/--
info: config is { x := 0, y := false }
---
info: config is { x := 0, y := true }
---
info: config is { x := 1, y := false }
---
info: config is { x := 2, y := false }
---
info: config is { x := 1, y := true }
---
info: config is { x := 0, y := false }
-/
#guard_msgs in
example : True := by
  my_tactic
  my_tactic +y
  my_tactic (x := 1)
  my_tactic -y (x := 2)
  my_tactic (config := {x := 1, y := true})
  my_tactic +y (config := {y := false})
  trivial

/-!
Basic errors
-/

/--
error: option is not boolean-valued, so '(x := ...)' syntax must be used
---
info: config is { x := 0, y := false }
---
error: unsolved goals
⊢ True
-/
#guard_msgs in example : True := by my_tactic +x

/--
error: structure 'MyTacticConfig' does not have a field named 'w'
---
info: config is { x := 0, y := false }
---
error: unsolved goals
⊢ True
-/
#guard_msgs in example : True := by my_tactic +w

/--
error: field 'x' of structure 'MyTacticConfig' is not a structure
---
info: config is { x := 0, y := false }
---
error: unsolved goals
⊢ True
-/
#guard_msgs in example : True := by my_tactic +x.a

/-!
A tactic configuration extending another with different default values.
-/
structure MyTacticConfig' extends MyTacticConfig where
  x := 22
  y := true
  deriving Repr

declare_config_elab elabMyTacticConfig' MyTacticConfig'

elab "my_tactic'" cfg:Parser.Tactic.optConfig : tactic => do
  let config ← elabMyTacticConfig' cfg
  logInfo m!"config is {repr config}"

/--
info: config is { toMyTacticConfig := { x := 22, y := true } }
---
info: config is { toMyTacticConfig := { x := 22, y := true } }
---
info: config is { toMyTacticConfig := { x := 1, y := true } }
---
info: config is { toMyTacticConfig := { x := 2, y := false } }
---
info: config is { toMyTacticConfig := { x := 1, y := true } }
---
info: config is { toMyTacticConfig := { x := 22, y := false } }
-/
#guard_msgs in
example : True := by
  my_tactic'
  my_tactic' +y
  my_tactic' (x := 1)
  my_tactic' -y (x := 2)
  my_tactic' (config := {x := 1, y := true})
  my_tactic' +y (config := {y := false})
  trivial

/-!
Tactic configurations with hierarchical fields
-/

structure A where
  x : Bool := false
  deriving Repr
structure B extends A
  deriving Repr
structure C where
  b : B := {}
  deriving Repr
declare_config_elab elabC C

elab "ctac" cfg:Parser.Tactic.optConfig : tactic => do
  let config ← elabC cfg
  logInfo m!"config is {repr config}"

/--
info: config is { b := { toA := { x := true } } }
---
info: config is { b := { toA := { x := true } } }
-/
#guard_msgs in
example : True := by
  ctac +b.x
  ctac +b.toA.x
  trivial

/-!
Responds to recovery mode. In these, `ctac` continues even though configuration elaboration failed.
-/

/--
error: structure 'C' does not have a field named 'x'
---
info: config is { b := { toA := { x := false } } }
-/
#guard_msgs in
example : True := by
  ctac +x
  trivial

/--
error: structure 'C' does not have a field named 'x'
---
info: config is { b := { toA := { x := false } } }
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by
  ctac +x
  done

/-!
Responds to recovery mode. In this, `ctac` fails, doesn't report anything, and then execution continues to `exact`.
-/

/-- error: unknown identifier 'blah' -/
#guard_msgs in
example : True := by
  first | ctac +x | exact blah
