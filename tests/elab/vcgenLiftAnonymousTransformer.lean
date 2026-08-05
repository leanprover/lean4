import Std.Tactic.Do
import Std.Internal.Do

/-!
`vcgen [liftMach]` unfolds `liftMach c` to `liftM (fun s => match c s.machine with …)`, a `monadLift`
of an anonymous state transformer. The `monadLift` spec chain rewrites this down to the bare
`fun s => match c s.machine with …`, a program whose head is a lambda that no spec keys on. `vcgen`
reports it as a missing spec, the same result it gives for a constant head with no registered spec,
rather than a hard "This should not happen" failure.
-/

open Std.Internal.Do

set_option mvcgen.warning false

structure Sys where
  machine : Nat

abbrev Base := EStateM Unit Nat
abbrev M := ReaderT Unit (StateT Unit (EStateM Unit Sys))

/-- Lift a `Base` computation over `Sys.machine`, via the anonymous state transformer
`fun s => match c s.machine with …`. -/
def liftMach {α} (c : Base α) : M α :=
  liftM (m := EStateM Unit Sys) (fun s => match c s.machine with
    | .ok a m => .ok a { s with machine := m }
    | .error e m => .error e { s with machine := m })

def prog : M Unit := do
  let v ← liftMach (get : Base Nat)
  liftMach (set v)

section
variable (Q : Unit → Unit → Unit → Sys → Prop) (E : Unit → Sys → Prop)

/--
error: No spec found for program fun s =>
  match get s.machine with
  | EStateM.Result.ok a m => EStateM.Result.ok a { machine := m }
  | EStateM.Result.error e m => EStateM.Result.error e { machine := m }.
-/
#guard_msgs (whitespace := lax) in
theorem prog_spec : ⦃ fun r n s => Q () r n s ⦄ prog ⦃ Q; E ⦄ := by
  vcgen [prog, liftMach]

end
