module
import Reference
import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.Command

/-! Unused conflicting definitions must not change a literal approved input. -/

run_elab
  let attempt : IO Unit := do
    try
      IO.FS.writeFile "../evaluator/reference.export" "tampered during compilation"
      IO.eprintln "protected-write-succeeded: compilation"
    catch _ => IO.eprintln "protected-write-denied: compilation"
  liftM attempt

public theorem success (_ : forall n : Nat, n + n = 2 * n) : True := True.intro
