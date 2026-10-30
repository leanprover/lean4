import Std.Internal.UV

/-!
`Loop.configure` borrows its options instead of leaking them: the options object stays exclusive
after the call. Compiled only, since the interpreter holds its own references to the object.
-/

open Std.Internal.UV

/-- Built at runtime so the options object is not a persistent closed term. -/
@[noinline] def mkOpts (b : Bool) : Loop.Options :=
  { accumulateIdleTime := b, blockSigProfSignal := b }

def main (args : List String) : IO Unit := do
  let o := mkOpts args.isEmpty
  Loop.configure o
  IO.println s!"exclusive after configure: {unsafe isExclusiveUnsafe o}"
