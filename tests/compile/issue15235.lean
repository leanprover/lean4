/-!
Tests `withExclusive` (#15235): logically it is `k false`, at runtime `k` learns whether the
argument is exclusive.
-/

example (a : Nat) (k : Bool → Nat) (h : k true = k false) : withExclusive a k h = k false := rfl

set_option compiler.extract_closed false

@[noinline] def sizeReportingExclusive (a : @& Array Nat) : Nat :=
  let n := a.size
  withExclusive a (fun excl => dbgTrace s!"exclusive: {excl}" fun _ => n) rfl

@[noinline] def mkArr (n : Nat) : Array Nat := Array.range n

def main : IO Unit := do
  let a := mkArr 3
  IO.eprintln (sizeReportingExclusive a)
  let b := mkArr 4
  let c := #[b]
  IO.eprintln (sizeReportingExclusive b)
  IO.eprintln c.size
