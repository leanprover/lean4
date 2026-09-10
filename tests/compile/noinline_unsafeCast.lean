/-! Regression test against a segfault caused by inlining unsafeCast, see issue #14315 -/

structure P where
  a : Nat
  b : Nat

structure Q where
  p : P
  n : Nat

@[inline] def mkP (n : Nat) : Option P := some ⟨n, n + 1⟩

def combine (n : Nat) : Option Q :=
  (mkP n).attach.map fun x => ⟨x.val, n⟩

def main : IO Unit := do
  match combine 5 with
  | some q => IO.println s!"{q.p.a} {q.p.b}"
  | none => IO.println "none"
