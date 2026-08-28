/-!
# Test for improved error message when `initialize` fails due to missing `Nonempty` instance

See https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/initialize.20structure.20with.20IO.2ERef/near/564920245
-/

structure Foo where
  ref : IO.Ref Nat

def mkFoo : IO Foo := do
  let ref ← IO.mkRef 0
  return { ref }

/-- error: failed to synthesize 'Inhabited' or 'Nonempty' instance for
  Foo

If this type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it. -/
#guard_msgs in
initialize _foo : Foo ← mkFoo

-- The fix: adding `deriving Nonempty` makes it work
structure Bar where
  ref : IO.Ref Nat
  deriving Nonempty

def mkBar : IO Bar := do
  let ref ← IO.mkRef 0
  return { ref }

initialize _bar : Bar ← mkBar
