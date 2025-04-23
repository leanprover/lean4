

def tst : IO (OptionArg Nat) := do
let x? : OptionArg Nat ← pure none;
pure x?

def tst2 (x : Nat) : IO (OptionArg Nat) := do
let x? : OptionArg Nat := x;
if x?.isNone then
  /-
    We need the `some` because we propagate the expected type at `pure` applications.
    The expected type is `IO (OptionArg Nat)`, and we elaborate `x+1` with expected type
    `OptionArg Nat`, which forces us the elaborator (to try) to synthesize `[Add (OptionArg Nat)]`.
    If we disable expected type propagation for `pure` we can elaborate it without `some`.
    The `x+1` will be elaborated without an expected type. We will infer the type
    `?m Nat` for `pure (x+1)`, and coercions are used to convert it into `IO (OptionArg Nat)`.
  -/
  return some (x+1)
else
  return x?
