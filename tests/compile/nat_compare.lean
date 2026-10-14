/-!
Checks that the runtime implementation of `compare` on `Nat` agrees with a reference implementation
built from `<` and `=`. The inputs straddle the boundary between unboxed and boxed natural numbers on
both 32-bit and 64-bit platforms, and include equal boxed numbers that are distinct objects.
-/

/-- Compiles to a direct call into the runtime. -/
@[noinline] def viaRuntime (a b : Nat) : Ordering :=
  compare a b

/-- Goes through the `Ord` dictionary, which exercises the boxed entry point. -/
@[noinline, nospecialize] def viaInstance {α : Type} [Ord α] (a b : α) : Ordering :=
  compare a b

/-- Branches on the result, which relies on the runtime returning a valid constructor index. -/
@[noinline] def viaMatch (a b : Nat) : String :=
  match compare a b with
  | .lt => "lt"
  | .eq => "eq"
  | .gt => "gt"

@[noinline] def reference (a b : Nat) : Ordering :=
  if a < b then .lt else if a = b then .eq else .gt

def Ordering.name : Ordering → String
  | .lt => "lt"
  | .eq => "eq"
  | .gt => "gt"

/-- Returns a number equal to `n` that, if boxed, is a different object than `n`. -/
@[noinline] def fresh (n : Nat) : Nat :=
  (toString n).toNat!

def values : List Nat :=
  let base := [0, 1, 2, 3, 1000,
    2^31 - 2, 2^31 - 1, 2^31, 2^31 + 1, 2^32 - 1, 2^32, 2^32 + 1,
    2^62 - 1, 2^62, 2^63 - 2, 2^63 - 1, 2^63, 2^63 + 1, 2^64 - 1, 2^64, 2^64 + 1,
    2^127, 2^128 - 1, 2^128, 2^128 + 1, 3^200]
  base ++ base.map fresh

def main : IO UInt32 := do
  let mut lt := 0
  let mut eq := 0
  let mut gt := 0
  let mut failures := 0
  for a in values do
    for b in values do
      let expected := reference a b
      let results := [viaRuntime a b, viaInstance a b]
      unless results.all (· == expected) && viaMatch a b == expected.name do
        failures := failures + 1
        IO.println s!"mismatch on {a} vs {b}: {repr results}, {viaMatch a b}, expected {repr expected}"
      match expected with
      | .lt => lt := lt + 1
      | .eq => eq := eq + 1
      | .gt => gt := gt + 1
  IO.println s!"{lt} lt, {eq} eq, {gt} gt, {failures} failures"
  return if failures == 0 then 0 else 1
