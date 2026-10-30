/-!
Checks that the `memcmp`-based implementations of the `LT`, `LE`, `BEq` and `Ord` instances on
`String.Slice` agree with the corresponding operations on `String.Slice.copy` and with an independent
reference implementation. The inputs cover all short slices over an alphabet straddling the boundary
between `0x7f` and `0x80` at varying offsets into their underlying strings, as well as long slices
that differ at word and vector boundaries or are prefixes of each other.
-/

open String (Slice)

structure Results where
  lt : Bool
  le : Bool
  gt : Bool
  ge : Bool
  cmp : Ordering
  beq : Bool
deriving BEq, Repr

/-- Uses the `Slice` instances directly. -/
@[noinline] def viaRuntime (s t : Slice) : Results where
  lt := decide (s < t)
  le := decide (s ≤ t)
  gt := decide (s > t)
  ge := decide (s ≥ t)
  cmp := compare s t
  beq := s == t

/-- Goes through instance dictionaries, which exercises the boxed entry points. -/
@[noinline, nospecialize] def viaInstances {α : Type} [LT α] [DecidableLT α] [LE α] [DecidableLE α]
    [Ord α] [BEq α] (a b : α) : Results where
  lt := decide (a < b)
  le := decide (a ≤ b)
  gt := decide (a > b)
  ge := decide (a ≥ b)
  cmp := compare a b
  beq := a == b

/-- Goes through the instances provided by the `LinearPreorderPackage`. -/
@[noinline, nospecialize] def viaPackage {α : Type} [Std.LinearPreorderPackage α] (a b : α) :
    Results :=
  viaInstances a b

/-- Evaluates the logical definitions, which are stated in terms of `String.Slice.copy`. -/
@[noinline] def viaCopy (s t : Slice) : Results where
  lt := decide (s.copy < t.copy)
  le := decide (s.copy ≤ t.copy)
  gt := decide (t.copy < s.copy)
  ge := decide (t.copy ≤ s.copy)
  cmp := compare s.copy t.copy
  beq := s.copy == t.copy

def refCompare : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    if x.toNat < y.toNat then .lt else if y.toNat < x.toNat then .gt else refCompare xs ys

@[noinline] def viaReference (s t : Slice) : Results :=
  let c := refCompare s.copy.toUTF8.toList t.copy.toUTF8.toList
  { lt := c == .lt
    le := c != .gt
    gt := c == .gt
    ge := c != .lt
    cmp := c
    beq := c == .eq }

structure Stats where
  lt : Nat := 0
  eq : Nat := 0
  gt : Nat := 0
  failures : Array String := #[]

def describe (s : Slice) : String :=
  s!"{s.copy.toUTF8} (bytes {s.startInclusive.offset.byteIdx} to {s.endExclusive.offset.byteIdx} of {s.str.toUTF8})"

def check (s t : Slice) : StateM Stats Unit := do
  let expected := viaReference s t
  let results := [("runtime", viaRuntime s t), ("instances", viaInstances s t),
    ("package", viaPackage s t), ("copy", viaCopy s t)]
  for (name, r) in results do
    unless r == expected do
      let msg := s!"{name} disagrees with reference on {describe s} vs {describe t}:\n{repr r}\nexpected\n{repr expected}"
      modify fun s => { s with failures := s.failures.push msg }
  match expected.cmp with
  | .lt => modify fun s => { s with lt := s.lt + 1 }
  | .eq => modify fun s => { s with eq := s.eq + 1 }
  | .gt => modify fun s => { s with gt := s.gt + 1 }

def checkBoth (s t : Slice) : StateM Stats Unit := do
  check s t
  check t s

def report (name : String) (m : StateM Stats Unit) : IO Bool := do
  let (_, s) := Id.run (m.run {})
  IO.println s!"{name}: {s.lt} lt, {s.eq} eq, {s.gt} gt, {s.failures.size} failures"
  for f in s.failures.extract 0 10 do
    IO.println f
  return s.failures.isEmpty

/--
Characters whose encodings contain bytes on both sides of the boundary between `0x7f` and `0x80`,
which a signed comparison gets wrong. `é` and `ÿ` only differ in their second byte.
-/
def alphabet : List Char := ['a', '\x7f', 'é', 'ÿ', '€']

def allUpTo : Nat → List String
  | 0 => [""]
  | n + 1 => "" :: (alphabet.flatMap fun c => (allUpTo n).map (c.toString ++ ·))

/-- All slices of `s` that start and end at character boundaries. -/
def slicesOf (s : String) : List Slice := Id.run do
  let n := s.length
  let mut r := []
  for i in 0...=n do
    for j in i...=n do
      r := ((s.toSlice.drop i).take (j - i)) :: r
  return r

def exhaustive : StateM Stats Unit := do
  let xs := (allUpTo 2).flatMap slicesOf
  for s in xs do
    for t in xs do
      check s t

/-- A slice with contents `s` that does not start at the beginning of its underlying string. -/
def embed (s : String) : Slice :=
  (("x" ++ s ++ "yz").toSlice.drop 1).dropEnd 2

def lengths : List Nat :=
  [1, 4, 8, 16, 17, 32, 33, 64, 65, 128, 129, 257]

/--
Compares `n` copies of `é` (`c3 a9`) with a copy in which the `k`-th character is replaced by
`ÿ` (`c3 bf`), `Ù` (`c3 99`) or `\x7f\x7f` (`7f 7f`), as well as with prefixes of both and with
a slice of the same contents at a different offset.
-/
def boundaries : StateM Stats Unit := do
  for n in lengths do
    let base := String.ofList (List.replicate n 'é')
    let positions := [0, 1, 3, 4, 7, 8, 15, 16, 31, 32, n / 2, n - 1].filter (· < n)
    checkBoth (embed base) base.toSlice
    for k in positions do
      checkBoth base.toSlice (base.toSlice.take k)
      checkBoth (embed base) (base.toSlice.take k)
      for c in ["ÿ", "Ù", "\x7f\x7f"] do
        let modified := String.ofList (List.replicate k 'é') ++ c ++
          String.ofList (List.replicate (n - k - 1) 'é')
        for (s, t) in [(base.toSlice, modified.toSlice), (embed base, modified.toSlice),
            (base.toSlice, embed modified), (embed base, embed modified)] do
          checkBoth s t
          checkBoth (s.take k) t
          checkBoth (s.take (k + 1)) t
          checkBoth s (t.take (k + 1))

def main : IO UInt32 := do
  let mut ok := true
  ok := (← report "exhaustive" exhaustive) && ok
  ok := (← report "boundaries" boundaries) && ok
  return if ok then 0 else 1
