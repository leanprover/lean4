/-!
Checks that the `memcmp`-based runtime implementations behind the `LT`, `LE`, `BEq`,
`DecidableEq`, `Ord`, `Min` and `Max` instances on `ByteArray` agree with the logical definitions
in terms of `Array UInt8` and with an independent reference implementation. The inputs cover all
short byte arrays over an alphabet straddling the signed/unsigned boundary, long byte arrays that
differ at word and vector boundaries, prefixes, differing capacities, and random pairs.
-/

structure Results where
  lt : Bool
  le : Bool
  gt : Bool
  ge : Bool
  cmp : Ordering
  beq : Bool
  deq : Bool
  min : List UInt8
  max : List UInt8
deriving BEq, Repr

/-- Uses the `ByteArray` instances directly, which compile to calls into the runtime. -/
@[noinline] def viaRuntime (a b : ByteArray) : Results where
  lt := decide (a < b)
  le := decide (a ≤ b)
  gt := decide (a > b)
  ge := decide (a ≥ b)
  cmp := compare a b
  beq := a == b
  deq := decide (a = b)
  min := (min a b).toList
  max := (max a b).toList

/-- Goes through instance dictionaries, which exercises the boxed entry points of the runtime. -/
@[noinline, nospecialize] def viaInstances {α : Type} [LT α] [DecidableLT α] [LE α] [DecidableLE α]
    [Ord α] [BEq α] [DecidableEq α] [Min α] [Max α] (toList : α → List UInt8) (a b : α) : Results where
  lt := decide (a < b)
  le := decide (a ≤ b)
  gt := decide (a > b)
  ge := decide (a ≥ b)
  cmp := compare a b
  beq := a == b
  deq := decide (a = b)
  min := toList (min a b)
  max := toList (max a b)

/-- Evaluates the bodies of the definitions, which are stated in terms of `Array UInt8`. -/
@[noinline] def viaArray (a b : ByteArray) : Results where
  lt := decide (a.data < b.data)
  le := decide (a.data ≤ b.data)
  gt := decide (b.data < a.data)
  ge := decide (b.data ≤ a.data)
  cmp := compare a.data b.data
  beq := a.data == b.data
  deq := decide (a.data = b.data)
  min := if a.data ≤ b.data then a.data.toList else b.data.toList
  max := if b.data ≤ a.data then a.data.toList else b.data.toList

def refCompare : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    if x.toNat < y.toNat then .lt else if y.toNat < x.toNat then .gt else refCompare xs ys

@[noinline] def viaReference (a b : ByteArray) : Results :=
  let c := refCompare a.toList b.toList
  { lt := c == .lt
    le := c != .gt
    gt := c == .gt
    ge := c != .lt
    cmp := c
    beq := c == .eq
    deq := c == .eq
    min := if c != .gt then a.toList else b.toList
    max := if c != .lt then a.toList else b.toList }

structure Stats where
  lt : Nat := 0
  eq : Nat := 0
  gt : Nat := 0
  failures : Array String := #[]

def check (a b : ByteArray) : StateM Stats Unit := do
  let expected := viaReference a b
  let results := [("runtime", viaRuntime a b), ("instances", viaInstances ByteArray.toList a b),
    ("array", viaArray a b)]
  for (name, r) in results do
    unless r == expected do
      let msg := s!"{name} disagrees with reference on {a} vs {b}:\n{repr r}\nexpected\n{repr expected}"
      modify fun s => { s with failures := s.failures.push msg }
  match expected.cmp with
  | .lt => modify fun s => { s with lt := s.lt + 1 }
  | .eq => modify fun s => { s with eq := s.eq + 1 }
  | .gt => modify fun s => { s with gt := s.gt + 1 }

def checkAll (xs ys : Array ByteArray) : StateM Stats Unit := do
  for a in xs do
    for b in ys do
      check a b

def checkBoth (a b : ByteArray) : StateM Stats Unit := do
  check a b
  check b a

def report (name : String) (m : StateM Stats Unit) : IO Bool := do
  let (_, s) := Id.run (m.run {})
  IO.println s!"{name}: {s.lt} lt, {s.eq} eq, {s.gt} gt, {s.failures.size} failures"
  for f in s.failures.extract 0 10 do
    IO.println f
  return s.failures.isEmpty

/-- Bytes on both sides of the boundary between `0x7f` and `0x80`, which a signed comparison gets wrong. -/
def alphabet : List UInt8 := [0x00, 0x01, 0x7f, 0x80, 0xff]

def allUpTo : Nat → List (List UInt8)
  | 0 => [[]]
  | n + 1 => [] :: (alphabet.flatMap fun x => (allUpTo n).map (x :: ·))

def exhaustive : StateM Stats Unit := do
  let xs := (allUpTo 3).toArray.map List.toByteArray
  checkAll xs xs

def pattern (n : Nat) : ByteArray := Id.run do
  let mut r := ByteArray.emptyWithCapacity n
  for i in 0...n do
    r := r.push (i * 37 + 11).toUInt8
  return r

def lengths : List Nat :=
  [1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 255, 256, 257, 4096, 4097]

def boundaries : StateM Stats Unit := do
  for n in lengths do
    let a := pattern n
    let positions := [0, 1, 7, 8, 15, 16, 31, 32, 63, 64, n / 2, n - 2, n - 1].filter (· < n)
    for i in positions do
      let x := a[i]!
      for y in [0x00, 0x7f, 0x80, 0xff, x + 1, x - 1] do
        checkBoth a (a.set! i y)
    for m in 0 :: lengths do
      checkBoth a (pattern m)
      checkBoth a ((pattern m).push 0x00)
      checkBoth a ((pattern m).push 0xff)

def capacities : StateM Stats Unit := do
  let xs := #[ByteArray.empty, ByteArray.emptyWithCapacity 100, [1, 2].toByteArray,
    ((ByteArray.emptyWithCapacity 100).push 1).push 2, ((ByteArray.emptyWithCapacity 1).push 1).push 2,
    "hello".toUTF8, [104, 101, 108, 108, 111].toByteArray, (pattern 100).extract 10 20,
    (pattern 20).extract 10 20, (pattern 100).copySlice 10 ByteArray.empty 0 10 (exact := false)]
  checkAll xs xs

def next (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

def randomBytes (s : UInt64) (n : Nat) : UInt64 × ByteArray := Id.run do
  let mut s := s
  let mut r := ByteArray.empty
  for _ in 0...n do
    s := next s
    r := r.push alphabet[(s % 5).toNat]!
  return (s, r)

/-- Pairs `(a, b)` where `b` is often a small modification of `a`, so that long common prefixes and
equal arrays are frequent. -/
def random (iters : Nat) : StateM Stats Unit := do
  let mut s : UInt64 := 0x2545F4914F6CDD1D
  for _ in 0...iters do
    s := next s
    let (s', a) := randomBytes s (s % 41).toNat
    s := next s'
    let mut b := a
    match s % 5 with
    | 0 => pure ()
    | 1 => b := a.extract 0 ((s >>> 8) % 41).toNat
    | 2 => b := a.push alphabet[((s >>> 8) % 5).toNat]!
    | 3 =>
      if a.size ≠ 0 then
        b := a.set! ((s >>> 8).toNat % a.size) alphabet[((s >>> 16) % 5).toNat]!
    | _ =>
      let (s', b') := randomBytes s ((s >>> 8) % 41).toNat
      s := s'
      b := b'
    check a b

def main : IO UInt32 := do
  let mut ok := true
  ok := (← report "exhaustive" exhaustive) && ok
  ok := (← report "boundaries" boundaries) && ok
  ok := (← report "capacities" capacities) && ok
  ok := (← report "random" (random 20000)) && ok
  return if ok then 0 else 1
