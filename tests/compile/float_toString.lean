/-!
Checks that `Float.toString` and `Float32.toString` print the shortest decimal that reads back to
the same value, laid out as Python's `repr`: positional notation from `1e-4` up to `1e16`,
scientific notation outside, and always a `.` or an `e`. The inputs cover the layout boundaries,
subnormals, the largest finite values, infinities and NaN, and `-0.0` under `Repr`. For
pseudo-random bit patterns, the output is read back with `Lean.Syntax.decodeScientificLitVal?` and
`OfScientific.ofScientific`, as a literal is, and compared bit for bit with the input.
-/

def floats : List Float :=
  [0.1, 0.2, 0.1 + 0.2, 1.0, -1.0, 0.0, -0.0, 100.0, 123.456, 1e15, 1e16, 9007199254740993.0,
   1e22, 1.5e300, 1.7976931348623157e308, 0.0001, 0.00012, 0.00001, 1e-9, 0.1234567,
   2.2250738585072014e-308, 5e-324, 1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0]

def floats32 : List Float32 :=
  [0.1, 0.2, 0.1 + 0.2, 1.0, -1.0, 0.0, -0.0, 16777216.0, 16777217.0, 3.4028235e38, 1e-9,
   1.17549435e-38, 1e-45, 1.0 / 0.0, 0.0 / 0.0]

/-- Reads a printed number back the way a literal is read. -/
def readBack (s : String) : Option Float :=
  let (neg, s) := if s.startsWith "-" then (true, (s.dropPrefix "-").toString) else (false, s)
  (Lean.Syntax.decodeScientificLitVal? s).map fun (m, sign, e) =>
    let x : Float := OfScientific.ofScientific m sign e
    if neg then -x else x

def readBack32 (s : String) : Option Float32 :=
  let (neg, s) := if s.startsWith "-" then (true, (s.dropPrefix "-").toString) else (false, s)
  (Lean.Syntax.decodeScientificLitVal? s).map fun (m, sign, e) =>
    let x : Float32 := OfScientific.ofScientific m sign e
    if neg then -x else x

/-- The first `n` outputs of a 64-bit linear congruential generator. -/
def randomBits (n : Nat) : Array UInt64 := Id.run do
  let mut state : UInt64 := 0x9e3779b97f4a7c15
  let mut out := #[]
  for _ in [0:n] do
    state := state * 6364136223846793005 + 1442695040888963407
    out := out.push state
  return out

/-- Reports how many finite values among `bits` were checked and how many did not read back. -/
def report (label : String) (bits : Array UInt64) (check : UInt64 → Option Bool) : IO Bool := do
  let results := bits.filterMap check
  let failures := results.filter (!·) |>.size
  IO.println s!"{label}: {results.size} finite values, {failures} failures"
  return failures == 0

def main : IO UInt32 := do
  for x in floats do
    IO.println x
  for x in floats32 do
    IO.println x
  IO.println (repr (some (-0.0 : Float)))
  IO.println (repr (some (-1.5 : Float)))
  IO.println (repr (some (-0.0 : Float32)))
  let bits := randomBits 2000
  let ok64 ← report "Float round trip" bits fun b =>
    let x := Float.ofBits b
    if x.isFinite then some ((readBack x.toString).map Float.toBits == some x.toBits) else none
  let ok32 ← report "Float32 round trip" bits fun b =>
    let y := Float32.ofBits (b >>> 32).toUInt32
    if y.isFinite then some ((readBack32 y.toString).map Float32.toBits == some y.toBits) else none
  return if ok64 && ok32 then 0 else 1
