/-!
Tests big `Nat` and `Int` arithmetic (`Init.Data.Nat.BigRuntime`) on pseudo-random operands of many
sizes, including scalar/big boundaries. The expected output was produced with the former GMP-based
implementation; each line is a checksum over all results of one operation.
-/

def rand (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- A number with about `bits` bits; `kind` picks all-ones, a power of two, or random bits. -/
def mkNat (bits : Nat) (s : UInt64) : Nat × UInt64 := Id.run do
  let s := rand s
  match (s >>> 60).toNat % 4 with
  | 0 => return (2^bits - 1, s)
  | 1 => return (2^bits, s)
  | _ =>
    let mut s := s
    let mut n := 0
    for _ in [0:(bits + 63) / 64] do
      s := rand s
      n := n * 2^64 + s.toNat
    return (n % 2^(bits + 1), s)

def sizes : List Nat := [0, 1, 30, 31, 32, 33, 62, 63, 64, 65, 96, 127, 128, 200, 640, 2000]

def P : Nat := 2^61 - 1

structure Sums where
  sums : Array Nat := Array.replicate 40 0

def Sums.add (a : Sums) (i : Nat) (v : Nat) : Sums :=
  ⟨a.sums.modify i fun s => (s * 1000003 + v % P) % P⟩

def Sums.addI (a : Sums) (i : Nat) (v : Int) : Sums :=
  a.add i (if v < 0 then 2 * v.natAbs + 1 else 2 * v.natAbs)

def names : Array String := #["add", "sub", "mul", "div", "mod", "gcd", "land", "lor", "xor",
  "shiftLeft", "shiftRight", "pow", "log2", "lt/le/eq", "toString", "ofString", "UInt8/16/32/64.ofNat",
  "USize.ofNat", "powMod", "Int.add", "Int.sub", "Int.mul", "Int.tdiv", "Int.tmod", "Int.ediv",
  "Int.emod", "Int.neg", "Int.lt/le/eq", "Int8/16/32/64.ofInt", "Int.toNat", "Int.toString",
  "Int.ofString", "Nat.toFloat", "divExact"]

@[noinline] def step (acc : Sums) (a b : Nat) (sa sb : Bool) (e : Nat) : Sums := Id.run do
  let mut acc := acc
  acc := acc.add 0 (a + b)
  acc := acc.add 1 (a - b)
  acc := acc.add 2 (a * b)
  acc := acc.add 3 (a / b)
  acc := acc.add 4 (a % b)
  acc := acc.add 5 (Nat.gcd a b)
  acc := acc.add 6 (a &&& b)
  acc := acc.add 7 (a ||| b)
  acc := acc.add 8 (a ^^^ b)
  acc := acc.add 9 (a <<< (b % 300))
  acc := acc.add 10 (a >>> (b % 300))
  acc := acc.add 11 (a ^ (b % 7))
  acc := acc.add 12 a.log2
  acc := acc.add 13 ((if a < b then 1 else 0) + (if a ≤ b then 2 else 0) + (if a == b then 4 else 0))
  acc := acc.add 14 (toString a).hash.toNat
  acc := acc.add 15 (toString a).toNat!
  acc := acc.add 16 (a.toUInt8.toNat + a.toUInt16.toNat + a.toUInt32.toNat + a.toUInt64.toNat)
  acc := acc.add 17 a.toUSize.toNat
  acc := acc.add 18 (Nat.powMod a e (b + 2))
  let x : Int := if sa then -a else a
  let y : Int := if sb then -b else b
  acc := acc.addI 19 (x + y)
  acc := acc.addI 20 (x - y)
  acc := acc.addI 21 (x * y)
  acc := acc.addI 22 (x.tdiv y)
  acc := acc.addI 23 (x.tmod y)
  acc := acc.addI 24 (x / y)
  acc := acc.addI 25 (x % y)
  acc := acc.addI 26 (-x)
  acc := acc.add 27 ((if x < y then 1 else 0) + (if x ≤ y then 2 else 0) + (if x == y then 4 else 0))
  acc := acc.addI 28 ((Int8.ofInt x).toInt + (Int16.ofInt x).toInt + (Int32.ofInt x).toInt + (Int64.ofInt x).toInt)
  acc := acc.add 29 x.toNat
  acc := acc.add 30 (toString x).hash.toNat
  acc := acc.addI 31 (toString x).toInt!
  acc := acc.add 32 (a.toFloat.toUInt64.toNat)
  if b != 0 then acc := acc.add 33 ((a * b) / b)
  return acc

def main : IO Unit := do
  let mut acc : Sums := {}
  let mut s : UInt64 := 1
  for ba in sizes do
    for bb in sizes do
      for _ in [0:3] do
        let (a, s1) := mkNat ba s
        let (b, s2) := mkNat bb s1
        let (e, s3) := mkNat 70 s2
        s := rand s3
        acc := step acc a b (s &&& 1 == 0) (s &&& 2 == 0) e
        acc := step acc b a (s &&& 4 == 0) (s &&& 8 == 0) e
  for h : i in [0:names.size] do
    IO.println s!"{names[i]}: {acc.sums[i]!}"
  IO.println (2^200 * 3^100 + 17)
  IO.println (-(10^50 : Int) / 7)
