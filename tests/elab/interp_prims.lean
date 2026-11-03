/-!
Tests the `USize`, `UInt64` and `Array.uget`/`uset` primitives that the IR interpreter evaluates
in place instead of calling their boxed native wrappers: wrap-around, division by zero, shift
amounts at least the bit width, big `Nat` conversions, and the borrow/ownership of array arguments.
-/

@[noinline] def usizeOps (a b : USize) : List Nat :=
  [(a + b).toNat, (a - b).toNat, (a * b).toNat, (a / b).toNat, (a % b).toNat,
   (a &&& b).toNat, (a ||| b).toNat, (a ^^^ b).toNat, (a <<< b).toNat, (a >>> b).toNat,
   (a.toUInt64 + 1).toNat]

@[noinline] def usizeCmp (a b : USize) : List Bool :=
  [a == b, decide (a < b), decide (a ≤ b)]

@[noinline] def usizeOfNat (n : Nat) : Nat := (USize.ofNat n).toNat

@[noinline] def uint64Ops (a b : UInt64) : List Nat :=
  [(a + b).toNat, (a - b).toNat, (a * b).toNat, (a / b).toNat, (a % b).toNat,
   (a &&& b).toNat, (a ||| b).toNat, (a ^^^ b).toNat, (a <<< b).toNat, (a >>> b).toNat,
   a.toUSize.toNat]

@[noinline] def uint64Cmp (a b : UInt64) : List Bool :=
  [a == b, decide (a < b), decide (a ≤ b)]

#eval usizeOps (-1) 2

#eval usizeOps (-4) 9

#eval usizeOps 7 0

#eval usizeOps 7 65

#eval [usizeCmp 1 (-1), usizeCmp 5 5, usizeCmp (-1) 0]

#eval [usizeOfNat (2^70 + 5), usizeOfNat (2^64 - 1), usizeOfNat (2^64)]

#eval uint64Ops 7 0

#eval uint64Ops 7 65

#eval uint64Ops (-1) 2

#eval [uint64Cmp 1 (-1), uint64Cmp 5 5, uint64Cmp (-1) 0]

/-! `for` loops over arrays use `Array.usize` and `Array.uget`. -/

@[noinline] def sumLens (xs : Array String) : Nat := Id.run do
  let mut s := 0
  for x in xs do
    s := s + x.length
  return s

@[noinline] def setAll (xs : Array String) (v : String) : Array String := Id.run do
  let mut ys := xs
  let mut i : USize := 0
  while h : i.toNat < ys.size do
    ys := ys.uset i (v ++ ys.uget i h) h
    i := i + 1
  return ys

#eval
  let xs := #["ab", "cde", "f"].map (· ++ "")
  (sumLens (xs.push "123456"), setAll xs "!", xs)

#eval setAll #["x", "yz"].toList.toArray "?"

@[noinline] unsafe def firstBorrowed (xs : Array String) : String :=
  if h : (0 : USize).toNat < xs.size then (xs.ugetBorrowed 0 h).push '.' else ""

#eval
  let xs := #["a", "b"].map (· ++ "")
  (unsafe firstBorrowed xs, xs)
