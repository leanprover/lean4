/-!
Tests the IR interpreter's calls to `@[extern]` runtime primitives on `Nat`, `UIntX`/`USize`, and
`Array`. Covers small and big (heap-allocated) `Nat`s, wrap-around and large `UInt64`/`USize` values,
borrowed vs. owned arguments, erased arguments, and copy-on-write of shared arrays. All helpers are
`@[noinline]` so the primitive calls are executed by the interpreter rather than constant-folded.
-/

/-! ## `Nat` -/

@[noinline] def natOps (a b : Nat) : List Nat :=
  [a + b, a - b, b - a, a * b, a / b, a % b, a / 0, a % 0, Nat.pred a,
   a &&& b, a ||| b, a ^^^ b, a >>> 3]

@[noinline] def natCmps (a b : Nat) : List Bool :=
  [a == b, a != b, decide (a = b), decide (a ≤ b), decide (a < b), Nat.ble a b]

/-- info: [10, 4, 0, 21, 2, 1, 0, 7, 6, 3, 7, 4, 0] -/
#guard_msgs in #eval natOps 7 3

/-- info: [false, true, false, false, false, false] -/
#guard_msgs in #eval natCmps 7 3

def big : Nat := 2 ^ 100 + 12345

/--
info: [1267650600228229401496704500066, 1267650600228229401496701935376, 0, 1625565408949668831862289887728435745,
 988540993436422648738602, 636031, 0, 1267650600228229401496703217721, 1267650600228229401496703217720, 4137,
 1267650600228229401496704495929, 1267650600228229401496704491792, 158456325028528675187087902215]
-/
#guard_msgs in #eval natOps big 1282345

/-- info: [false, true, false, false, false, false] -/
#guard_msgs in #eval natCmps big 1282345

/-- info: [true, false, true, true, false, true] -/
#guard_msgs in #eval natCmps big big

@[noinline] def natDivExact (a : Nat) : Nat := Nat.divExact (a * 3) 3 (Nat.dvd_mul_left 3 a)

/-- info: 1267650600228229401496703217721 -/
#guard_msgs in #eval natDivExact big

/-- Borrowed big-`Nat` arguments are used repeatedly after the calls. -/
@[noinline] def natLoop (x : Nat) : Nat → Nat → Nat
  | 0, acc => acc + x
  | n + 1, acc => natLoop x n (acc + x * 2 - x / 2 + x % 7)

/-- info: 1902743550942572331646551529805721 -/
#guard_msgs in #eval natLoop big 1000 0

/-! ## `UIntX` / `USize` -/

@[noinline] def u8Ops (a b : UInt8) : List UInt8 :=
  [a + b, a - b, b - a, a * b, a / b, a % b, a / 0, a &&& b, a ||| b, a ^^^ b, a <<< 3, a >>> 3,
   ~~~a, -a, UInt8.log2 a]

/-- info: [4, 240, 16, 196, 25, 0, 0, 10, 250, 240, 208, 31, 5, 6, 7] -/
#guard_msgs in #eval u8Ops 250 10

@[noinline] def u16Ops (a b : UInt16) : List UInt16 :=
  [a + b, a - b, a * b, a / b, a % b, a <<< 15, a >>> 1, ~~~a, -a, UInt16.log2 a]

/-- info: [4, 65520, 65476, 6553, 0, 0, 32765, 5, 6, 15] -/
#guard_msgs in #eval u16Ops 65530 10

@[noinline] def u32Ops (a b : UInt32) : List UInt32 :=
  [a + b, a - b, a * b, a / b, a % b, a <<< 31, a >>> 1, ~~~a, -a, UInt32.log2 a]

/-- info: [4, 4294967280, 4294967236, 429496729, 0, 0, 2147483645, 5, 6, 31] -/
#guard_msgs in #eval u32Ops 4294967290 10

@[noinline] def u64Ops (a b : UInt64) : List UInt64 :=
  [a + b, a - b, a * b, a / b, a % b, a <<< 63, a >>> 1, ~~~a, -a, UInt64.log2 a,
   a &&& b, a ||| b, a ^^^ b]

/--
info: [4, 18446744073709551600, 18446744073709551556, 1844674407370955161, 0, 0, 9223372036854775805, 5, 6, 63, 10,
 18446744073709551610, 18446744073709551600]
-/
#guard_msgs in #eval u64Ops 18446744073709551610 10

@[noinline] def usizeOps (a b : USize) : List USize :=
  [a + b, a - b, a * b, a / b, a % b, a >>> 1, ~~~a, -a, USize.log2 a, a &&& b, a ||| b, a ^^^ b]

/--
info: [4, 18446744073709551600, 18446744073709551556, 1844674407370955161, 0, 9223372036854775805, 5, 6, 63, 10,
 18446744073709551610, 18446744073709551600]
-/
#guard_msgs in #eval usizeOps (USize.ofNat 18446744073709551610) 10

@[noinline] def u64Cmps (a b : UInt64) : List Bool :=
  [a == b, decide (a = b), decide (a < b), decide (a ≤ b), decide (b < a), decide (b ≤ a)]

/-- info: [false, false, false, false, true, true] -/
#guard_msgs in #eval u64Cmps 18446744073709551610 10

@[noinline] def uCmps (a b : UInt8) (c d : UInt16) (e f : UInt32) (g h : USize) : List Bool :=
  [a == b, decide (a < b), decide (a ≤ b), c == d, decide (c < d), decide (c ≤ d),
   e == f, decide (e < f), decide (e ≤ f), g == h, decide (g < h), decide (g ≤ h)]

/-- info: [false, true, true, true, false, true, false, false, false, false, true, true] -/
#guard_msgs in #eval uCmps 1 2 3 3 6 5 7 8

/-- Conversions between `Nat`, `BitVec`, `Bool` and the unsigned types, including big `Nat`s. -/
@[noinline] def uConvs (n : Nat) (x : UInt64) (b : Bool) : List Nat :=
  [(UInt8.ofNat n).toNat, (UInt16.ofNat n).toNat, (UInt32.ofNat n).toNat, (UInt64.ofNat n).toNat,
   (USize.ofNat n).toNat, x.toNat, x.toUInt8.toNat, x.toUInt16.toNat, x.toUInt32.toNat,
   x.toUSize.toNat, x.toUInt32.toUInt64.toNat, x.toUInt8.toUInt16.toUInt32.toUInt64.toNat,
   (UInt64.ofBitVec (BitVec.ofNat 64 n)).toNat, x.toBitVec.toNat, b.toUInt8.toNat, b.toUInt64.toNat,
   b.toUSize.toNat, x.toUSize.toUInt64.toNat]

/--
info: [57, 12345, 12345, 12345, 12345, 18446744073709551610, 250, 65530, 4294967290, 18446744073709551610, 4294967290, 250,
 12345, 18446744073709551610, 1, 1, 1, 18446744073709551610]
-/
#guard_msgs in #eval uConvs 12345 18446744073709551610 true

/-- info: [57, 12345, 12345, 12345, 12345, 0, 0, 0, 0, 0, 0, 0, 12345, 0, 0, 0, 0, 0] -/
#guard_msgs in #eval uConvs big 0 false

/-! ## `Array` -/

@[noinline] def arrBasics (xs : Array Nat) (i : Nat) (j : USize) : List Nat :=
  [xs.size, xs.usize.toNat, xs[i]!, xs[i]?.getD 0, xs.getD 100 7,
   if h : j.toNat < xs.size then xs.uget j h else 0,
   (xs.set! i 42)[i]!,
   (if h : j.toNat < xs.size then xs.uset j 43 h else xs)[j.toNat]!,
   (xs.swapIfInBounds 0 i)[0]!,
   xs.pop.size, (Array.mkEmpty (α := Nat) 10).size, (Array.emptyWithCapacity (α := Nat) 3).size]

/-- info: ["4", "4", "big", "big", "7", "2", "42", "43", "big", "3", "0", "0"] -/
#guard_msgs in #eval
  let r := arrBasics #[1, 2, 3, big] 3 1
  r.map fun n => if n == big then "big" else toString n

/-- Shared arrays must be copied on update; the original is still observable afterwards. -/
@[noinline] def arrShared (xs : Array Nat) : Array Nat × Array Nat × Array Nat × Array Nat :=
  (xs, xs.set! 0 100, xs.swapIfInBounds 0 2, xs.pop)

/-- info: (#[1, 2, 3], #[100, 2, 3], #[3, 2, 1], #[1, 2]) -/
#guard_msgs in #eval arrShared #[1, 2, 3]

/-- Unshared updates in a loop: elements are big `Nat`s so a missing `inc`/`dec` would be visible. -/
@[noinline] def arrLoop (xs : Array Nat) : Nat → Array Nat
  | 0 => xs
  | n + 1 =>
    let i := n % xs.size
    let xs := xs.set! i (xs[i]! + big)
    let xs := xs.swapIfInBounds i ((i + 1) % xs.size)
    arrLoop xs n

/-- info: 126768862974623624837874811881753166 -/
#guard_msgs in #eval (arrLoop #[big, 1, big, 2, big] 100000).foldl (· + ·) 0

/-- `USize`-indexed loop, the shape of compiled `for` loops over arrays. -/
@[noinline] partial def arrUSum (xs : Array Nat) (i : USize) (acc : Nat) : Nat :=
  if h : i.toNat < xs.size then arrUSum xs (i + 1) (acc + xs.uget i h) else acc

/-- info: 2535301200456458802993406435445 -/
#guard_msgs in #eval arrUSum #[big, 1, big, 2] 0 0

/-- `Array.replicate`, `push` and `for` loops (compiled to `uget`-based code). -/
@[noinline] def arrFor (n : Nat) : Nat := Id.run do
  let mut xs := Array.replicate n big
  xs := xs.push 5
  let mut acc := 0
  for x in xs do
    acc := acc + x % 1000
  return acc

/-- info: 721005 -/
#guard_msgs in #eval arrFor 1000
