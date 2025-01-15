/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.System.IO
universe u

/-!
Basic random number generator support based on the one
available on the Haskell library
-/

/-- Interface for random number generators. -/
class RandomGen (g : Type u) where
  /-- `range` returns the range of values returned by
      the generator. -/
  range : g → Nat × Nat
  /-- `next` operation returns a natural number that is uniformly distributed
      the range returned by `range` (including both end points),
     and a new generator. -/
  next  : g → Nat × g
  /--
    The 'split' operation allows one to obtain two distinct random number
    generators. This is very useful in functional programs (for example, when
    passing a random number generator down to recursive calls). -/
  split : g → g × g

/-- "Standard" random number generator. -/
structure StdGen where
  s1 : Nat
  s2 : Nat

instance : Inhabited StdGen := ⟨{ s1 := 0, s2 := 0 }⟩

def stdRange := (1, 2147483562)

instance : Repr StdGen where
  reprPrec | ⟨s1, s2⟩, _ => Std.Format.bracket "⟨" (repr s1 ++ ", " ++ repr s2) "⟩"

def stdNext : StdGen → Nat × StdGen
  | ⟨s1, s2⟩ =>
    let k    : Int := Int.ofNat (s1 / 53668)
    let s1'  : Int := 40014 * (Int.ofNat s1 - k * 53668) - k * 12211
    let s1'' : Nat := if s1' < 0 then (s1' + 2147483563).toNat else s1'.toNat
    let k'   : Int := Int.ofNat (s2 / 52774)
    let s2'  : Int := 40692 * (Int.ofNat s2 - k' * 52774) - k' * 3791
    let s2'' : Nat := if s2' < 0 then (s2' + 2147483399).toNat else s2'.toNat
    let z    : Int := Int.ofNat s1'' - Int.ofNat s2''
    let z'   : Nat := if z < 1 then (z + 2147483562).toNat else z.toNat % 2147483562
    (z', ⟨s1'', s2''⟩)

def stdSplit : StdGen → StdGen × StdGen
  | g@⟨s1, s2⟩ =>
    let newS1  := if s1 = 2147483562 then 1 else s1 + 1
    let newS2  := if s2 = 1          then 2147483398 else s2 - 1
    let newG   := (stdNext g).2
    let leftG  := StdGen.mk newS1 newG.2
    let rightG := StdGen.mk newG.1 newS2
    (leftG, rightG)

instance : RandomGen StdGen := {
  range  := fun _ => stdRange,
  next   := stdNext,
  split  := stdSplit
}

/-- Return a standard number generator. -/
def mkStdGen (s : Nat := 0) : StdGen :=
  let q  := s / 2147483562
  let s1 := s % 2147483562
  let s2 := q % 2147483398
  ⟨s1 + 1, s2 + 1⟩

/--
Auxiliary function for randomNatVal.
Generate random values until we exceed the target magnitude.
`genLo` and `genMag` are the generator lower bound and magnitude.
The parameter `r` is the "remaining" magnitude.
-/
private partial def randNatAux {gen : Type u} [RandomGen gen] (genLo genMag : Nat) : Nat → (Nat × gen) → Nat × gen
  | 0,        (v, g) => (v, g)
  | r'@(_+1), (v, g) =>
    let (x, g') := RandomGen.next g
    let v'      := v*genMag + (x - genLo)
    randNatAux genLo genMag (r' / genMag - 1) (v', g')

/-- Generate a random natural number in the interval [lo, hi]. -/
def randNat {gen : Type u} [RandomGen gen] (g : gen) (lo hi : Nat) : Nat × gen :=
  let lo'            := if lo > hi then hi else lo
  let hi'            := if lo > hi then lo else hi
  let (genLo, genHi) := RandomGen.range g
  let genMag         := genHi - genLo + 1
      /-
        Probabilities of the most likely and least likely result
        will differ at most by a factor of (1 +- 1/q).  Assuming the RandomGen
        is uniform, of course
      -/
  let q       := 1000
  let k       := hi' - lo' + 1
  let tgtMag  := k * q
  let (v, g') := randNatAux genLo genMag tgtMag (0, g)
  let v'      := lo' + (v % k)
  (v', g')

/-- Generate a random Boolean. -/
def randBool {gen : Type u} [RandomGen gen] (g : gen) : Bool × gen :=
  let (v, g') := randNat g 0 1
  (v = 1, g')

initialize IO.stdGenRef : IO.Ref StdGen ←
  let seed := UInt64.toNat (ByteArray.toUInt64LE! (← IO.getRandomBytes 8))
  IO.mkRef (mkStdGen seed)

def IO.setRandSeed (n : Nat) : BaseIO Unit :=
  IO.stdGenRef.set (mkStdGen n)

def IO.rand (lo hi : Nat) : BaseIO Nat := do
  let gen ← IO.stdGenRef.get
  let (r, gen) := randNat gen lo hi
  IO.stdGenRef.set gen
  pure r
