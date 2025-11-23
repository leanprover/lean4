/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fady Adal

Tests for BitVec container operations: OfFn, Count, Map, and Hamming modules.
-/

open BitVec

/-! ## OfFn module tests -/

-- ofFn tests
#guard ofFn (fun i : Fin 4 => i.val % 2 == 0) = 0b0101#4
#guard ofFn (fun _ : Fin 4 => true) = 0b1111#4
#guard ofFn (fun _ : Fin 4 => false) = 0b0000#4
#guard ofFn (fun _ : Fin 0 => false) = nil

-- toList tests
#guard toList 0b1010#4 = [false, true, false, true]
#guard toList 0b1111#4 = [true, true, true, true]
#guard toList 0b0000#4 = [false, false, false, false]
#guard toList nil = []

-- toArray tests
#guard toArray 0b1010#4 = #[false, true, false, true]
#guard toArray 0b1111#4 = #[true, true, true, true]
#guard toArray nil = #[]

-- Roundtrip properties
#guard ofBoolListLE (toList 0b1010#4) = 0b1010#4
#guard ofArray 4 (toArray 0b1010#4) = 0b1010#4
#guard ofVector (toVector 0b1010#4) = 0b1010#4

/-! ## Count module tests -/

-- popcount tests
#guard popcount 0b1010#4 = 2
#guard popcount 0b1111#4 = 4
#guard popcount 0b0000#4 = 0
#guard popcount 0b1001#4 = 2
#guard popcount nil = 0
#guard popcount (0#8) = 0

-- zerocount tests
#guard zerocount 0b1010#4 = 2
#guard zerocount 0b1111#4 = 0
#guard zerocount 0b0000#4 = 4
#guard zerocount 0b0110#4 = 2
#guard zerocount nil = 0
#guard zerocount (0#8) = 8

-- countP tests
#guard countP 0b1010#4 id = 2
#guard countP 0b1010#4 not = 2
#guard countP 0b1111#4 id = 4
#guard countP 0b0000#4 id = 0
#guard countP 0b0000#4 not = 4

-- countIdxP tests (using BOTH index and bit value)
#guard countIdxP 0b1111#4 (fun i b => i.val % 2 == 0 && b) = 2  -- count true bits at even positions
#guard countIdxP 0b1010#4 (fun i b => i.val % 2 == 1 && b) = 2  -- count true bits at odd positions
#guard countIdxP 0b1010#4 (fun i b => i.val % 2 == 0 && !b) = 2  -- count false bits at even positions

-- Relationship tests
#guard popcount 0b1010#4 + zerocount 0b1010#4 = 4
#guard zerocount (~~~0b1010#4) = popcount 0b1010#4
#guard popcount (~~~0b1010#4) = zerocount 0b1010#4

/-! ## Map module tests -/

-- map tests
#guard map 0b1010#4 not = 0b0101#4
#guard map 0b1111#4 id = 0b1111#4
#guard map 0b0000#4 not = 0b1111#4
#guard map nil (fun _ => true) = nil

-- mapIdx tests
#guard mapIdx 0b1111#4 (fun i _ => i.val % 2 == 0) = 0b0101#4
#guard mapIdx 0b1010#4 (fun i b => b && (i.val < 2)) = 0b0010#4

-- zipWith tests
#guard zipWith (· && ·) 0b1100#4 0b1010#4 = 0b1000#4
#guard zipWith (· || ·) 0b1100#4 0b1010#4 = 0b1110#4
#guard zipWith xor 0b1100#4 0b1010#4 = 0b0110#4
#guard zipWith (fun _ _ => true) 0b0000#4 0b0000#4 = 0b1111#4

-- Test relationships
#guard 0b1100#4 &&& 0b1010#4 = zipWith (· && ·) 0b1100#4 0b1010#4
#guard 0b1100#4 ||| 0b1010#4 = zipWith (· || ·) 0b1100#4 0b1010#4
#guard 0b1100#4 ^^^ 0b1010#4 = zipWith xor 0b1100#4 0b1010#4
#guard ~~~0b1010#4 = map 0b1010#4 not

/-! ## Hamming module tests -/

-- dot product tests
#guard dot 0b1100#4 0b1010#4 = 1  -- only position 3 has both bits set
#guard dot 0b1111#4 0b1111#4 = 4  -- all positions match
#guard dot 0b1010#4 0b0101#4 = 0  -- no positions match
#guard dot 0b0000#4 0b1111#4 = 0  -- one vector is zero
#guard dot 0b1010#4 0b1100#4 = dot 0b1100#4 0b1010#4  -- commutative

-- Hamming distance tests
#guard hammingDist 0b1100#4 0b1010#4 = 2  -- differ at positions 0 and 2
#guard hammingDist 0b1111#4 0b1111#4 = 0  -- identical
#guard hammingDist 0b0000#4 0b1111#4 = 4  -- maximum distance
#guard hammingDist 0b1001#4 0b0110#4 = 4  -- differ at all positions
#guard hammingDist 0b1010#4 0b1100#4 = hammingDist 0b1100#4 0b1010#4  -- commutative

-- parity tests
#guard parity 0b1010#4 = false  -- 2 ones, even
#guard parity 0b1011#4 = true   -- 3 ones, odd
#guard parity 0b0000#4 = false  -- 0 ones, even
#guard parity 0b1111#4 = false  -- 4 ones, even
#guard parity 0b0001#4 = true   -- 1 one, odd
#guard parity (0b1010#4 ^^^ 0b1100#4) = (parity 0b1010#4 ^^ parity 0b1100#4)  -- xor distributes

/-! ## Integration tests -/

-- Combining operations from multiple modules
#guard let x := 0b1010#4
      let y := 0b1100#4
      let z := zipWith (· && ·) x y
      popcount z = 1

#guard let x := 0b1111#4
      let mapped := map x not
      popcount mapped = 0

#guard let x := ofFn (fun i : Fin 8 => i.val < 4)
      popcount x = 4

-- Complex predicate: count true bits at even positions
#guard let x := 0b10110101#8
      countIdxP x (fun i b => i.val % 2 == 0 && b) = 3

-- Hamming distance between complementary vectors
#guard let x := 0b1010#4
      hammingDist x (~~~x) = 4

/-! ## Edge cases -/

-- Empty bitvector (width 0)
#guard popcount nil = 0
#guard zerocount nil = 0
#guard dot nil nil = 0
#guard hammingDist nil nil = 0
#guard parity nil = false
#guard map nil id = nil
#guard toList nil = []

-- Single bit vectors
#guard popcount 0b1#1 = 1
#guard popcount 0b0#1 = 0
#guard hammingDist 0b1#1 0b0#1 = 1
#guard parity 0b1#1 = true
#guard parity 0b0#1 = false

-- Large vectors (test performance doesn't regress)
#guard popcount (allOnes 32) = 32
#guard zerocount (0#32) = 32
#guard hammingDist (allOnes 32) (0#32) = 32
