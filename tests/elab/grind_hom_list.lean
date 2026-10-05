/-!
Tests for `[grind hom]` combined with `List` reasoning, ported from the intblasting prototype
test suite (#15224). The goals come from bedrock2/LiveVerif and mix `BitVec` word arithmetic
with `List.take`/`List.drop`/`List.length`.
-/

-- Shim for prototype names
abbrev BitVec.unsigned {w} (x : BitVec w) : Int := Int.ofNat x.toNat

open BitVec

-- From bedrock2/src/bedrock2/bottom_up_simpl_perf.v

example (s1 s2 : List Nat) (p1_pre p2_pre : BitVec 32) (v : Nat)
    (p1' p2' c1 c2 p1 p2 : BitVec 32)
    (_h_v : v = s1.length - (p1' - p1_pre).toNat)
    (_h_bounds1 : (p1' - p1_pre).toNat ≤ s1.length)
    (_h_bounds2 : (p2' - p2_pre).toNat ≤ s2.length)
    (_h_eq_len : (p1' - p1_pre).unsigned = (p2' - p2_pre).unsigned)
    (_h_eq_slice : List.take (p1' - p1_pre).toNat s1 = List.take (p2' - p2_pre).toNat s2)
    (h_c1 : c1 = BitVec.ofNat 32 ((s1 ++ [0]).getD (p1' - p1_pre).toNat 0))
    (h_c2 : c2 = BitVec.ofNat 32 ((s2 ++ [0]).getD (p2' - p2_pre).toNat 0))
    (_h_p1 : p1 = p1' + 1#32)
    (_h_p2 : p2 = p2' + 1#32)
    (h_c_eq : c1 = c2)
    (h_c1_neq : c1 ≠ 0#32)
    (_h_len_neq : (p1' - p1_pre).toNat ≠ s1.length)
    (h_len_eq : (p2' - p2_pre).toNat = s2.length) :
    False := by grind

example (s1 s2 : List Nat) (p1_pre p2_pre : BitVec 32) (v : Nat)
    (p1' p2' c1 c2 p1 p2 : BitVec 32)
    (_h_v : v = s1.length - (p1' - p1_pre).unsigned)
    (_h_bounds1 : (p1' - p1_pre).unsigned ≤ s1.length)
    (_h_bounds2 : (p2' - p2_pre).unsigned ≤ s2.length)
    (_h_eq_len : (p1' - p1_pre).unsigned = (p2' - p2_pre).unsigned)
    (_h_eq_slice : List.take (p1' - p1_pre).toNat s1 = List.take (p2' - p2_pre).toNat s2)
    (h_c1 : c1 = BitVec.ofNat 32 ((s1 ++ [0]).getD (p1' - p1_pre).toNat 0))
    (h_c2 : c2 = BitVec.ofNat 32 ((s2 ++ [0]).getD (p2' - p2_pre).toNat 0))
    (_h_p1 : p1 = p1' + 1#32)
    (_h_p2 : p2 = p2' + 1#32)
    (h_c_eq : c1 = c2)
    (h_c1_neq : c1 ≠ 0#32)
    (_h_len_neq : (p1' - p1_pre).unsigned ≠ s1.length)
    (h_len_eq : (p2' - p2_pre).unsigned = s2.length) :
    False := by grind

-- From LiveVerif/src/LiveVerifExamples/Tests/SampleSimpls.v

example (_p i j count : BitVec 32) (l : List Nat) (n : Nat)
  (h1 : i.unsigned + count.unsigned ≤ j.unsigned)
  (_h2 : j.toNat + count.toNat ≤ n)
  (_h3 : 2 * n < 2^32)
  (_h4 : l.length = n) :
  (List.take i.toNat l ++
   List.take count.toNat (List.drop (i.toNat + count.toNat + (j - i - count).toNat) l) ++
   List.take (j - (i + count)).toNat (List.drop (i + count).toNat l) ++
   List.take count.toNat (List.drop i.toNat l) ++
   List.drop (i.toNat + count.toNat + (j - i).toNat) l) =
  (List.take i.toNat l ++
   List.take count.toNat (List.drop j.toNat l) ++
   List.take (j - (i + count)).toNat (List.drop (i + count).toNat l) ++
   List.take count.toNat (List.drop i.toNat l) ++
   List.drop (count.toNat + j.toNat) l) := by
  grind (splits := 32)

example (_p i j count : BitVec 32) (l : List Nat) (n : Nat)
  (h1 : i.unsigned + count.unsigned ≤ j.unsigned)
  (_h2 : j.unsigned + count.unsigned ≤ n)
  (_h3 : 2 * n < 2^32)
  (_h4 : l.length = n) :
  (List.take i.toNat l ++
   List.take count.toNat (List.drop (i.toNat + count.toNat + (j - i - count).toNat) l) ++
   List.take (j - (i + count)).toNat (List.drop (i + count).toNat l) ++
   List.take count.toNat (List.drop i.toNat l) ++
   List.drop (i.toNat + count.toNat + (j - i).toNat) l) =
  (List.take i.toNat l ++
   List.take count.toNat (List.drop j.toNat l) ++
   List.take (j - (i + count)).toNat (List.drop (i + count).toNat l) ++
   List.take count.toNat (List.drop i.toNat l) ++
   List.drop (count.toNat + j.toNat) l) := by
  grind (splits := 32)

example (A : Type) (s1 : List A) :
  ((s1.drop 1).length : Int) + 1 ≤ (s1.length : Int) + 1 := by
  grind

example (A : Type) (i : Nat) (a : Int) (s1 : List A) :
  ((s1.take i).length : Int) + a ≤ (s1.length : Int) + a := by
  grind

example (A : Type) (x y z : A) (l : List A) :
  ((l ++ l).length : Int) + ((x :: y :: l).length : Int) + ((x :: y :: z :: []).length : Int) =
  3 * (l.length : Int) + 5 := by
  grind
