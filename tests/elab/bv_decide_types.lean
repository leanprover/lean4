import Std.Tactic.BVDecide

/-!
Tests for the `types [...]` clause of the `bv_decide` family of tactics, which restricts the
structure and enum inductive analysis to the listed types.
-/

inductive Color where
  | red
  | green
  | blue

@[ext]
structure Pair where
  x : BitVec 8
  y : BitVec 8

def isRed (c : Color) : Bool :=
  match c with
  | .red => true
  | _ => false

example (a b : Pair) (c d : Color) (h1 : a = b) (h2 : c = d) : a.x = b.x ∧ d = c := by
  bv_decide

example (a b : Pair) (h : a = b) : a.x = b.x := by
  bv_decide types [Pair]

example (c d : Color) (h : c = d) : d = c := by
  bv_decide types [Color]

example (c : Color) (h : isRed c = true) : c = .red := by
  simp only [isRed] at h
  bv_decide types [Color]

example (a b : Pair) (c d : Color) (h1 : a = b) (h2 : c = d) : a.x = b.x ∧ d = c := by
  bv_decide types [Pair, Color]

example (a b : Pair) (h : a = b) : a.x = b.x := by
  bv_decide types [Pair, Pair]

/--
error: None of the hypotheses are in the supported BitVec fragment after applying preprocessing.
There are three potential reasons for this:
1. If you are using custom BitVec constructs simplify them to built-in ones.
2. If your problem is using only built-in ones it might currently be out of reach.
   Consider expressing it in terms of different operations that are better supported.
3. The original goal was reduced to False and is thus invalid.
-/
#guard_msgs in
example (c d : Color) (h : c = d) : d = c := by
  bv_decide types [Pair]

/--
error: None of the hypotheses are in the supported BitVec fragment after applying preprocessing.
There are three potential reasons for this:
1. If you are using custom BitVec constructs simplify them to built-in ones.
2. If your problem is using only built-in ones it might currently be out of reach.
   Consider expressing it in terms of different operations that are better supported.
3. The original goal was reduced to False and is thus invalid.
-/
#guard_msgs in
example (c d : Color) (h : c = d) : d = c := by
  bv_decide types []

example (a b : Pair) (h : a = b) : a.x = b.x := by
  sym =>
    bv_normalize types [Pair]

example (a b : Pair) (h : a = b) : a.x = b.x := by
  sym =>
    bv_decide types [Pair]

/--
error: `Nat` cannot be used in a `types` clause, only non-recursive structures and enum inductives are supported
-/
#guard_msgs in
example (a b : Pair) (h : a = b) : a.x = b.x := by
  bv_decide types [Nat]

inductive Tagged where
  | tag (x : BitVec 8)

/--
error: `Tagged` cannot be used in a `types` clause, only non-recursive structures and enum inductives are supported
-/
#guard_msgs in
example (a b : Pair) (h : a = b) : a.x = b.x := by
  bv_decide types [Tagged]

/-- error: Unknown constant `DoesNotExist` -/
#guard_msgs in
example (a b : Pair) (h : a = b) : a.x = b.x := by
  bv_decide types [DoesNotExist]

-- `types` is not a reserved keyword.
def types : Nat := 0
