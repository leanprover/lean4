/-!
Tests that the canonicalizer maps all spellings of the same bit-vector literal (e.g. `1#1`
and `(1 : BitVec 1)`) to a single representation before they reach the E-graph. Two
representations of the same value used to reach the E-graph as distinct interpreted nodes,
and `grind` produced an invalid inconsistency proof rejected by the kernel with
`eq_false_of_decide (eagerReduce (Eq.refl false))`. See #14521. `grind.debug` enables the
E-graph invariant check that all interpreted nodes are in canonical form.
-/

set_option grind.debug true

example (i : BitVec (id 32)) (hne : i ≠ 0#32) : i ≠ 0 := by
  grind

/-!
Example reported on Zulip: `1#1` occurs inside the `match`-conditions of the negated goal
and is not normalized to the `OfNat.ofNat` representation used by the `BitVec` literal
propagators.
-/

inductive MyInt (w : Nat) where
  | poison
  | val (v : BitVec w)

namespace MyInt

def isPoison {w : Nat} : MyInt w → Bool
  | .poison => true
  | .val _ => false

def getValue {w : Nat} (x : MyInt w) (h : x.isPoison = false := by grind) : BitVec w :=
  match x, h with
  | .val v, _ => v

def select {w : Nat} (c : MyInt 1) (x y : MyInt w) : MyInt w :=
  match c with
  | .val c' => if c' == 1#1 then x else y
  | .poison => .poison

@[grind =]
theorem isPoison_select {w : Nat} (x y : MyInt w) (c : MyInt 1) :
    (select c x y).isPoison =
      if h : c.isPoison = true then true
      else if c.getValue = 1#1 then x.isPoison else y.isPoison := by
  cases c with
  | poison => simp [select, isPoison]
  | val c' => by_cases hc : c' = 1#1 <;> simp [select, isPoison, hc, getValue]

theorem getValue_select {w : Nat} (x y : MyInt w) (c : MyInt 1) (h : (select c x y).isPoison = false) :
    (select c x y).getValue h = if _ : c.getValue = 1#1 then x.getValue else y.getValue := by
  simp [select, getValue]
  grind

end MyInt
