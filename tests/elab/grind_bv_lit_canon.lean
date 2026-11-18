/-!
Ground subterms of e-matching patterns are internalized after `preprocessLight`
only, which does not put bit-vector literals in `grind` normal form. A `1#2`
reaching the e-graph as `BitVec.ofNat` rather than `OfNat.ofNat` gave two
interpreted nodes for one value, and merging them looked like a
`valueInconsistency` to `addEqStep`.
-/

example (f g : Nat → BitVec 2) (h : ∀ n, f n = g n ||| 1#2) : f 0 = g 0 ||| 1#2 := by grind

example (f g : Nat → BitVec 2) (h : ∀ n, f n = g n &&& 1#2) : f 0 = g 0 &&& 1#2 := by grind

example (f g : Nat → BitVec 2) (h : ∀ n, f n = g n ||| 0#2) : f 0 = g 0 ||| 0#2 := by grind

example (f g : Nat → BitVec 4) (h : ∀ n, f n = g n ||| 1#4) : f 0 = g 0 ||| 1#4 := by grind

-- mixed spellings across hypothesis and goal
example (f g : Nat → BitVec 2) (h : ∀ n, f n = g n ||| 1#2) :
    f 0 = g 0 ||| (1 : BitVec 2) := by grind

example (f g : Nat → BitVec 2) (h : ∀ n, f n = g n ||| (1 : BitVec 2)) :
    f 0 = g 0 ||| 1#2 := by grind
