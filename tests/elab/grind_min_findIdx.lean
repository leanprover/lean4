/-!
`grind` instantiates `List.min_findIdx_findIdx` only for distinct predicates and only on terms of low
generation, so it terminates on goals that take the `min` of `List.findIdx` terms.
-/

set_option maxHeartbeats 20000 in
example (l : List Nat) (p : Nat → Bool) : min (l.findIdx p) (l.findIdx p) = l.findIdx p := by
  grind

set_option maxHeartbeats 20000 in
example (l : List Nat) (p q : Nat → Bool) (h : l.findIdx (fun a => p a || q a) = 3) :
    min (l.findIdx p) (l.findIdx q) = 3 := by
  grind

set_option maxHeartbeats 20000 in
example (l : List Nat) (p q : Nat → Bool) (h : l.findIdx p ≤ l.findIdx q) :
    min (l.findIdx p) (l.findIdx q) = l.findIdx p := by
  grind
