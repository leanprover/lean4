/-!
Regression test for #15562: `grind` diverged on the first goal below. The `grind =` lemma
`List.min_findIdx_findIdx` rewrote `min (l.findIdx p) (l.findIdx p)` to
`l.findIdx (fun a => p a || p a)`. Because `min x x = x`, that term lands in the class of
`l.findIdx p`, so the lemma matched again and produced ever longer predicates until the heartbeat
limit. The other two goals check that `grind` still uses the lemma.
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
