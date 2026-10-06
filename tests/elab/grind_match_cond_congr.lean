/-!
`Grind.MatchCond` nodes are not in the congruence table, and must not enter it when the parents of
a merged class are reinserted. The entry was hashed on the root of the `MatchCond` argument, of
which the node is not a registered parent, so it went stale when the argument merged with
`False`. `grind.debug` checks every congruence table entry.
-/

set_option grind.debug true

example (x n : Nat)
    : 0 < match x with
          | 0  => 1
          | _ => x + n := by
  grind

example (x y : Nat)
    : 0 < match x, y with
          | 0, 0   => 1
          | _, _ => x + y := by
  grind

example (x : Nat) (h : (match x with | 0 => true | _ => false) = true) : x = 0 := by
  grind

example (xs : List Nat) (h : (match xs with | [] => 0 | x :: _ => x + 1) = 0) : xs = [] := by
  grind
