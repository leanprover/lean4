/-
This test case explores the interaction between the `split` tactic and the
tailrecursion checking:

If `split` would rewrite matches with identical targets together, and thus clear out
dead code, this would be accepted, despite a non-tailrecursive call there.
-/

/--
error: Could not prove 'whileSome' to be monotone in its recursive calls:
  Cannot eliminate recursive call `whileSome some x'` enclosed in
    id (whileSome some x'✝)
-/
#guard_msgs in
def whileSome (f : α → Option α) (x : α) : α :=
  match f x with
  | none => x
  | some x' =>
    match f x with
    | none => id $ whileSome some x'
    | some x' => whileSome f x'
partial_fixpoint
