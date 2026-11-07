/-!
Regression test for #15778: `grind?` produced a script whose `cases` step picked the wrong
case-split. The candidates `if w✝ ∈ p :: s then w✝ else 0` differ only in hidden variables
introduced by function extensionality, and used to share the same anchor. As a consequence,
the script could not be replayed, and `grind?` dropped `List.mem_cons` from its suggestion.
-/

-- `grind?` must not warn that its generated tactic cannot close the goal.
#guard_msgs (warning, drop info) in
example (p : Nat) (s : List Nat) (P : (Nat → Nat) → Prop)
    (ha : P (fun _ => 0))
    (hb : P (fun x => if x ∈ s then x else 0))
    (h : P (fun x => if x = p then x else if x ∈ s then x else 0)) :
    P (fun x => if x ∈ p :: s then x else 0) := by
  grind? only [List.mem_cons]
