example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1

/-!
Within a tactic macro, all identifiers *not* from this quotation should be regarded as inaccessible.
-/

macro "my_tac " h:ident : tactic =>
 `(tactic| (
   cases $h:ident
   rename_i h_p3
   rename_i h_p1_p2 -- must rename `left`, not `h_p3`
   cases h_p1_p2  -- fails otherwise
   ))

example (h : (p1 ∧ p2) ∧ p3) : True := by
  my_tac h
  sorry
