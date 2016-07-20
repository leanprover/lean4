open tactic

axiom Sorry : ∀ A : Type, A

inductive Enum : Type := ea | eb | ec | ed
noncomputable definition Enum_dec_eq [instance] : decidable_eq Enum :=
by do a ← intro "a", cases a,
      b ← intro "b", cases b,
      right >> reflexivity,
      try (left >> intro  "H" >>= cases),
      repeat $ intros >> mk_const "Sorry" >>= apply
