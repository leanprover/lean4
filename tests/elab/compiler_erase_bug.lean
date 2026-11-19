def f (h : α = { n : Nat // True }) (a : α) : Nat :=
  (cast h a).casesOn (motive := fun _ => Nat) fun val prop => val

#guard f rfl ⟨42, ⟨⟩⟩ == 42
