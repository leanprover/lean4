def f (h : α = { n : Nat // True }) (a : α) : Nat :=
  (cast h a).casesOn (motive := fun _ => Nat) fun val prop => val

#eval f rfl ⟨42, ⟨⟩⟩
