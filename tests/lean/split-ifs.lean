/-! Test that the `split` tactic doesn't use `Classical.em` to split ifs.
-/

/- Basic example -/
theorem ittt1 (n : Nat) : (if n = 0 then 0 else 0) = 0 := by split <;> rfl

#print axioms ittt1

/- Example where the decidabilty instance has loose bound variables
  and split falls back on classical axioms (courtesy of Mario Carneiro). -/
theorem ittt2 (c : Prop) :
    (fun [Decidable c] => if c then 0 else 0) = (fun _ => 0) := by
  split <;> rfl

#print axioms ittt2
