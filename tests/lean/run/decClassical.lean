open Classical

theorem ex : if (fun x => x + 1) = (fun x => x + 2) then False else True := by
  have : (fun x => x + 1) ≠ (fun x => x + 2) := by
    intro h
    have : 1 = 2 := congrFun h 0
    contradiction
  rw [if_neg this]
  exact True.intro

def tst (x : Nat) : Bool :=
  if 1 < 2 then true else false
