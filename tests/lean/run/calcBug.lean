namespace Hidden

open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   (show 0 + 0 = 0 from rfl)
   (fun (n : Nat) (ih : 0 + n = n) =>
    show 0 + succ n = succ n from
    calc
       0 + succ n = succ (0 + n) := rfl
                _ = succ n       := by rw [ih])

end Hidden
