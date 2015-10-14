import data.nat.basic
open nat algebra

theorem zero_left (n : ℕ) : 0 + n = n :=
nat.induction_on n
    !add_zero
    (take m IH,
     begin
      refine
        (calc
           0 + succ m = succ (0 + m) : _
                  ... = succ m       : IH),
      esimp
     end)
