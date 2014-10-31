import data.nat.basic
open nat

theorem zero_left (n : ℕ) : 0 + n = n :=
nat.induction_on n
    !add.zero_right
    (take m IH, show 0 + succ m = succ m, from
      calc
        0 + succ m = succ (0 + m) : add.succ_right
               ... = succ m       : IH)
