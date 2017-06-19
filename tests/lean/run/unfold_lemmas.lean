open nat well_founded

def gcd : ℕ → ℕ → ℕ | y := λ x,
if h : y = 0 then
    x
else
    have x % y < y, by { apply mod_lt, cases y, contradiction, apply succ_pos },
    gcd (x % y) y

@[simp] lemma gcd_zero_right (x : nat) : gcd 0 x = x := rfl
