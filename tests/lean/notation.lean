import logic data.num
open num
constant b : num
check b + b + b
check true ∧ false ∧ true
check (true ∧ false) ∧ true
check (2:num) + (2 + 2)
check (2 + 2) + (2:num)
check (1:num) = (2 + 3)*2
check (2:num) + 3 * 2 = 3 * 2 + 2
check (true ∨ false) = (true ∨ false) ∧ true
check true ∧ (false ∨ true)
constant A : Type₁
constant a : A
notation 1 := a
check a
open nat
check ℕ → ℕ
