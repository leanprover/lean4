open tactic

run_cmd do `(%%a → %%b) ← pure ↑`(nat → nat) | failed, skip
run_cmd do `(%%a → %%b) ← pure ↑`(Π (b : nat), nat) | failed, skip
run_cmd do `(λ a : %%a, (%%b : %%c)) ← pure ↑`(λ n, n + 1) | failed, skip
run_cmd do `(let a := (%%a : %%c) in (%%b : %%d)) ← pure ↑`(let n := 1 in n) | failed, skip
