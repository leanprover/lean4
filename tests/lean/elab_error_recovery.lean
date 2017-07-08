def half_baked : ℕ → ℕ
| 3  := 2
-- type mismatches
| 0  := 1 + ""
-- placeholders
| 5  := _ + 4
-- missing typeclass instances
| 42 := if 2 ∈ 3 then 3 else _
-- exceptions during tactic evaluation
| 7  := by do undefined
-- nested elaboration errors
| 10 := begin exact [] end
-- missing cases

#print half_baked._main

#reduce    half_baked 3
#reduce    half_baked 5
#eval half_baked 3

-- type errors in binders
#check ∀ x : nat.zero, x = x
