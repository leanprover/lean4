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
| _  := begin exact [] end

print half_baked._main

eval    half_baked 3
eval    half_baked 5
vm_eval half_baked 3

-- type errors in binders
check ∀ x : nat.zero, x = x
