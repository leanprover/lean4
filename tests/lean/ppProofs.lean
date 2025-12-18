/-!
# Tests for the `pp.proofs` option
-/

section
set_option pp.analyze.trustSubst true
set_option pp.proofs false
example (h : α = β) : h ▸ (a : α) = (b : β) := _
example (h : α = β) : id h ▸ (a : α) = (b : β) := _
example (h : α = β) : id h ▸ (a : α) = (b : β) := by simp (config := { failIfUnchanged := false })
set_option pp.proofs.withType false
example (h : α = β) : id h ▸ (a : α) = (b : β) := _
set_option pp.proofs true
example (h : α = β) : id h ▸ (a : α) = (b : β) := _
end

/-!
Testing threshold option
-/
section
#check let _ := Nat.le_succ 1; 0
set_option pp.proofs.threshold 10
#check let _ := Nat.le_succ 1; 0
end
