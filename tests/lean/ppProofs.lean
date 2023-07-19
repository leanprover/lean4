set_option pp.analyze.trustSubst true
set_option pp.proofs false
example (h : α = β) : h ▸ (a : α) = (b : β) := _
example (h : α = β) : id h ▸ (a : α) = (b : β) := _
example (h : α = β) : id h ▸ (a : α) = (b : β) := by simp (config := { failIfUnchanged := false })
set_option pp.proofs.withType false
example (h : α = β) : id h ▸ (a : α) = (b : β) := _
set_option pp.proofs true
example (h : α = β) : id h ▸ (a : α) = (b : β) := _
