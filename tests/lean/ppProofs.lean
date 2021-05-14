example (h : α = β) : h ▸ (a : α) = (b : β) := _
example (h : α = β) : id h ▸ (a : α) = (b : β) := _
set_option pp.proofs.withType false
example (h : α = β) : id h ▸ (a : α) = (b : β) := _
set_option pp.proofs true
example (h : α = β) : id h ▸ (a : α) = (b : β) := _
