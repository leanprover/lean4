open expr tactic

example : false := by do
n ← mk_fresh_name,
apply (local_const n n binder_info.default (const ``false []))
