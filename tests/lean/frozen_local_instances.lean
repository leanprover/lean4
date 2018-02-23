example (α : Type) [has_add α] [has_mul α] [decidable_eq α] : true :=
begin
  (tactic.frozen_local_instances >>= tactic.trace),
  tactic.unfreeze_local_instances,
  (tactic.frozen_local_instances >>= tactic.trace),
  trivial
end
