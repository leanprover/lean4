mutual
def a : Nat := b
partial_fixpoint
def b : Nat := a
partial_fixpoint
end


/--
info: a.mutual_fixpoint_induct (motive_1 motive_2 : Nat → Prop) (adm_1 : Lean.Order.admissible motive_1)
  (adm_2 : Lean.Order.admissible motive_2) (h_1 : ∀ (b : Nat), motive_2 b → motive_1 b)
  (h_2 : ∀ (a : Nat), motive_1 a → motive_2 a) : motive_1 a ∧ motive_2 b
-/
#guard_msgs(pass trace, all) in
#check a.mutual_fixpoint_induct


mutual
def c (n : Nat) : Nat := d (n + 1)
partial_fixpoint
def d (n : Nat) : Nat := c (n + 2)
partial_fixpoint
end

/--
info: c.mutual_fixpoint_induct (motive_1 motive_2 : (Nat → Nat) → Prop) (adm_1 : Lean.Order.admissible motive_1)
  (adm_2 : Lean.Order.admissible motive_2) (h_1 : ∀ (d : Nat → Nat), motive_2 d → motive_1 fun n => d (n + 1))
  (h_2 : ∀ (c : Nat → Nat), motive_1 c → motive_2 fun n => c (n + 2)) : motive_1 c ∧ motive_2 d
-/
#guard_msgs(pass trace, all) in
#check c.mutual_fixpoint_induct
