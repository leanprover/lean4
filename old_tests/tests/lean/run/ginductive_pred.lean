inductive term : Type
| var : nat → term
| app : string → list term → term

/- In the current system, it will be hard to work with mutually inductive predicates.
   Reason: we cannot use well-founded recursion, and the induction principle for it
   is too weak. -/
mutual inductive var_occ, var_occ_list
with var_occ : nat → term → Prop
| leaf (n : nat) : var_occ n (term.var n)
| app  (n : nat) (s : string) (ts : list term) : var_occ_list n ts → var_occ n (term.app s ts)
with var_occ_list : nat → list term → Prop
| head (n : nat) (t : term) (ts : list term) : var_occ n t → var_occ_list n (t::ts)
| tail (n : nat) (t : term) (ts : list term) : var_occ_list n ts → var_occ_list n (t::ts)
