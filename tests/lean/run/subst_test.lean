import data.nat
open nat

structure less_than (n : nat) := (val : nat) (lt : val < n)

namespace less_than
open decidable

set_option pp.beta false

definition less_than.has_decidable_eq [instance] (n : nat) : ∀ (i j : less_than n), decidable (i = j)
| (mk ival ilt) (mk jval jlt) :=
  match nat.has_decidable_eq ival jval with
  | inl veq := inl (by subst veq)
  | inr vne := inr (by intro h; injection h; contradiction)
  end

end less_than
