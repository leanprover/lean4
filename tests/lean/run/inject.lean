open nat

inductive fi : nat → Type
| f0 : ∀ {n}, fi (succ n)
| fs : ∀ {n} (j : fi n), fi (succ n)

namespace fi

def lift {m k : nat} (f : fi m → fi k) : ∀ {n} (i : fi (m + n)), fi (k + n)
| 0        v      := f v
| (succ n) f0     := f0
| (succ n) (fs i) := fs (lift i)

set_option pp.implicit true

#check @lift.equations._eqn_1
#check @lift.equations._eqn_2
#check @lift.equations._eqn_3

def to_nat : ∀ {n}, fi n → nat
| ._ (@f0 n)   := 0
| ._ (@fs n i) := succ (to_nat i)

def fi' {n} (i : fi n) : Type :=
fi (to_nat i)

set_option trace.eqn_compiler true
set_option trace.type_context.is_def_eq true

def inject : ∀ {n} {i : fi n}, fi' i → fi n
| ._ (@fs n i) f0     := f0
| ._ (@fs n i) (fs j) := fs (inject j)

#exit

/- fi (to_nat (fs n i))  =?= fi (succ n) -/

#check @inject.equations._eqn_1
#check @inject.equations._eqn_2

@[unify] def to_nat_hint (n m k : nat) (i : fi (succ n)) (j : fi n) : unification_hint :=
{ pattern     := @to_nat (succ n) (@fs n j) ≟ succ m,
  constraints := [m ≟ to_nat j] }

def inject' : ∀ {n} {i : fi n}, fi' i → fi n
| ._ (@fs n i) f0     := f0
| ._ (@fs n i) (fs j) := fs (inject' j)



end fi
