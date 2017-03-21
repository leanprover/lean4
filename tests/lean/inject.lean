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
| (succ n) f0     := 0
| (succ n) (fs i) := succ (to_nat i)

#check @to_nat.equations._eqn_1
#check @to_nat.equations._eqn_2

def to_nat' : ∀ {n}, fi n → nat
| ._ (@f0 n)   := 0
| ._ (@fs n i) := succ (to_nat' i)

def fi' {n} (i : fi n) : Type :=
fi (to_nat i)

/- We need the unification hint to be able to get sane equations when using fi' -/
@[unify] def to_nat_hint (n m k : nat) (i : fi (succ n)) (j : fi n) : unification_hint :=
{ pattern     := @to_nat (succ n) (@fs n j) ≟ succ m,
  constraints := [m ≟ to_nat j] }

def inject : ∀ {n} {i : fi n}, fi' i → fi n
| (succ n) (fs i) f0     := f0
| (succ n) (fs i) (fs j) := fs (inject j)

def inject' : ∀ {n} {i : fi n}, fi' i → fi n
| ._ (@fs n i) f0     := f0
| ._ (@fs n i) (fs j) := fs (inject' j)

#check @inject.equations._eqn_1
#check @inject.equations._eqn_2

#check @inject'.equations._eqn_1
#check @inject'.equations._eqn_2

def raise {m} : Π n, fi m → fi (m + n)
| 0        i := i
| (succ n) i := fs (raise n i)

#check @raise.equations._eqn_1
#check @raise.equations._eqn_2

def deg : Π {n}, fi (n + 1) → fi n → fi (n + 1)
| (succ n) f0     j      := fs j
| (succ n) (fs i) f0     := f0
| (succ n) (fs i) (fs j) := fs (deg i j)

def deg' : Π {n}, fi (n + 1) → fi n → fi (n + 1)
| ._ (@f0 (succ n))   j      := fs j
| ._ (@fs (succ n) i) f0     := f0
| ._ (@fs (succ n) i) (fs j) := fs (deg' i j)

#check @deg.equations._eqn_1
#check @deg.equations._eqn_2
#check @deg.equations._eqn_3

#check @deg'.equations._eqn_1
#check @deg'.equations._eqn_2
#check @deg'.equations._eqn_3

end fi
