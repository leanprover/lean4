

inductive Formula
| eqf  : Nat → Nat → Formula
| impf : Formula → Formula → Formula

def Formula.denote : Formula → Prop
| eqf n1 n2  => n1 = n2
| impf f1 f2 => denote f1 → denote f2

theorem Formula.denote_eqf (n1 n2 : Nat) : denote (eqf n1 n2) = (n1 = n2) :=
rfl

theorem Formula.denote_impf (f1 f2 : Formula) : denote (impf f1 f2) = (denote f1 → denote f2) :=
rfl
