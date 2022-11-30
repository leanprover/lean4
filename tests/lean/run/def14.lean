

inductive Formula
| eqf  : Nat → Nat → Formula
| impf : Formula → Formula → Formula

def Formula.Denote : Formula → Prop
| eqf n1 n2  => n1 = n2
| impf f1 f2 => Denote f1 → Denote f2

theorem Formula.denote_eqf (n1 n2 : Nat) : Denote (eqf n1 n2) = (n1 = n2) :=
rfl

theorem Formula.denote_impf (f1 f2 : Formula) : Denote (impf f1 f2) = (Denote f1 → Denote f2) :=
rfl
