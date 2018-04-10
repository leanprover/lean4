
inductive formula
| eqf  : nat → nat → formula
| impf : formula → formula → formula

namespace formula
  definition denote : formula → Prop
  | (eqf n1 n2)  := n1 = n2
  | (impf f1 f2) := denote f1 → denote f2

  theorem denote_eqf (n1 n2 : nat) : denote (eqf n1 n2) = (n1 = n2) :=
  rfl

  theorem denote_impf (f1 f2 : formula) : denote (impf f1 f2) = (denote f1 → denote f2) :=
  rfl
end formula
