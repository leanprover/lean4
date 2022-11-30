

inductive Formula
| eqf  : Nat → Nat → Formula
| andf : Formula → Formula → Formula
| impf : Formula → Formula → Formula
| notf : Formula → Formula
| orf  : Formula → Formula → Formula
| allf : (Nat → Formula) → Formula

namespace Formula
def Implies (a b : Prop) : Prop := a → b

def Denote : Formula → Prop
| eqf n1 n2  => n1 = n2
| andf f1 f2 => Denote f1 ∧ Denote f2
| impf f1 f2 => Implies (Denote f1) (Denote f2)
| orf f1 f2  => Denote f1 ∨ Denote f2
| notf f     => ¬ Denote f
| allf f     => (n : Nat) → Denote (f n)

theorem denote_eqf (n1 n2 : Nat) : Denote (eqf n1 n2) = (n1 = n2) :=
rfl

theorem denote_andf (f1 f2 : Formula) : Denote (andf f1 f2) = (Denote f1 ∧ Denote f2) :=
rfl

theorem denote_impf (f1 f2 : Formula) : Denote (impf f1 f2) = (Denote f1 → Denote f2) :=
rfl

theorem denote_orf (f1 f2 : Formula) : Denote (orf f1 f2) = (Denote f1 ∨ Denote f2) :=
rfl

theorem denote_notf (f : Formula) : Denote (notf f) = ¬ Denote f :=
rfl

theorem denote_allf (f : Nat → Formula) : Denote (allf f) = (∀ n, Denote (f n)) :=
rfl

theorem ex : Denote (allf (fun n₁ => allf (fun n₂ => impf (eqf n₁ n₂) (eqf n₂ n₁)))) = (∀ (n₁ n₂ : Nat), n₁ = n₂ → n₂ = n₁) :=
rfl

end Formula
