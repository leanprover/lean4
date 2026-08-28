

inductive Formula
| eqf  : Nat → Nat → Formula
| andf : Formula → Formula → Formula
| impf : Formula → Formula → Formula
| notf : Formula → Formula
| orf  : Formula → Formula → Formula
| allf : (Nat → Formula) → Formula

namespace Formula
def implies (a b : Prop) : Prop := a → b

def denote : Formula → Prop
| eqf n1 n2  => n1 = n2
| andf f1 f2 => denote f1 ∧ denote f2
| impf f1 f2 => implies (denote f1) (denote f2)
| orf f1 f2  => denote f1 ∨ denote f2
| notf f     => ¬ denote f
| allf f     => (n : Nat) → denote (f n)

theorem denote_eqf (n1 n2 : Nat) : denote (eqf n1 n2) = (n1 = n2) :=
rfl

theorem denote_andf (f1 f2 : Formula) : denote (andf f1 f2) = (denote f1 ∧ denote f2) :=
rfl

theorem denote_impf (f1 f2 : Formula) : denote (impf f1 f2) = (denote f1 → denote f2) :=
rfl

theorem denote_orf (f1 f2 : Formula) : denote (orf f1 f2) = (denote f1 ∨ denote f2) :=
rfl

theorem denote_notf (f : Formula) : denote (notf f) = ¬ denote f :=
rfl

theorem denote_allf (f : Nat → Formula) : denote (allf f) = (∀ n, denote (f n)) :=
rfl

theorem ex : denote (allf (fun n₁ => allf (fun n₂ => impf (eqf n₁ n₂) (eqf n₂ n₁)))) = (∀ (n₁ n₂ : Nat), n₁ = n₂ → n₂ = n₁) :=
rfl

end Formula
