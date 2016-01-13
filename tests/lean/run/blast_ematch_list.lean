import data.list
open list


lemma last_singleton [simp] {A : Type} (a : A) : last [a] !cons_ne_nil = a :=
rfl

lemma last_cons_cons [simp] {A : Type} (a₁ a₂ : A) (l : list A)  : last (a₁::a₂::l) !cons_ne_nil = last (a₂::l) !cons_ne_nil :=
rfl

theorem last_concat [simp] {A : Type} {x : A} : ∀ {l : list A}, last (concat x l) !concat_ne_nil = x :=
by rec_inst_simp
