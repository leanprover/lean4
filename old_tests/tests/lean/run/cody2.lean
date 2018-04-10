definition subsets (P : Type) := P → Prop.

section

parameter A : Type.

parameter r : A → subsets A.

parameter i : subsets A → A.

parameter retract {P : subsets A} {a : A} : r (i P) a = P a.

definition delta (a:A) : Prop := ¬ (r a a).

local notation `δ` := delta.

theorem delta_aux : ¬ (δ (i delta))
         := assume H : δ (i delta),
            H (eq.subst (symm (@retract delta (i delta))) H)

#check delta_aux.

end
