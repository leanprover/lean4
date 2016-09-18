open eq
definition subsets (P : Type) := P → Prop.

section

hypothesis A : Type.

hypothesis r : A → subsets A.

hypothesis i : subsets A → A.

hypothesis retract {P : subsets A} {a : A} : r (i P) a = P a.

definition delta (a:A) : Prop := ¬ (r a a).

local notation `δ` := delta.

theorem delta_aux : ¬ (δ (i delta))
         := assume H : δ (i delta),
            H (subst (symm (@retract delta (i delta))) H)

check delta_aux.

end
