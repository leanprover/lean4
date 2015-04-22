import logic

definition subsets (P : Type) := P → Prop.

section

hypothesis A : Type.

hypothesis r : A → subsets A.

hypothesis i : subsets A → A.

hypothesis retract {P : subsets A} {a : A} : r (i P) a = P a.

definition delta (a:A) : Prop := ¬ (r a a).

local notation `δ` := delta.

-- Crashes unifier!
theorem false_aux : ¬ (δ (i delta))
         := assume H : δ (i delta),
            have H' : r (i delta) (i delta),
              from eq.rec H (eq.symm retract),
            H H'.
end
