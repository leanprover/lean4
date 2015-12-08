namespace ex
set_option blast.strategy "backward"

constant typ : Type₁

constant subtype : typ → typ → Prop

constant subtype_refl : ∀ T, subtype T T

constant subtype_trans : ∀ S T U, subtype S T → subtype T U → subtype S U

attribute subtype_refl subtype_trans [intro]

lemma L1 : ∀ T1 T2 T3 T4 T5 T6, subtype T1 T2 → subtype T2 T3 → subtype T3 T4 → subtype T4 T5 → subtype T5 T6 → subtype T1 T6 :=
by blast

reveal L1
print L1

end ex
