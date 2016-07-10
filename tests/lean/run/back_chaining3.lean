namespace ex
open tactic

constant typ : Type₁

constant subtype : typ → typ → Prop

constant subtype_refl : ∀ T, subtype T T

constant subtype_trans : ∀ S T U, subtype S T → subtype T U → subtype S U

attribute subtype_refl subtype_trans [intro]

lemma L1 : ∀ T1 T2 T3 T4, subtype T1 T2 → subtype T2 T3 → subtype T3 T4 → subtype T1 T4 :=
by intros >> back_chaining_using_hs

set_option back_chaining.max_depth 10

lemma L2 : ∀ T1 T2 T3 T4 T5 T6 (H1 :subtype T1 T2) (H2 : subtype T2 T3) (H3 : subtype T3 T4) (H3 : subtype T4 T5) (H4 : subtype T5 T6), subtype T1 T6 :=
by intros >> back_chaining_using_hs

end ex
