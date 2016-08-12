/-
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
-/
prelude
import init.logic

namespace simplifier

namespace empty
end empty

namespace prove
attribute eq_self_iff_true [simp]
end prove

namespace unit_simp

-- TODO(dhs): prove these lemmas elsewhere and only gather the
-- [simp] attributes here

variables {A B C : Prop}

attribute [simp]
lemma and_imp : (A ∧ B → C) ↔ (A → B → C) :=
iff.intro (assume H a b, H (and.intro a b))
          (assume H ab, H (and.left ab) (and.right ab))

attribute [simp]
lemma or_imp : (A ∨ B → C) ↔ ((A → C) ∧ (B → C)) :=
iff.intro (assume H, and.intro (assume a, H (or.inl a))
                               (assume b, H (or.inr b)))
          (assume H ab, and.rec_on H
            (assume Hac Hbc, or.rec_on ab Hac Hbc))

attribute [simp]
lemma imp_and : (A → B ∧ C) ↔ ((A → B) ∧ (A → C)) :=
iff.intro (assume H, and.intro (assume a, and.left (H a))
                               (assume a, and.right (H a)))
          (assume H a, and.rec_on H
            (assume Hab Hac, and.intro (Hab a) (Hac a)))

-- TODO(dhs, leo): do we want to pre-process away the [iff]s?
/-
attribute [simp]
lemma iff_and_imp : ((A ↔ B) → C) ↔ (((A → B) ∧ (B → A)) → C) :=
iff.intro (assume H1 H2, and.rec_on H2 (assume ab ba, H1 (iff.intro ab ba)))
          (assume H1 H2, H1 (and.intro (iff.elim_left H2) (iff.elim_right H2)))
-/

attribute [simp]
lemma a_of_a : (A → A) ↔ true :=
iff.intro (assume H, trivial)
          (assume t a, a)

attribute [simp]
lemma not_true_of_false : ¬ true ↔ false :=
iff.intro (assume H, H trivial)
          (assume f, false.rec (¬ true) f)

attribute [simp]
lemma imp_true : (A → true) ↔ true :=
iff.intro (assume H, trivial)
          (assume t a, trivial)

attribute [simp]
lemma true_imp : (true → A) ↔ A :=
iff.intro (assume H, H trivial)
          (assume a t, a)

-- lemma fold_not [simp] : (A → false) ↔ ¬ A :=
-- iff.intro id id

attribute [simp]
lemma false_imp : (false → A) ↔ true :=
iff.intro (assume H, trivial)
          (assume t f, false.rec A f)


attribute [simp]
lemma ite_and [A_dec : decidable A] : ite A B C ↔ ((A → B) ∧ (¬ A → C)) :=
iff.intro (assume H, and.intro (assume a, implies_of_if_pos H a)
                               (assume a, implies_of_if_neg H a))
          (assume H, and.rec_on H
            (assume Hab Hnac, decidable.rec_on A_dec
              (assume na,
                have rw : @decidable.ff A na = A_dec, from
                  subsingleton.rec_on (subsingleton_decidable A)
                    (assume H, H (@decidable.ff A na) A_dec),
                have Hc : C, from Hnac na,
                have ite A B C = C, from if_neg na,
                have @ite A (@decidable.ff A na) Prop B C = C, from eq.subst (eq.symm rw) this,
                eq.mpr this Hc)
              (assume a,
                have rw : @decidable.tt A a = A_dec, from
                  subsingleton.rec_on (subsingleton_decidable A)
                    (assume H, H (@decidable.tt A a) A_dec),
                have Hb : B, from Hab a,
                have ite A B C = B, from if_pos a,
                have @ite A (@decidable.tt A a) Prop B C = B, from eq.subst (eq.symm rw) this,
                eq.mpr this Hb)))

end unit_simp
end simplifier
