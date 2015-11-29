/-
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
-/
prelude
import init.logic

namespace simplifier

namespace unit_simp
open eq.ops

-- TODO(dhs): prove these lemmas elsewhere and only gather the
-- [simp] attributes here

variables {A B C : Prop}

lemma and_imp [simp] : (A ∧ B → C) ↔ (A → B → C) :=
iff.intro (assume H a b, H (and.intro a b))
          (assume H ab, H (and.left ab) (and.right ab))

lemma or_imp [simp] : (A ∨ B → C) ↔ ((A → C) ∧ (B → C)) :=
iff.intro (assume H, and.intro (assume a, H (or.inl a))
                               (assume b, H (or.inr b)))
          (assume H ab, and.rec_on H
            (assume Hac Hbc, or.rec_on ab Hac Hbc))

lemma imp_and [simp] : (A → B ∧ C) ↔ ((A → B) ∧ (A → C)) :=
iff.intro (assume H, and.intro (assume a, and.left (H a))
                               (assume a, and.right (H a)))
          (assume H a, and.rec_on H
            (assume Hab Hac, and.intro (Hab a) (Hac a)))

-- TODO(dhs, leo): do we want to pre-process away the [iff]s?
/-
lemma iff_and_imp [simp] : ((A ↔ B) → C) ↔ (((A → B) ∧ (B → A)) → C) :=
iff.intro (assume H1 H2, and.rec_on H2 (assume ab ba, H1 (iff.intro ab ba)))
          (assume H1 H2, H1 (and.intro (iff.elim_left H2) (iff.elim_right H2)))
-/

lemma a_of_a [simp] : (A → A) ↔ true :=
iff.intro (assume H, trivial)
          (assume t a, a)

lemma not_true_of_false [simp] : ¬ true ↔ false :=
iff.intro (assume H, H trivial)
          (assume f, false.rec (¬ true) f)

lemma imp_true [simp] : (A → true) ↔ true :=
iff.intro (assume H, trivial)
          (assume t a, trivial)

lemma true_imp [simp] : (true → A) ↔ A :=
iff.intro (assume H, H trivial)
          (assume a t, a)

lemma fold_not [simp] : (A → false) ↔ ¬ A :=
iff.intro id id

lemma false_imp [simp] : (false → A) ↔ true :=
iff.intro (assume H, trivial)
          (assume t f, false.rec A f)

lemma ite_and [simp] [A_dec : decidable A] : ite A B C ↔ ((A → B) ∧ (¬ A → C)) :=
iff.intro (assume H, and.intro (assume a, implies_of_if_pos H a)
                               (assume a, implies_of_if_neg H a))
          (assume H, and.rec_on H
            (assume Hab Hnac, decidable.rec_on A_dec
              (assume a,
                assert rw : @decidable.inl A a = A_dec, from
                  subsingleton.rec_on (subsingleton_decidable A)
                    (assume H, H (@decidable.inl A a) A_dec),
                by rewrite [rw, if_pos a] ; exact Hab a)
              (assume na,
                assert rw : @decidable.inr A na = A_dec, from
                  subsingleton.rec_on (subsingleton_decidable A)
                    (assume H, H (@decidable.inr A na) A_dec),
                by rewrite [rw, if_neg na] ; exact Hnac na)))

end unit_simp



end simplifier
