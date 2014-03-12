-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import macros
import subtype

definition reflexive {A : Type} (r : A → A → Bool)   := ∀ a, r a a
definition symmetric {A : Type} (r : A → A → Bool)   := ∀ a b, r a b → r b a
definition transitive {A : Type} (r : A → A → Bool)  := ∀ a b c, r a b → r b c → r a c
definition equivalence {A : Type} (r : A → A → Bool) := reflexive r ∧ symmetric r ∧ transitive r

namespace quotient
definition member {A : Type} (a : A) (S : A → Bool) := S a
infix 50 ∈ : member

definition eqc {A : Type} (a : A) (r : A → A → Bool) := λ b, r a b

theorem eqc_mem {A : Type} {a b : A} (r : A → A → Bool) : r a b → b ∈ eqc a r
:= assume H : r a b, H

theorem eqc_r {A : Type} {a b : A} (r : A → A → Bool) : b ∈ (eqc a r) → r a b
:= assume H : b ∈ (eqc a r), H

theorem eqc_eq {A : Type} {a b : A} {r : A → A → Bool} : equivalence r → r a b → (eqc a r) = (eqc b r)
:= assume (Heqv : equivalence r) (Hrab : r a b),
   have Hsym : symmetric r,
     from and_eliml (and_elimr Heqv),
   have Htrans : transitive r,
     from and_elimr (and_elimr Heqv),
   funext (λ x : A,
     iff_intro
       (assume Hin : x ∈ (eqc a r),
          have Hb : r b x,
            from Htrans b a x (Hsym a b Hrab) (eqc_r r Hin),
          eqc_mem r Hb)
       (assume Hin : x ∈ (eqc b r),
          have Ha : r a x,
            from Htrans a b x Hrab (eqc_r r Hin),
          eqc_mem r Ha))

definition rep_i {A : Type} (a : A) (r : A → A → Bool) : A
:= ε (inhabited_intro a) (eqc a r)

theorem r_rep {A : Type} (a : A) (r : A → A → Bool) : reflexive r → r a (rep_i a r)
:= assume R : reflexive r,
   eps_ax (inhabited_intro a) a (R a)

theorem rep_eq {A : Type} {a b : A} {r : A → A → Bool} : equivalence r → r a b → rep_i a r = rep_i b r
:= assume (Heqv : equivalence r) (Hrab : r a b),
   have Heq : eqc a r = eqc b r,
     from eqc_eq Heqv Hrab,
   have Hin : inhabited_intro a = inhabited_intro b,
     from proof_irrel (inhabited_intro a) (inhabited_intro b),
   calc rep_i a r = ε (inhabited_intro a) (eqc a r)  : refl _
              ... = ε (inhabited_intro b) (eqc a r)  : { Hin }
              ... = ε (inhabited_intro b) (eqc b r)  : { Heq }
              ... = rep_i b r                        : refl _

theorem rep_rep {A : Type} (a : A) {r : A → A → Bool} : equivalence r → rep_i (rep_i a r) r = rep_i a r
:= assume Heqv : equivalence r,
   have Hrefl : reflexive r,
     from and_eliml Heqv,
   have Hsym : symmetric r,
     from and_eliml (and_elimr Heqv),
   have Hr : r (rep_i a r) a,
     from Hsym _ _ (r_rep a r Hrefl),
   rep_eq Heqv Hr

definition quotient {A : Type} {r : A → A → Bool} (e : equivalence r)
:= subtype A (λ a, rep_i a r = a)

theorem inhab {A : Type} (Hin : inhabited A) {r : A → A → Bool} (e : equivalence r) : inhabited (quotient e)
:= obtain (a : A) (Ht : true), from Hin,
   subtype::subtype_inhabited (exists_intro (rep_i a r) (rep_rep a e))

definition abst {A : Type} (a : A) {r : A → A → Bool} (e : equivalence r) : quotient e
:= subtype::abst (rep_i a r) (inhab (inhabited_intro a) e)

notation 65 [ _ ] _ : abst

definition rep {A : Type} {r : A → A → Bool} {e : equivalence r} (q : quotient e) : A
:= subtype::rep q

theorem quotient_eq {A : Type} (a b : A) {r : A → A → Bool} (e : equivalence r) : r a b → [a]e = [b]e
:= assume Hrab : r a b,
   have Heq_a : [a]e = subtype::abst (rep_i a r) (inhab (inhabited_intro a) e),
     from refl _,
   have Heq_b : [b]e = subtype::abst (rep_i b r) (inhab (inhabited_intro b) e),
     from refl _,
   have Heq_r : rep_i a r = rep_i b r,
     from rep_eq e Hrab,
   have Heq_pr : inhabited_intro a = inhabited_intro b,
     from proof_irrel _ _,
   calc  [a]e = subtype::abst (rep_i a r) (inhab (inhabited_intro a) e)  : Heq_a
          ... = subtype::abst (rep_i b r) (inhab (inhabited_intro a) e)  : { Heq_r }
          ... = subtype::abst (rep_i b r) (inhab (inhabited_intro b) e)  : { Heq_pr }
          ... = [b]e                                                     : symm Heq_b

theorem quotient_rep {A : Type} (a : A) {r : A → A → Bool} (e : equivalence r) : r a (rep ([a]e))
:= have Heq1 : [a]e = subtype::abst (rep_i a r) (inhab (inhabited_intro a) e),
     from refl ([a]e),
   have Heq2 : rep ([a]e) = @rep A r e (subtype::abst (rep_i a r) (inhab (inhabited_intro a) e)),
     from congr2 (λ x : quotient e, @rep A r e x) Heq1,
   have Heq3 : @rep A r e (subtype::abst (rep_i a r) (inhab (inhabited_intro a) e)) = (rep_i a r),
     from subtype::rep_abst (inhab (inhabited_intro a) e) (rep_i a r) (rep_rep a e),
   have Heq4 : rep ([a]e) = (rep_i a r),
     from trans Heq2 Heq3,
   have Hr : r a (rep_i a r),
     from r_rep a r (and_eliml e),
   subst Hr (symm Heq4)

set_opaque eqc true
set_opaque rep_i true
set_opaque quotient true
set_opaque abst true
set_opaque rep true
end
definition quotient {A : Type} {r : A → A → Bool} (e : equivalence r) := quotient::quotient e
