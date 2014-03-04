import macros tactic

namespace sum
definition sum (A B : Type) := sig b : Bool, if b then A else B

theorem sum_if_l (A B : Type) : A == if true then A else B
:= by simp

theorem sum_if_r (A B : Type) : B == if false then A else B
:= by simp

definition inl {A : Type} (a : A) (B : Type) : sum A B
:= pair true (cast (sum_if_l A B) a)

definition inr (A : Type) {B : Type} (b : B) : sum A B
:= pair false (cast (sum_if_r A B) b)

theorem cast_eq_cast {A B1 B2 : Type} {H1 : A == B1} {H2 : A == B2} {a1 a2 : A} (H : cast H1 a1 == cast H2 a2) : a1 = a2
:= have S1 : cast H1 a1 == a1,
     from cast_heq H1 a1,
   have S2 : cast H2 a2 == a2,
     from cast_heq H2 a2,
   to_eq (htrans (htrans (hsymm S1) H) S2)

theorem inl_inj {A B : Type} {a1 a2 : A} : inl a1 B = inl a2 B → a1 = a2
:= assume H : inl a1 B = inl a2 B,
   have H1 : (cast _ a1) == (cast _ a2),
     from hproj2_congr H,
   cast_eq_cast H1

theorem inr_inj {A B : Type} {b1 b2 : B} : inr A b1 = inr A b2 → b1 = b2
:= assume H : inr A b1 = inr A b2,
   have H1 : (cast _ b1) == (cast _ b2),
     from hproj2_congr H,
   cast_eq_cast H1

theorem distinct {A B : Type} (a : A) (b : B) : inl a B ≠ inr A b
:= not_intro (assume N : inl a B = inr A b,
   absurd (proj1_congr N) true_ne_false)

theorem dichotomy {A B : Type} (n : sum A B) : (∃ a, n = inl a B) ∨ (∃ b, n = inr A b)
:= or_elim (em (proj1 n))
     (assume H : proj1 n,
       have H1n : proj1 n = true,
         from eqt_intro H,
       have Haux : (if (proj1 n) then A else B) = A,
         from calc (if (proj1 n) then A else B) = if true then A else B : { H1n }
                                            ... = A                     : if_true _ _,
       let a : A := cast (to_heq Haux) (proj2 n) in
       have H1i : proj1 (inl a B) = true,
         from refl _,
       have H2n : proj2 n == a,
         from hsymm (cast_heq (to_heq Haux) (proj2 n)),
       have H2i : proj2 (inl a B) == a,
         from cast_heq (sum_if_l A B) a,
       have Heq : n = (inl a B),
         from pairext n (inl a B) (trans H1n (symm H1i)) (htrans H2n (hsymm H2i)),
       or_introl (exists_intro a Heq) (∃ b, n = inr A b))
     (assume H : ¬ proj1 n,
       have H1n : proj1 n = false,
         from eqf_intro H,
       have Haux : (if (proj1 n) then A else B) = B,
         from calc (if (proj1 n) then A else B) = if false then A else B : { H1n }
                                            ... = B                      : if_false _ _,
       let b : B := cast (to_heq Haux) (proj2 n) in
       have H1i : proj1 (inr A b) = false,
         from refl _,
       have H2n : proj2 n == b,
         from hsymm (cast_heq (to_heq Haux) (proj2 n)),
       have H2i : proj2 (inr A b) == b,
         from cast_heq (sum_if_r A B) b,
       have Heq : n = (inr A b),
         from pairext n (inr A b) (trans H1n (symm H1i)) (htrans H2n (hsymm H2i)),
       or_intror (∃ a, n = inl a B) (exists_intro b Heq))

theorem induction {A B : Type} {P : sum A B → Bool} (H1 : ∀ a, P (inl a B)) (H2 : ∀ b, P (inr A b)) : ∀ n, P n
:= take n, or_elim (dichotomy n)
    (assume Hex : ∃ a, n = inl a B,
     obtain (a : A) (Ha : n = inl a B), from Hex,
     show P n,
        from subst (H1 a) (symm Ha))
    (assume Hex : ∃ b, n = inr A b,
     obtain (b : B) (Hb : n = inr A b), from Hex,
     show P n,
        from subst (H2 b) (symm Hb))

set_opaque inl true
set_opaque inr true
set_opaque sum true
end
definition sum := sum::sum