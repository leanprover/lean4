-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import macros
import subtype
import tactic
using subtype

namespace num
theorem inhabited_ind : inhabited ind
-- We use as the witness for non-emptiness, the value w in ind that is not convered by f.
:= obtain f His, from infinity,
   obtain w Hw, from and_elimr His,
      inhabited_intro w

definition S := ε (inhabited_ex_intro infinity) (λ f, injective f ∧ non_surjective f)
definition Z := ε inhabited_ind (λ y, ∀ x, ¬ S x = y)

theorem injective_S      : injective S
:= and_eliml (exists_to_eps infinity)

theorem non_surjective_S : non_surjective S
:= and_elimr (exists_to_eps infinity)

theorem S_ne_Z (i : ind) : S i ≠ Z
:= obtain w Hw, from non_surjective_S,
     eps_ax inhabited_ind w Hw i

definition N (i : ind) : Bool
:= ∀ P, P Z → (∀ x, P x → P (S x)) → P i

theorem N_Z : N Z
:= λ P Hz Hi, Hz

theorem N_S {i : ind} (H : N i) : N (S i)
:= λ P Hz Hi, Hi i (H P Hz Hi)

theorem N_smallest : ∀ P : ind → Bool, P Z → (∀ x, P x → P (S x)) → (∀ i, N i → P i)
:= λ P Hz Hi i Hni, Hni P Hz Hi

definition num := subtype ind N

theorem inhab : inhabited num
:= subtype_inhabited (exists_intro Z N_Z)

definition zero : num
:= abst Z inhab

theorem zero_pred : N Z
:= N_Z

definition succ (n : num) : num
:= abst (S (rep n)) inhab

theorem succ_pred (n : num) : N (S (rep n))
:= have N_n : N (rep n),
     from P_rep n,
   show N (S (rep n)),
     from N_S N_n

theorem succ_inj {a b : num} : succ a = succ b → a = b
:= assume Heq1 : succ a = succ b,
   have Heq2 : S (rep a) = S (rep b),
      from abst_inj inhab (succ_pred a) (succ_pred b) Heq1,
   have rep_eq : (rep a) = (rep b),
      from injective_S (rep a) (rep b) Heq2,
   show a = b,
      from rep_inj rep_eq

theorem succ_inj_rw {a b : num} : succ a = succ b ↔ a = b
:= iff_intro
     (assume Hl, succ_inj Hl)
     (assume Hr, congr2 succ Hr)

add_rewrite succ_inj_rw

theorem succ_nz (a : num) : ¬ (succ a = zero)
:= not_intro (assume R : succ a = zero,
   have Heq1 : S (rep a) = Z,
      from abst_inj inhab (succ_pred a) zero_pred R,
   show false,
      from absurd Heq1 (S_ne_Z (rep a)))

add_rewrite succ_nz

theorem induction {P : num → Bool} (H1 : P zero) (H2 : ∀ n, P n → P (succ n)) : ∀ a, P a
:= take a,
   let Q := λ x, N x ∧ P (abst x inhab)
   in have QZ : Q Z,
        from and_intro zero_pred H1,
      have QS : ∀ x, Q x → Q (S x),
        from take x, assume Qx,
               have Hp1 : P (succ (abst x inhab)),
                 from H2 (abst x inhab) (and_elimr Qx),
               have Hp2 : P (abst (S (rep (abst x inhab))) inhab),
                 from Hp1,
               have Nx : N x,
                 from and_eliml Qx,
               have rep_eq : rep (abst x inhab) = x,
                 from rep_abst inhab x Nx,
               show Q (S x),
                 from and_intro (N_S Nx) (subst Hp2 rep_eq),
      have Qa : P (abst (rep a) inhab),
        from and_elimr (N_smallest Q QZ QS (rep a) (P_rep a)),
      have abst_eq : abst (rep a) inhab = a,
        from abst_rep inhab a,
      show P a,
        from subst Qa abst_eq

theorem induction_on {P : num → Bool} (a : num) (H1 : P zero) (H2 : ∀ n, P n → P (succ n)) : P a
:= induction H1 H2 a

theorem dichotomy (m : num) : m = zero ∨ (∃ n, m = succ n)
:= induction_on m
     (by simp)
     (λ n iH, or_intror _
                        (@exists_intro _ (λ x, succ n = succ x) n (refl (succ n))))

theorem sn_ne_n (n : num) : succ n ≠ n
:= induction_on n
     (succ_nz zero)
     (λ (n : num) (iH : succ n ≠ n),
        not_intro
          (assume R : succ (succ n) = succ n,
              absurd (succ_inj R) iH))

add_rewrite sn_ne_n

set_opaque num  true
set_opaque Z    true
set_opaque S    true
set_opaque zero true
set_opaque succ true

definition lt (m n : num) := ∃ P, (∀ i, P (succ i) → P i) ∧ P m ∧ ¬ P n
infix 50 < : lt

theorem lt_elim {m n : num} {B : Bool} (H1 : m < n)
                (H2 : ∀ (P : num → Bool), (∀ i, P (succ i) → P i) → P m → ¬ P n → B)
                : B
:= obtain P Pdef, from H1,
   H2 P (and_eliml Pdef) (and_eliml (and_elimr Pdef)) (and_elimr (and_elimr Pdef))

theorem lt_intro {m n : num} {P : num → Bool} (H1 : ∀ i, P (succ i) → P i) (H2 : P m) (H3 : ¬ P n) : m < n
:= exists_intro P (and_intro H1 (and_intro H2 H3))

set_opaque lt true

theorem lt_nrefl (n : num) : ¬ (n < n)
:= not_intro
     (assume N : n < n,
      lt_elim N (λ P Pred Pn nPn, absurd Pn nPn))

add_rewrite lt_nrefl

theorem lt_succ {m n : num} : succ m < n → m < n
:= assume H : succ m < n,
   lt_elim H
     (λ (P : num → Bool) (Pred : ∀ i, P (succ i) → P i) (Psm : P (succ m)) (nPn : ¬ P n),
        have Pm : P m,
          from Pred m Psm,
        show m < n,
          from lt_intro Pred Pm nPn)

theorem not_lt_zero (n : num) : ¬ (n < zero)
:= induction_on n
      (show ¬ (zero < zero),
         from lt_nrefl zero)
      (λ (n : num) (iH : ¬ (n < zero)),
         show ¬ (succ n < zero),
           from not_intro
                  (assume N : succ n < zero,
                   have nLTzero : n < zero,
                     from lt_succ N,
                   show false,
                     from absurd nLTzero iH))

add_rewrite not_lt_zero

theorem zero_lt_succ_zero : zero < succ zero
:= let P : num → Bool := λ x, x = zero
   in have Ppred : ∀ i, P (succ i) → P i,
        from take i, assume Ps : P (succ i),
               have si_eq_z : succ i = zero,
                  from Ps,
               have si_ne_z : succ i ≠ zero,
                  from succ_nz i,
               show P i,
                  from absurd_elim (P i) si_eq_z (succ_nz i),
      have Pz : P zero,
        from (refl zero),
      have nPs : ¬ P (succ zero),
        from succ_nz zero,
      show zero < succ zero,
        from lt_intro Ppred Pz nPs

theorem succ_mono_lt {m n : num} : m < n → succ m < succ n
:= assume H : m < n,
   lt_elim H
     (λ (P : num → Bool) (Ppred : ∀ i, P (succ i) → P i) (Pm : P m) (nPn : ¬ P n),
        let Q : num → Bool := λ x, x = succ m ∨ P x
        in have Qpred : ∀ i, Q (succ i) → Q i,
             from take i, assume Qsi : Q (succ i),
                    or_elim Qsi
                      (assume Hl : succ i = succ m,
                         have Him : i = m, from succ_inj Hl,
                         have Pi  : P i,   from subst Pm (symm Him),
                           or_intror _ Pi)
                      (assume Hr : P (succ i),
                         have Pi  : P i,   from Ppred i Hr,
                           or_intror _ Pi),
           have Qsm   : Q (succ m),
             from or_introl (refl (succ m)) _,
           have nQsn  : ¬ Q (succ n),
             from not_intro
               (assume R : Q (succ n),
                  or_elim R
                    (assume Hl : succ n = succ m,
                       absurd Pm (subst nPn (succ_inj Hl)))
                    (assume Hr : P (succ n), absurd (Ppred n Hr) nPn)),
           show succ m < succ n,
             from lt_intro Qpred Qsm nQsn)

theorem lt_to_lt_succ {m n : num} : m < n → m < succ n
:= assume H : m < n,
   lt_elim H
     (λ (P : num → Bool) (Ppred : ∀ i, P (succ i) → P i) (Pm : P m) (nPn : ¬ P n),
        have nPsn : ¬ P (succ n),
          from not_intro
            (assume R : P (succ n),
               absurd (Ppred n R) nPn),
        show m < succ n,
          from lt_intro Ppred Pm nPsn)

theorem n_lt_succ_n (n : num) : n < succ n
:= induction_on n
     zero_lt_succ_zero
     (λ (n : num) (iH : n < succ n),
        succ_mono_lt iH)

add_rewrite n_lt_succ_n

theorem lt_to_neq {m n : num} : m < n → m ≠ n
:= assume H : m < n,
   lt_elim H
     (λ (P : num → Bool) (Ppred : ∀ i, P (succ i) → P i) (Pm : P m) (nPn : ¬ P n),
       not_intro
         (assume R : m = n,
            absurd Pm (subst nPn (symm R))))

theorem eq_to_not_lt {m n : num} : m = n → ¬ (m < n)
:= assume Heq : m = n,
     not_intro (assume R : m < n, absurd (subst R Heq) (lt_nrefl n))

theorem zero_lt_succ_n {n : num} : zero < succ n
:= induction_on n
     zero_lt_succ_zero
     (λ (n : num) (iH : zero < succ n),
        lt_to_lt_succ iH)

add_rewrite zero_lt_succ_n

theorem lt_succ_to_disj {m n : num} : m < succ n → m = n ∨ m < n
:= assume H : m < succ n,
   lt_elim H
     (λ (P : num → Bool) (Ppred : ∀ i, P (succ i) → P i) (Pm : P m) (nPsn : ¬ P (succ n)),
        or_elim (em (m = n))
          (assume Heq : m = n, or_introl Heq _)
          (assume Hne : m ≠ n,
             let Q : num → Bool := λ x, x ≠ n ∧ P x
             in have Qpred : ∀ i, Q (succ i) → Q i,
                  from take i, assume Hsi : Q (succ i),
                     have H1 : succ i ≠ n,
                       from and_eliml Hsi,
                     have Psi : P (succ i),
                       from and_elimr Hsi,
                     have Pi  : P i,
                       from Ppred i Psi,
                     have neq : i ≠ n,
                       from not_intro (assume N : i = n,
                           absurd (subst Psi N) nPsn),
                     and_intro neq Pi,
                have Qm : Q m,
                  from and_intro Hne Pm,
                have nQn : ¬ Q n,
                  from not_intro
                        (assume N : n ≠ n ∧ P n,
                           absurd (refl n) (and_eliml N)),
                show m = n ∨ m < n,
                  from or_intror _ (lt_intro Qpred Qm nQn)))

theorem disj_to_lt_succ {m n : num} : m = n ∨ m < n → m < succ n
:= assume H : m = n ∨ m < n,
     or_elim H
       (λ Hl : m = n,
          have H1 : n < succ n,
            from n_lt_succ_n n,
          show m < succ n,
            from subst H1 (symm Hl))
       (λ Hr : m < n, lt_to_lt_succ Hr)

theorem lt_succ_ne_to_lt {m n : num} : m < succ n → m ≠ n → m < n
:= assume (H1 : m < succ n) (H2 : m ≠ n),
     resolve1 (lt_succ_to_disj H1) H2

definition simp_rec_rel {A : (Type U)} (fn : num → A) (x : A) (f : A → A) (n : num)
:= fn zero = x ∧ (∀ m, m < n → fn (succ m) = f (fn m))

definition simp_rec_fun {A : (Type U)} (x : A) (f : A → A) (n : num) : num → A
:= ε (inhabited_fun num (inhabited_intro x)) (λ fn : num → A, simp_rec_rel fn x f n)

-- The basic idea is:
--   (simp_rec_fun x f n) returns a function that 'works' for all m < n
-- We have that n < succ n, then we can define (simp_rec x f n) as:
definition simp_rec {A : (Type U)} (x : A) (f : A → A) (n : num) : A
:= simp_rec_fun x f (succ n) n

theorem simp_rec_def {A : (Type U)} (x : A) (f : A → A) (n : num)
                     : (∃ fn, simp_rec_rel fn x f n)
                       ↔
                       (simp_rec_fun x f n zero = x ∧
                        ∀ m, m < n → simp_rec_fun x f n (succ m) = f (simp_rec_fun x f n m))
:= iff_intro
    (assume Hl : (∃ fn, simp_rec_rel fn x f n),
       obtain (fn : num → A) (Hfn : simp_rec_rel fn x f n),
         from Hl,
       have inhab : inhabited (num → A),
         from (inhabited_fun num (inhabited_intro x)),
       show simp_rec_rel (simp_rec_fun x f n) x f n,
         from @eps_ax (num → A) inhab (λ fn, simp_rec_rel fn x f n) fn Hfn)
    (assume Hr,
       have H1 : simp_rec_rel (simp_rec_fun x f n) x f n,
         from Hr,
       show (∃ fn, simp_rec_rel fn x f n),
         from exists_intro (simp_rec_fun x f n) H1)

theorem simp_rec_ex {A : (Type U)} (x : A) (f : A → A) (n : num)
                    : ∃ fn, simp_rec_rel fn x f n
:= induction_on n
     (let fn : num → A := λ n, x in
      have fz  : fn zero = x, by simp,
      have fs  : ∀ m, m < zero → fn (succ m) = f (fn m),
        from take m, assume Hmn : m < zero,
                absurd_elim (fn (succ m) = f (fn m))
                            Hmn
                            (not_lt_zero m),
      show ∃ fn, simp_rec_rel fn x f zero,
        from exists_intro fn (and_intro fz fs))
    (λ (n : num) (iH : ∃ fn, simp_rec_rel fn x f n),
       obtain (fn : num → A) (Hfn : simp_rec_rel fn x f n), from iH,
       let fn1 : num → A := λ m, if succ n = m then f (fn n) else fn m in
       have fnz : fn zero = x,  from and_eliml Hfn,
       have f1z : fn1 zero = x, by simp,
       have f1s : ∀ m, m < succ n → fn1 (succ m) = f (fn1 m),
         from take m, assume Hlt : m < succ n,
                 or_elim (lt_succ_to_disj Hlt)
                   (assume Hl : m = n, by simp)
                   (assume Hr : m < n,
                       have Haux1 : fn (succ m) = f (fn m),
                         from (and_elimr Hfn m Hr),
                       have Hrw1 : (succ n = succ m) ↔ false,
                         from eqf_intro (not_intro (assume N : succ n = succ m,
                                  have nLt : ¬ m < n,
                                    from eq_to_not_lt (symm (succ_inj N)),
                                  absurd Hr nLt)),
                       have Haux2 : m < succ n,
                         from lt_to_lt_succ Hr,
                       have Haux3 : ¬ (succ n = m),
                         from ne_symm (lt_to_neq Haux2),
                       have Hrw2 : fn m = fn1 m,
                          by simp,
                       calc fn1 (succ m) = if succ n = succ m then f (fn n) else fn (succ m) : refl (fn1 (succ m))
                                    ...  = if false then f (fn n) else fn (succ m)           : { Hrw1 }
                                    ...  = fn (succ m)                                       : if_false _ _
                                    ...  = f (fn m)                                          : Haux1
                                    ...  = f (fn1 m)                                         : { Hrw2 }),
       show ∃ fn, simp_rec_rel fn x f (succ n),
         from exists_intro fn1 (and_intro f1z f1s))


theorem simp_rec_lemma1 {A : (Type U)} (x : A) (f : A → A) (n : num)
                       : simp_rec_fun x f n zero = x ∧
                         ∀ m, m < n → simp_rec_fun x f n (succ m) = f (simp_rec_fun x f n m)
:= (simp_rec_def x f n) ◂ (simp_rec_ex x f n)

theorem simp_rec_lemma2 {A : (Type U)} (x : A) (f : A → A) (n m1 m2 : num)
                        : n < m1 → n < m2 → simp_rec_fun x f m1 n = simp_rec_fun x f m2 n
:= induction_on n
     (assume H1 H2,
          calc simp_rec_fun x f m1 zero = x                         : and_eliml (simp_rec_lemma1 x f m1)
                                   ...  = simp_rec_fun x f m2 zero  : symm (and_eliml (simp_rec_lemma1 x f m2)))
     (λ (n : num) (iH : n < m1 → n < m2 → simp_rec_fun x f m1 n = simp_rec_fun x f m2 n),
        assume (Hs1 : succ n < m1) (Hs2 : succ n < m2),
        have H1  : n < m1,
          from lt_succ Hs1,
        have H2  : n < m2,
          from lt_succ Hs2,
        have Heq1 : simp_rec_fun x f m1 (succ n) = f (simp_rec_fun x f m1 n),
          from and_elimr (simp_rec_lemma1 x f m1) n H1,
        have Heq2 : simp_rec_fun x f m1 n = simp_rec_fun x f m2 n,
          from iH H1 H2,
        have Heq3 : simp_rec_fun x f m2 (succ n) = f (simp_rec_fun x f m2 n),
          from and_elimr (simp_rec_lemma1 x f m2) n H2,
        show simp_rec_fun x f m1 (succ n) = simp_rec_fun x f m2 (succ n),
          by simp)

theorem simp_rec_thm {A : (Type U)} (x : A) (f : A → A)
                     : simp_rec x f zero = x ∧
                       ∀ m, simp_rec x f (succ m) = f (simp_rec x f m)
:= have Heqz : simp_rec_fun x f (succ zero) zero = x,
     from and_eliml (simp_rec_lemma1 x f (succ zero)),
   have Hz : simp_rec x f zero = x,
     from calc simp_rec x f zero = simp_rec_fun x f (succ zero) zero : refl _
                           ...   = x                                 : Heqz,
   have Hs : ∀ m, simp_rec x f (succ m) = f (simp_rec x f m),
     from take m,
       have Hlt1 : m < succ (succ m),
         from lt_to_lt_succ (n_lt_succ_n m),
       have Hlt2 : m < succ m,
         from n_lt_succ_n m,
       have Heq1 : simp_rec_fun x f (succ (succ m)) (succ m) = f (simp_rec_fun x f (succ (succ m)) m),
         from and_elimr (simp_rec_lemma1 x f (succ (succ m))) m Hlt1,
       have Heq2 : simp_rec_fun x f (succ (succ m)) m = simp_rec_fun x f (succ m) m,
         from simp_rec_lemma2 x f m (succ (succ m)) (succ m) Hlt1 Hlt2,
       calc simp_rec x f (succ m) = simp_rec_fun x f (succ (succ m)) (succ m) : refl _
                           ...    = f (simp_rec_fun x f (succ (succ m)) m)    : Heq1
                           ...    = f (simp_rec_fun x f (succ m) m)           : { Heq2 }
                           ...    = f (simp_rec x f m)                        : refl _,
   show simp_rec x f zero = x ∧ ∀ m, simp_rec x f (succ m) = f (simp_rec x f m),
     from and_intro Hz Hs

definition pre (m : num) := if m = zero then zero else ε inhab (λ n, succ n = m)

theorem pre_zero : pre zero = zero
:= by (Then (unfold num::pre) simp)

theorem pre_succ (m : num) : pre (succ m) = m
:= have Heq : (λ n, succ n = succ m) = (λ n, n = m),
     from funext (λ n, iff_intro (assume Hl, succ_inj Hl)
                                 (assume Hr, congr2 succ Hr)),
   calc pre (succ m) = ε inhab (λ n, succ n = succ m)  : by (Then (unfold num::pre) simp)
                 ... = ε inhab (λ n, n = m)            : { Heq }
                 ... = m                               : eps_singleton inhab m

add_rewrite pre_zero pre_succ

theorem succ_pre (m : num) : m ≠ zero → succ (pre m) = m
:= assume H : m ≠ zero,
   have H1 : ∃ n, m = succ n,
     from resolve1 (dichotomy m) H,
   obtain (w : num) (H2 : m = succ w), from H1,
   have H3 : (λ n, succ n = m) = (λ n, n = w),
     from funext (λ n, by simp),
   calc succ (pre m) = succ (if m = zero then zero else ε inhab (λ n, succ n = m)) : refl _
                 ... = succ (ε inhab (λ n, n = w))                                 : by simp
                 ... = succ w                                                      : { eps_singleton inhab w }
                 ... = m                                                           : symm H2

definition prim_rec_fun {A : (Type U)} (x : A) (f : A → num → A)
:= simp_rec (λ n : num, x) (λ fn n, f (fn (pre n)) n)

definition prim_rec {A : (Type U)} (x : A) (f : A → num → A) (m : num)
:= prim_rec_fun x f m (pre m)

theorem prim_rec_thm {A : (Type U)} (x : A) (f : A → num → A)
                     : prim_rec x f zero = x ∧
                       ∀ m, prim_rec x f (succ m) = f (prim_rec x f m) m
:= let faux := λ fn n, f (fn (pre n)) n in
   have Hz : prim_rec x f zero = x,
     from have Heq1 : simp_rec (λ n, x) faux zero = (λ n : num, x),
            from and_eliml (simp_rec_thm (λ n, x) faux),
          calc prim_rec x f zero = prim_rec_fun x f zero (pre zero)       : refl _
                           ...   = prim_rec_fun x f zero zero             : { pre_zero }
                           ...   = simp_rec (λ n, x) faux zero zero       : refl _
                           ...   = x                                      : congr1 Heq1 zero,
   have Hs : ∀ m, prim_rec x f (succ m) = f (prim_rec x f m) m,
     from take m,
        have Heq1 : pre (succ m) = m,
          from pre_succ m,
        have Heq2 : simp_rec (λ n, x) faux (succ m) = faux (simp_rec (λ n, x) faux m),
          from and_elimr (simp_rec_thm (λ n, x) faux) m,
        calc prim_rec x f (succ m) = prim_rec_fun x f (succ m) (pre (succ m)) : refl _
                              ...  = prim_rec_fun x f (succ m) m              : { Heq1 }
                              ...  = simp_rec (λ n, x) faux (succ m) m        : refl _
                              ...  = faux (simp_rec (λ n, x) faux m) m        : congr1 Heq2 m
                              ...  = f (prim_rec x f m) m                     : refl _,
   show prim_rec x f zero = x ∧ ∀ m, prim_rec x f (succ m) = f (prim_rec x f m) m,
     from and_intro Hz Hs

theorem prim_rec_zero {A : (Type U)} (x : A) (f : A → num → A) : prim_rec x f zero = x
:= and_eliml (prim_rec_thm x f)

theorem prim_rec_succ {A : (Type U)} (x : A) (f : A → num → A) (m : num) : prim_rec x f (succ m) = f (prim_rec x f m) m
:= and_elimr (prim_rec_thm x f) m

set_opaque simp_rec_rel true
set_opaque simp_rec_fun true
set_opaque simp_rec     true
set_opaque prim_rec_fun true
set_opaque prim_rec     true

definition add (a b : num) : num
:= prim_rec a (λ x n, succ x) b
infixl 65 + : add

theorem add_zeror (a : num) : a + zero = a
:= prim_rec_zero a (λ x n, succ x)

theorem add_succr (a b : num) : a + succ b = succ (a + b)
:= prim_rec_succ a (λ x n, succ x) b

definition mul (a b : num) : num
:= prim_rec zero (λ x n, x + a) b
infixl 70 * : mul

theorem mul_zeror (a : num) : a * zero = zero
:= prim_rec_zero zero (λ x n, x + a)

theorem mul_succr (a b : num) : a * (succ b) = a * b + a
:= prim_rec_succ zero (λ x n, x + a) b

add_rewrite add_zeror add_succr mul_zeror mul_succr

set_opaque add true
set_opaque mul true

theorem add_zerol (a : num) : zero + a = a
:= induction_on a (by simp) (by simp)

theorem add_succl (a b : num) : (succ a) + b = succ (a + b)
:= induction_on b (by simp) (by simp)

add_rewrite add_zerol add_succl

theorem add_comm (a b : num) : a + b = b + a
:= induction_on b (by simp) (by simp)

theorem add_assoc (a b c : num) : (a + b) + c = a + (b + c)
:= induction_on a (by simp) (by simp)

theorem add_left_comm (a b c : num) : a + (b + c) = b + (a + c)
:= left_comm add_comm add_assoc a b c

add_rewrite add_assoc add_comm add_left_comm

theorem mul_zerol (a : num) : zero * a = zero
:= induction_on a (by simp) (by simp)

theorem mul_succl (a b : num) : (succ a) * b = a * b + b
:= induction_on b (by simp) (by simp)

add_rewrite mul_zerol mul_succl

theorem mul_onel (a : num) : (succ zero) * a = a
:= induction_on a (by simp) (by simp)

theorem mul_oner (a : num) : a * (succ zero) = a
:= induction_on a (by simp) (by simp)

add_rewrite mul_onel mul_oner

theorem mul_comm (a b : num) : a * b = b * a
:= induction_on b (by simp) (by simp)

theorem distributer (a b c : num) : a * (b + c) = a * b + a * c
:= induction_on a (by simp) (by simp)

add_rewrite mul_comm distributer

theorem distributel (a b c : num) : (a + b) * c = a * c + b * c
:= induction_on a (by simp) (by simp)

add_rewrite distributel

theorem mul_assoc (a b c : num) : (a * b) * c = a * (b * c)
:= induction_on b (by simp) (by simp)

theorem mul_left_comm (a b c : num) : a * (b * c) = b * (a * c)
:= left_comm mul_comm mul_assoc a b c

add_rewrite mul_assoc mul_left_comm

theorem lt_addr {a b : num} (c : num) : a < b → a + c < b + c
:= assume H : a < b,
   induction_on c
     (by simp)
     (λ (c : num) (iH : a + c < b + c),
        have H1 : succ (a + c) < succ (b + c),
          from succ_mono_lt iH,
        show a + succ c < b + succ c,
          from subst (subst H1 (symm (add_succr a c))) (symm (add_succr b c)))

theorem addl_lt {a b c : num} : a + c < b → a < b
:= induction_on c
     (assume H : a + zero < b, subst H (add_zeror a))
     (λ (c : num) (iH : a + c < b → a < b),
        assume H : a + (succ c) < b,
        have H1 : succ (a + c) < b,
          from subst H (add_succr a c),
        have H2 : a + c < b,
          from lt_succ H1,
        show a < b, from iH H2)

theorem lt_to_nez {a b : num} (H : a < b) : b ≠ zero
:= not_intro (assume N : b = zero,
     absurd (subst H N) (not_lt_zero a))

theorem lt_ex1 {a b : num} : a < b → ∃ c, a + (succ c) = b
:= induction_on a
    (assume H : zero < b,
     have H1 : b ≠ zero, from lt_to_nez H,
     have H2 : succ (pre b) = b, from succ_pre b H1,
        show ∃ c, zero + (succ c) = b,
          from exists_intro (pre b) (by simp))
    (λ (a : num) (iH : a < b → ∃ c, a + (succ c) = b),
      assume H : succ a < b,
      have H1 : a < b, from lt_succ H,
      obtain (c : num) (Hc : a + (succ c) = b), from iH H1,
      have Hcnz : c ≠ zero,
        from not_intro (assume L1 : c = zero,
           have Hb : b = a + (succ c), from symm Hc,
           have L2 : succ a = b, by simp,
           show false, from absurd L2 (lt_to_neq H)),
      have Hspc : succ (pre c) = c,
        from succ_pre c Hcnz,
      show ∃ c, (succ a) + (succ c) = b,
          from exists_intro (pre c) (calc (succ a) + (succ (pre c)) = succ (a + c) : by simp
                                                                ... = a + (succ c) : symm (add_succr _ _)
                                                                ... = b            : Hc ))

theorem lt_ex2 {a b : num} : (∃ c, a + (succ c) = b) → a < b
:= assume Hex : ∃ c, a + (succ c) = b,
   obtain (c : num) (Hc : a + (succ c) = b), from Hex,
   have H1 : succ (a + c) = b,
      from subst Hc (add_succr a c),
   have H2 : a + c < b,
      from subst (n_lt_succ_n (a + c)) H1,
   show a < b,
      from addl_lt H2

theorem lt_ex (a b : num) : a < b ↔ ∃ c, a + (succ c) = b
:= iff_intro (assume Hl, lt_ex1 Hl) (assume Hr, lt_ex2 Hr)

theorem lt_to_ex {a b : num} (H : a < b) : ∃ c, a + (succ c) = b
:= lt_ex1 H

theorem ex_to_lt {a b c : num} (H : a + succ c = b) : a < b
:= lt_ex2 (exists_intro c H)

theorem lt_trans {a b c : num} : a < b → b < c → a < c
:= assume H1 H2,
   obtain (w1 : num) (Hw1 : a + succ w1 = b), from lt_to_ex H1,
   obtain (w2 : num) (Hw2 : b + succ w2 = c), from lt_to_ex H2,
   have Hac : a + succ (succ (w1 + w2)) = c,
     from calc a + succ (succ (w1 + w2)) = (a + succ w1) + succ w2 : by simp_no_assump
                                     ... = b + succ w2             : { Hw1 }
                                     ... = c                       : { Hw2 },
   ex_to_lt Hac

theorem strong_induction {P : num → Bool} (H : ∀ n, (∀ m, m < n → P m) → P n) : ∀ a, P a
:= take a : num,
   have stronger : P a ∧ ∀ m, m < a → P m,
    from induction_on a  -- we prove a stronger result by regular induction on a
       (have c2 : ∀ m, m < zero → P m,
          from λ (m : num) (Hlt : m < zero), absurd_elim (P m) Hlt (not_lt_zero m),
        have c1 : P zero,
          from H zero c2,
        show P zero ∧ ∀ m, m < zero → P m,
          from and_intro c1 c2)
       (λ (n : num) (iH : P n ∧ ∀ m, m < n → P m),
        have iH1 : P n,
          from and_eliml iH,
        have iH2 : ∀ m, m < n → P m,
          from and_elimr iH,
        have c2  : ∀ m, m < succ n → P m,
          from take m : num, assume Hlt : m < succ n,
                 or_elim (em (m = n))
                   (assume Heq : m = n, subst iH1 (symm Heq))
                   (assume Hne : m ≠ n, iH2 m (lt_succ_ne_to_lt Hlt Hne)),
        have c1  : P (succ n),
          from H (succ n) c2,
        and_intro c1 c2),
   show P a,
     from and_eliml stronger

end

definition num := num::num
