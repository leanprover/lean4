-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import num subtype optional macros tactic
using num
using subtype

namespace list
definition none {A : (Type U)} : optional A
:= optional::@none A

definition some {A : (Type U)} (a : A) : optional A
:= optional::some a

definition list_rep (A : (Type U))
:= (num → optional A) # num

definition list_pred (A : (Type U))
:= λ p : list_rep A, ∀ i, i < (proj2 p) ↔ (proj1 p) i ≠ (@none A)

definition list (A : (Type U))
:= subtype (list_rep A) (list_pred A)

definition len {A : (Type U)} (l : list A) : num
:= proj2 (rep l)

definition fn {A : (Type U)} (l : list A) : num → optional A
:= proj1 (rep l)

theorem ext {A : (Type U)} {l1 l2 : list A} (H1 : len l1 = len l2) (H2 : fn l1 = fn l2) : l1 = l2
:= have Heq : rep l1 = rep l2,
     from pairext _ _ H2 (to_heq H1),
   rep_inj Heq

definition nil_rep (A : (Type U)) : list_rep A
:= (pair (λ n : num, @none A) zero : list_rep A)

theorem nil_pred (A : (Type U)) : list_pred A (nil_rep A)
:= take i : num,
   let nil := nil_rep A
   in iff_intro
     (assume Hl : i < (proj2 nil),
      have H1 : i < zero,
        from Hl,
      absurd_elim ((proj1 nil) i ≠ (@none A)) H1 (not_lt_zero i))
     (assume Hr : (proj1 nil) i ≠ (@none A),
      have H1 : (@none A) ≠ (@none A),
        from Hr,
      false_elim (i < (proj2 nil)) (a_neq_a_elim H1))

theorem inhab (A : (Type U)) : inhabited (list A)
:= subtype_inhabited (exists_intro (nil_rep A) (nil_pred A))

definition nil {A : (Type U)} : list A
:= abst (nil_rep A) (list::inhab A)

theorem len_nil {A : (Type U)} : len (@nil A) = zero
:= have H1 : rep (@nil A) = (pair (λ n : num, @none A) zero : list_rep A),
     from rep_abst (list::inhab A) (nil_rep A) (nil_pred A),
   have H2 : len (@nil A) = proj2 (rep (@nil A)),
     from refl (len (@nil A)),
   have H3 : proj2 (rep (@nil A)) = zero,
     from proj2_congr H1,
   trans H2 H3

definition cons_rep {A : (Type U)} (h : A) (t : list A) : list_rep A
:= pair (λ n, if n = (len t) then (some h) else (fn t) n) (succ (len t))

theorem cons_rep_fn_at {A : (Type U)} (h : A) (t : list A) (i : num)
                       : (proj1 (cons_rep h t)) i = (if i = len t then some h else (fn t) i)
:= have Heq : proj1 (cons_rep h t) = λ n, if n = len t then some h else (fn t) n,
     from refl (proj1 (cons_rep h t)),
   congr1 Heq i

definition cons_pred {A : (Type U)} (h : A) (t : list A) : list_pred A (cons_rep h t)
:= take i : num,
   let  c   := cons_rep h t in
   have Hci : (proj1 c) i = (if i = (len t) then (some h) else (fn t) i),
     from cons_rep_fn_at h t i,
   have Ht  : ∀ i, i < (len t) ↔ (fn t) i ≠ (@none A),
     from P_rep t,
   iff_intro
     (assume Hl : i < (succ (len t)),
      or_elim (em (i = len t))
         (assume Heq : i = len t,
           calc (proj1 c) i = (if i = (len t) then (some h) else (fn t) i) : Hci
                        ... = some h                                       : by simp
                        ... ≠ @none A                                      : optional::distinct h)
         (assume Hne : i ≠ len t,
           have Hlt : i < len t,
             from lt_succ_ne_to_lt Hl Hne,
           calc (proj1 c) i = (if i = (len t) then (some h) else (fn t) i) : Hci
                        ... = (fn t) i                                     : by simp
                        ... ≠ @none A                                      : (Ht i) ◂ Hlt))
     (assume Hr : (proj1 c) i ≠ (@none A),
      or_elim (em (i = len t))
         (assume Heq : i = len t,
           subst (n_lt_succ_n (len t)) (symm Heq))
         (assume Hne : i ≠ len t,
           have Hne2 : (fn t) i ≠ (@none A),
             from calc (fn t) i = (if i = (len t) then (some h) else (fn t) i) : by simp
                            ... = (proj1 c) i                                  : symm Hci
                            ... ≠ (@none A)                                    : Hr,
           have Hlt : i < len t,
             from (symm (Ht i)) ◂ Hne2,
           show i < succ (len t),
             from lt_to_lt_succ Hlt))

definition cons {A : (Type U)} (h : A) (t : list A) : list A
:= abst (cons_rep h t) (list::inhab A)

theorem cons_fn_at {A : (Type U)} (h : A) (t : list A) (i : num)
                       : (fn (cons h t)) i = (if i = len t then some h else (fn t) i)
:= have H1 : rep (cons h t) = (cons_rep h t) ,
     from rep_abst (list::inhab A) (cons_rep h t) (cons_pred h t),
   have H2 : fn (cons h t) = proj1 (cons_rep h t),
     from proj1_congr H1,
   have H3 : fn (cons h t) i = (proj1 (cons_rep h t)) i,
     from congr1 H2 i,
   have H4 : (proj1 (cons_rep h t)) i = (if i = len t then some h else (fn t) i),
     from cons_rep_fn_at h t i,
   trans H3 H4

theorem len_cons {A : (Type U)} (h : A) (t : list A) : len (cons h t) = succ (len t)
:= have H1 : rep (cons h t) = cons_rep h t,
     from rep_abst (list::inhab A) (cons_rep h t) (cons_pred h t),
   have H2 : proj2 (cons_rep h t) = succ (len t),
     from refl (proj2 (cons_rep h t)),
   have H3 : proj2 (rep (cons h t)) = proj2 (cons_rep h t),
     from proj2_congr H1,
   trans H3 H2

theorem cons_ne_nil {A : (Type U)} (h : A) (t : list A) : cons h t ≠ nil
:= not_intro (assume R : cons h t = nil,
   have Heq1 : cons_rep h t = (nil_rep A),
      from abst_inj (list::inhab A) (cons_pred h t) (nil_pred A) R,
   have Heq2 : succ (len t) = zero,
      from proj2_congr Heq1,
   absurd Heq2 (succ_nz (len t)))

theorem flip_iff {a b : Bool} (H : a ↔ b) : ¬ a ↔ ¬ b
:= subst (refl (¬ a)) H

theorem cons_inj {A : (Type U)} {h1 h2 : A} {t1 t2 : list A} : cons h1 t1 = cons h2 t2 → h1 = h2 ∧ t1 = t2
:= assume Heq : cons h1 t1 = cons h2 t2,
   have Heq_rep : (cons_rep h1 t1) = (cons_rep h2 t2),
     from abst_inj (list::inhab A) (cons_pred h1 t1) (cons_pred h2 t2) Heq,
   have Heq_len : len t1 = len t2,
     from succ_inj (proj2_congr Heq_rep),
   have Heq_fn  : (λ n, if n = len t2 then some h1 else (fn t1) n) =
                  (λ n, if n = len t2 then some h2 else (fn t2) n),
     from subst (proj1_congr Heq_rep) Heq_len,
   have Heq_some : some h1 = some h2,
     from calc some h1 = if len t2 = len t2 then some h1 else (fn t1) (len t2)  : by simp
                   ... = if len t2 = len t2 then some h2 else (fn t2) (len t2)  : congr1 Heq_fn (len t2)
                   ... = some h2                                                : by simp,
   have Heq_head : h1 = h2,
     from optional::injectivity Heq_some,
   have Heq_fn_t : fn t1 = fn t2,
     from funext (λ i,
                    or_elim (em (i = len t2))
                      (λ Heqi : i = len t2,
                         have Hlti2 : ¬ (i < len t2),
                           from eq_to_not_lt Heqi,
                         have Hlti1 : ¬ (i < len t1),
                           from subst Hlti2 (symm Heq_len),
                         have Ht1 : i < len t1 ↔ (fn t1) i ≠ (@none A),
                           from P_rep t1 i,
                         have Ht2 : i < len t2 ↔ (fn t2) i ≠ (@none A),
                           from P_rep t2 i,
                         have Heq1 : (fn t1) i = (@none A),
                           from not_not_elim ((flip_iff Ht1) ◂ Hlti1),
                         have Heq2 : (fn t2) i = (@none A),
                           from not_not_elim ((flip_iff Ht2) ◂ Hlti2),
                         trans Heq1 (symm Heq2))
                      (λ Hnei : i ≠ len t2,
                         calc fn t1 i = if i = len t2 then some h1 else (fn t1) i : by simp
                                  ... = if i = len t2 then some h2 else (fn t2) i : congr1 Heq_fn i
                                  ... = fn t2 i                                   : by simp)),
   have Heq_tail : t1 = t2,
     from ext Heq_len Heq_fn_t,
   and_intro Heq_head Heq_tail

theorem cons_inj_head {A : (Type U)} {h1 h2 : A} {t1 t2 : list A} : cons h1 t1 = cons h2 t2 → h1 = h2
:= assume H, and_eliml (cons_inj H)

theorem cons_inj_tail {A : (Type U)} {h1 h2 : A} {t1 t2 : list A} : cons h1 t1 = cons h2 t2 → t1 = t2
:= assume H, and_elimr (cons_inj H)

set_opaque list true
set_opaque cons true
set_opaque nil  true
set_opaque len  true
end
definition list := list::list