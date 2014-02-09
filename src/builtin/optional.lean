-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import macros
import subtype
using subtype
-- We are encoding the (optional A) as a subset of A → Bool where
--   none     is the predicate that is false everywhere
--   some(a)  is the predicate that is true only at a
definition optional_pred (A : (Type U)) := (λ p : A → Bool, (∀ x, ¬ p x) ∨ exists_unique p)
definition optional (A : (Type U)) := subtype (A → Bool) (optional_pred A)

namespace optional
theorem some_pred {A : (Type U)} (a : A) : optional_pred A (λ x, x = a)
:= or_intror
     (∀ x, ¬ x = a)
     (exists_intro a
       (and_intro (refl a) (take y, assume H : y ≠ a, H)))

theorem none_pred (A : (Type U)) : optional_pred A (λ x, false)
:= or_introl (take x, not_false_trivial) (exists_unique (λ x, false))

theorem inhab (A : (Type U)) : inhabited (optional A)
:= subtype_inhabited (exists_intro (λ x, false) (none_pred A))

definition none {A : (Type U)} : optional A
:= abst (λ x, false) (inhab A)

definition some {A : (Type U)} (a : A) : optional A
:= abst (λ x, x = a) (inhab A)

definition is_some {A : (Type U)} (n : optional A) := ∃ x : A, some x = n

theorem injectivity {A : (Type U)} {a a' : A} : some a = some a' → a = a'
:= assume Heq : some a = some a',
   have eq_reps : (λ x, x = a) = (λ x, x = a'),
      from abst_inj (inhab A) (some_pred a) (some_pred a') Heq,
   show a = a',
      from (congr1 a eq_reps) ◂ (refl a)

theorem distinct {A : (Type U)} (a : A) : some a ≠ none
:= not_intro (assume N : some a = none,
   have eq_reps : (λ x, x = a) = (λ x, false),
      from abst_inj (inhab A) (some_pred a) (none_pred A) N,
   show false,
      from (congr1 a eq_reps) ◂ (refl a))

definition value {A : (Type U)} (n : optional A) (H : is_some n) : A
:= ε (inhabited_ex_intro H) (λ x, some x = n)

theorem is_some_some {A : (Type U)} (a : A) : is_some (some a)
:= exists_intro a (refl (some a))

theorem not_is_some_none {A : (Type U)} : ¬ is_some (@none A)
:= not_intro (assume N : is_some (@none A),
   obtain (w : A) (Hw : some w = @none A),
      from N,
   show false,
      from absurd Hw (distinct w))

theorem value_some {A : (Type U)} (a : A) (H : is_some (some a)) : value (some a) H = a
:= have eq1  : some (value (some a) H) = some a,
      from eps_ax (inhabited_ex_intro H) a (refl (some a)),
   show value (some a) H = a,
      from injectivity eq1

theorem false_pred {A : (Type U)} {p : A → Bool} (H : ∀ x, ¬ p x) : p = λ x, false
:= funext (λ x, eqf_intro (H x))

theorem singleton_pred {A : (Type U)} {p : A → Bool} {w : A} (H : p w ∧ ∀ y, y ≠ w → ¬ p y) : p = (λ x, x = w)
:= funext (take x, iff_intro
     (assume Hpx : p x,
      show x = w,
         from refute (assume N : x ≠ w,
                      show false,
                         from absurd Hpx (and_elimr H x N)))
     (assume Heq : x = w,
      show p x,
         from subst (and_eliml H) (symm Heq)))

theorem dichotomy {A : (Type U)} (n : optional A) : n = none ∨ ∃ a, n = some a
:= have pred : optional_pred A (rep n),
      from P_rep n,
   show n = none ∨ ∃ a, n = some a,
      from or_elim pred
        (assume Hl : ∀ x : A, ¬ rep n x,
         have rep_n_eq     : rep n    = λ x, false,
            from false_pred Hl,
         have rep_none_eq  : rep none = λ x, false,
            from rep_abst (inhab A) (λ x, false) (none_pred A),
         show n = none ∨ ∃ a, n = some a,
            from or_introl (rep_inj (trans rep_n_eq (symm rep_none_eq)))
                           (∃ a, n = some a))
        (assume Hr : ∃ x, rep n x ∧ ∀ y, y ≠ x → ¬ rep n y,
         obtain (w : A) (Hw : rep n w ∧ ∀ y, y ≠ w → ¬ rep n y),
            from Hr,
         have rep_n_eq    : rep n        = λ x, x = w,
            from singleton_pred Hw,
         have rep_some_eq : rep (some w) = λ x, x = w,
            from rep_abst (inhab A) (λ x, x = w) (some_pred w),
         have n_eq_some   : n = some w,
            from rep_inj (trans rep_n_eq (symm rep_some_eq)),
         show n = none ∨ ∃ a, n = some a,
            from or_intror (n = none)
                           (exists_intro w n_eq_some))

theorem induction {A : (Type U)} {P : optional A → Bool} (H1 : P none) (H2 : ∀ x, P (some x)) : ∀ n, P n
:= take n, or_elim (dichotomy n)
    (assume Heq : n = none,
     show P n,
        from subst H1 (symm Heq))
    (assume Hex : ∃ a, n = some a,
     obtain (w : A) (Hw : n = some w),
        from Hex,
     show P n,
        from subst (H2 w) (symm Hw))

set_opaque some           true
set_opaque none           true
set_opaque is_some        true
set_opaque value          true
end

set_opaque optional       true
set_opaque optional_pred  true
definition optional_inhabited := optional::inhab
add_rewrite optional::is_some_some optional::not_is_some_none optional::distinct optional::value_some
