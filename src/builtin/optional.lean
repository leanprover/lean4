import subtype
import macros
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

theorem optional_inhabited (A : (Type U)) : inhabited (optional A)
:= subtype_inhabited (exists_intro (λ x, false) (none_pred A))

definition none {A : (Type U)} : optional A
:= abst (λ x, false) (optional_inhabited A)

definition some {A : (Type U)} (a : A) : optional A
:= abst (λ x, x = a) (optional_inhabited A)

definition is_some {A : (Type U)} (n : optional A) := ∃ x : A, some x = n

theorem injectivity {A : (Type U)} {a a' : A} : some a = some a' → a = a'
:= assume Heq,
     let eq_reps : (λ x, x = a) = (λ x, x = a') := abst_inj (optional_inhabited A) (some_pred a) (some_pred a') Heq
     in  (congr1 a eq_reps) ◂ (refl a)

theorem distinct {A : (Type U)} (a : A) : some a ≠ none
:= assume N : some a = none,
     let eq_reps : (λ x, x = a) = (λ x, false) := abst_inj (optional_inhabited A) (some_pred a) (none_pred A) N
     in (congr1 a eq_reps) ◂ (refl a)

definition value {A : (Type U)} (n : optional A) (H : is_some n) : A
:= ε (inhabited_ex_intro H) (λ x, some x = n)

theorem is_some_some {A : (Type U)} (a : A) : is_some (some a)
:= exists_intro a (refl (some a))

theorem not_is_some_none {A : (Type U)} : ¬ is_some (@none A)
:= assume N : is_some (@none A),
     obtain (w : A) (Hw : some w = @none A), from N,
       absurd Hw (distinct w)

theorem value_some {A : (Type U)} (a : A) (H : is_some (some a)) : value (some a) H = a
:= let eq1  : some (value (some a) H) = some a := eps_ax (inhabited_ex_intro H) a (refl (some a))
   in injectivity eq1

-- TODO
-- theorem dichotomy {A : (Type U)} (n : optional A) : n = none ∨ ∃ a, n = some a
-- theorem induction {A : (Type U)} {P : optional A → Bool} (H1 : P none) (H2 : ∀ x, P (some x)) : ∀ o, P o

set_opaque some           true
set_opaque none           true
set_opaque is_some        true
set_opaque value          true
end
set_opaque optional       true
set_opaque optional_pred  true
definition optional_inhabited := optional::optional_inhabited
add_rewrite optional::is_some_some optional::not_is_some_none optional::distinct optional::value_some

