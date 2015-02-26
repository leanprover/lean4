prelude
import logic
namespace experiment
inductive nat : Type :=
| zero : nat
| succ : nat → nat

open eq

namespace nat
definition add (x y : nat)
:= nat.rec x (λ n r, succ r) y

infixl `+` := add

theorem add.left_id (x : nat) : x + zero = x
:= refl _

theorem succ_add (x y : nat) : x + (succ y) = succ (x + y)
:= refl _

definition is_zero (x : nat)
:= nat.rec true (λ n r, false) x

theorem is_zero_zero : is_zero zero
:= of_eq_true (refl _)

theorem not_is_zero_succ (x : nat) : ¬ is_zero (succ x)
:= not_of_eq_false (refl _)

theorem dichotomy (m : nat) : m = zero ∨ (∃ n, m = succ n)
:= nat.rec
     (or.intro_left _ (refl zero))
     (λ m H, or.intro_right _ (exists.intro m (refl (succ m))))
     m

theorem is_zero_to_eq (x : nat) (H : is_zero x) : x = zero
:= or.elim (dichotomy x)
     (assume Hz : x = zero, Hz)
     (assume Hs : (∃ n, x = succ n),
       exists.elim Hs (λ (w : nat) (Hw : x = succ w),
         absurd H (eq.subst (symm Hw) (not_is_zero_succ w))))

theorem is_not_zero_to_eq {x : nat} (H : ¬ is_zero x) : ∃ n, x = succ n
:= or.elim (dichotomy x)
     (assume Hz : x = zero,
       absurd (eq.subst (symm Hz) is_zero_zero) H)
     (assume Hs, Hs)

theorem not_zero_add (x y : nat) (H : ¬ is_zero y) : ¬ is_zero (x + y)
:= exists.elim (is_not_zero_to_eq H)
     (λ (w : nat) (Hw : y = succ w),
        have H1 : x + y = succ (x + w), from
          calc x + y = x + succ w   : {Hw}
                 ... = succ (x + w) : refl _,
        have H2 : ¬ is_zero (succ (x + w)), from
          not_is_zero_succ (x+w),
        subst (symm H1) H2)

inductive not_zero [class] (x : nat) : Prop :=
intro : ¬ is_zero x → not_zero x

theorem not_zero_not_is_zero {x : nat} (H : not_zero x) : ¬ is_zero x
:= not_zero.rec (λ H1, H1) H

theorem not_zero_add_right [instance] (x y : nat) (H : not_zero y) : not_zero (x + y)
:= not_zero.intro (not_zero_add x y (not_zero_not_is_zero H))

theorem not_zero_succ [instance] (x : nat) : not_zero (succ x)
:= not_zero.intro (not_is_zero_succ x)

constant dvd : Π (x y : nat) {H : not_zero y}, nat

constants a b : nat

set_option pp.implicit true
attribute add [reducible]
check dvd a (succ b)
check (λ H : not_zero b, dvd a b)
check (succ zero)
check a + (succ zero)
check dvd a (a + (succ b))

attribute add [irreducible]
check dvd a (a + (succ b))

attribute add [reducible]
check dvd a (a + (succ b))

attribute add [irreducible]
check dvd a (a + (succ b))

end nat
end experiment
