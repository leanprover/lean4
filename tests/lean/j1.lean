import tactic
import macros

definition bracket (A : Type) : Bool :=
      ∀ p : Bool, (A → p) → p

rewrite_set basic
add_rewrite imp_truel imp_truer imp_id eq_id : basic

theorem bracket_eq (x : Bool) : bracket x = x
:= boolext
    (assume H : ∀ p : Bool, (x → p) → p,
       (have ((x → x) → x) = x : by simp basic) ◂ H x)
    (assume H : x,
       take p,
          assume Hxp : x → p,
            Hxp H)

add_rewrite bracket_eq eq_id

theorem coerce (a b : Bool) (H : @eq Type a b) : @eq Bool a b
:=  calc a   = bracket a  : by simp
         ... = bracket b  : @subst Type a b (λ x : Type, bracket a = bracket x) (refl (bracket a)) H
         ... = b          : by simp
