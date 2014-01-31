import Int

variable Real : Type
alias ℝ : Real
builtin int_to_real : Int → Real
coercion int_to_real
definition nat_to_real (a : Nat) : Real := int_to_real (nat_to_int a)
coercion nat_to_real

namespace Real
builtin numeral

builtin add : Real → Real → Real
infixl 65 + : add

builtin mul : Real → Real → Real
infixl 70 * : mul

builtin div : Real → Real → Real
infixl 70 / : div

builtin le : Real → Real → Bool
infix  50 <= : le
infix  50 ≤  : le

definition ge (a b : Real) : Bool := b ≤ a
infix 50 >= : ge
infix 50 ≥  : ge

definition lt (a b : Real) : Bool := ¬ (a ≥ b)
infix 50 <  : lt

definition gt (a b : Real) : Bool := ¬ (a ≤ b)
infix 50 >  : gt

definition sub (a b : Real) : Real := a + -1.0 * b
infixl 65 - : sub

definition neg (a : Real) : Real := -1.0 * a
notation 75 - _ : neg

definition abs (a : Real) : Real := if (0.0 ≤ a) then a else (- a)
notation 55 | _ | : abs
end
