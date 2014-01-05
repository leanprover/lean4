import Nat

variable Int : Type
alias ℤ : Int
builtin nat_to_int : Nat → Int
coercion nat_to_int

namespace Int
builtin numeral

builtin add : Int → Int → Int
infixl 65 + : add

builtin mul : Int → Int → Int
infixl 70 * : mul

builtin div : Int → Int → Int
infixl 70 div : div

builtin le : Int → Int → Bool
infix  50 <= : le
infix  50 ≤  : le

definition ge (a b : Int) : Bool := b ≤ a
infix 50 >= : ge
infix 50 ≥  : ge

definition lt (a b : Int) : Bool := ¬ (a ≥ b)
infix 50 <  : lt

definition gt (a b : Int) : Bool := ¬ (a ≤ b)
infix 50 >  : gt

definition sub (a b : Int) : Int := a + -1 * b
infixl 65 - : sub

definition neg (a : Int) : Int := -1 * a
notation 75 - _ : neg

definition mod (a b : Int) : Int := a - b * (a div b)
infixl 70 mod : mod

definition divides (a b : Int) : Bool := (b mod a) = 0
infix 50 | : divides

definition abs (a : Int) : Int := if (0 ≤ a) a (- a)
notation 55 | _ | : abs

setopaque sub true
setopaque neg true
setopaque mod true
setopaque divides true
setopaque abs true
setopaque ge true
setopaque lt true
setopaque gt true
end

namespace Nat
definition sub (a b : Nat) : Int := nat_to_int a - nat_to_int b
infixl 65 - : sub

definition neg (a : Nat) : Int := - (nat_to_int a)
notation 75 - _ : neg

setopaque sub true
setopaque neg true
end