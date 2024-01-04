/-!
# Testing that binop% etc. have a quot_precheck
-/

section
variable (a b : Nat)

/-!
binop%
-/
local notation "c1" => a + b
/-!
rightact%
-/
local notation "c2" => a ^ b
/-!
binrel%
-/
local notation "c3" => a ≤ b
/-!
binrel_no_prop%
-/
local notation "c4" => a == b
/-!
unop%
-/
local notation "c5" => -(a : Int)
/-!
leftact% (artificial test because there is no notation using it in core Lean)
-/
local notation "c6" => leftact% HAdd.hAdd a b

example : c1 = a + b := rfl
example : c2 = a ^ b := rfl
example : c3 = (a ≤ b) := rfl
example : c4 = (a == b) := rfl
example : c5 = -a := rfl
example : c6 = a + b := rfl
end

section
variable (a b : Option Nat)

/-!
binop_lazy%
-/
local notation "c7" => a <|> b

example : c7 = (a <|> b) := rfl

end

/-!
Precheck failure in first argument.
-/
notation "precheckFailure" x y => binop% a x y

/-!
Precheck failure in second argument.
-/
notation "precheckFailure" y => binop% HAdd.hAdd a y

/-!
Precheck failure in third argument.
-/
notation "precheckFailure" x => binop% HAdd.hAdd x a

/-!
No precheck failure when `quotPrecheck` is off.
-/
set_option quotPrecheck false in
notation "skipPrecheck" => binop% a b c
