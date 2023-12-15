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
