import Lean
/-!
# Escaping names that are tokens when pretty printing
-/


/-!
Variable that's a token.
-/
section
variable («forall» : Nat)

/-- info: «forall» + 1 : Nat -/
#guard_msgs in #check «forall» + 1
end


/-!
Constant that's a token
-/
def «forall» := 1

/-- info: «forall» + 1 : Nat -/
#guard_msgs in #check «forall» + 1


/-!
Don't escape name components that are tokens if the prefix is not a token.
-/
def Exists.forall := 1

/-- info: Exists.forall : Nat -/
#guard_msgs in #check Exists.forall


/-!
Overly cautious for tokens that are prefixes.
-/
def forall.congr := 1

/-- info: «forall».congr : Nat -/
#guard_msgs in #check forall.congr


/-!
Escape the last name component to avoid a token.
-/
notation "Exists.forall" => true

/-- info: Exists.«forall» : Nat -/
#guard_msgs in #check «Exists».forall
/-- info: Exists.forall : Bool -/
#guard_msgs in #check Exists.forall
