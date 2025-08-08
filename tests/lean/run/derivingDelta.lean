/-!
# Tests for delta deriving of instances for definitions

In this file we test both `deriving` clauses on definitions and `deriving instance` commands.
-/

/-!
Simple definition, body has instance immediately.
-/
def P1 : Prop := 1 = 1
deriving Decidable

def P1' : Prop := 1 = 1
deriving instance Decidable for P1'

/-!
Parameterized instance, deriving goes underneath `fun x y => ...`
-/
def Rel (x y : Nat) : Prop := x = y
deriving Decidable

def Rel' (x y : Nat) : Prop := x = y
deriving instance Decidable for Rel'

/-!
Another parameterized instance.
-/
def MyFin (n : Nat) : Type := Fin n
deriving DecidableEq

/-!
Multiple unfolding
-/
def MyFin' (n : Nat) : Type := MyFin (n + 1)
deriving Inhabited

/-!
Outparam support. Skips outparams.
-/
def IOReader (α : Type) := ReaderT α IO
deriving MonadReader

def MyList (α : Type) := List α
deriving Membership

/-!
Allows metavariables in the class. These get abstracted.
-/
def MyNat := Nat
deriving OfNat

/-- info: instMyNatOfNat (x✝ : Nat) : OfNat MyNat x✝ -/
#guard_msgs in #check instMyNatOfNat

/-!
"Mixin" instances
-/
class C1 {α : Sort _} [DecidableEq α] (β : α → Type)
instance : C1 Fin := {}

def MyFin'' := Fin
deriving C1

/-- info: instMyFin''C1 : @C1 Nat instDecidableEqNat MyFin'' -/
#guard_msgs in set_option pp.explicit true in #check instMyFin''C1

/-!
Error to mix both inductives and defs in the same `deriving instance` command.
Rationale: none of the deriving handlers for inductives unfold definitions,
so it is clearer if we make `deriving instance` have two distinct modes.
-/
inductive I1 | mk
def D1 := Unit
/--
error: Declaration `I1` is not a definition.

Note: When any declaration is a definition, this command goes into delta deriving mode, which applies only to definitions. Delta deriving unfolds definitions and infers pre-existing instances.
-/
#guard_msgs in deriving instance Inhabited for I1, D1
deriving instance Inhabited for D1

/-!
No such class
-/
/-- error: Unknown constant `NotAClass` -/
#guard_msgs in deriving instance NotAClass for D1

/-!
Not a class
-/
/-- error: Failed to delta derive `Nat` instance for `D1`, `Nat` is not a class. -/
#guard_msgs in deriving instance Nat for D1

/-!
No such definition
-/
/-- error: Unknown constant `NotADefinition` -/
#guard_msgs in deriving instance Inhabited for NotADefinition

/-!
Delta deriving fails due to synthesis failure.
-/
/--
error: Failed to delta derive `Inhabited` instance for `D2`.

Failed to synthesize instance
n : Nat
⊢ Inhabited (Fin n)

Note: Delta deriving tries the following strategies: (1) inserting the definition into each explicit non-out-param parameter of a class and (2) further unfolding of definitions.
-/
#guard_msgs in
def D2 (n : Nat) := Fin n
deriving Inhabited

/-!
Delta deriving fails due to no way to construct the class type.
-/
/--
error: Failed to delta derive `Decidable` instance for `D3`, the class has no explicit non-out-param parameters where
  D3
can be inserted.
-/
#guard_msgs in
def D3 := Bool
deriving Decidable
