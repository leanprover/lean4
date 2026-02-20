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
Derived instances go into the current namespace at the point of derivation.
-/
def MyLib.MyUnit := Unit
deriving Inhabited
deriving instance Nonempty for MyLib.MyUnit

/-- info: MyLib.instInhabitedMyUnit -/
#guard_msgs in #synth Inhabited MyLib.MyUnit
/-- info: instNonemptyMyUnit -/
#guard_msgs in #synth Nonempty MyLib.MyUnit

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

/--
info: @[implicit_reducible] def instOfNatMyNat : (_x_1 : Nat) → OfNat MyNat _x_1 :=
fun _x_1 => instOfNatNat _x_1
-/
#guard_msgs in #print instOfNatMyNat

/-!
Explicit parameterization
-/
deriving instance (n : Nat) → OfNat _ n for MyNat
/--
info: @[implicit_reducible] def instOfNatMyNat_1 : (n : Nat) → OfNat MyNat n :=
fun n => instOfNatNat n
-/
#guard_msgs in #print instOfNatMyNat_1

/-!
Explicit parameterization using section variables
-/
section
variable (m : Nat)
deriving instance OfNat _ m for MyNat
end
/--
info: @[implicit_reducible] def instOfNatMyNat_2 : (m : Nat) → OfNat MyNat m :=
fun m => instOfNatNat m
-/
#guard_msgs in #print instOfNatMyNat_2

/-!
Can synthesize specific OfNat instances.
-/
def MyNat' := Nat
deriving OfNat _ 1

deriving instance OfNat _ 2 for MyNat'

/-- info: instOfNatMyNat'OfNatNat -/
#guard_msgs in #synth OfNat MyNat' 1
/-- info: instOfNatMyNat'OfNatNat_1 -/
#guard_msgs in #synth OfNat MyNat' 2
/--
error: failed to synthesize
  OfNat MyNat' 3

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #synth OfNat MyNat' 3

/-!
Don't unify with nontrivial arguments supplied by the user.
Without the nontriviality check, would get `instHAddMyNatNat : HAdd MyNat Nat Nat`.
-/
deriving instance HAdd Nat for MyNat
/-- info: instHAddNatMyNat : HAdd Nat MyNat Nat -/
#guard_msgs in #check instHAddNatMyNat

deriving instance HAdd _ Nat for MyNat
/-- info: instHAddMyNatNat : HAdd MyNat Nat Nat -/
#guard_msgs in #check instHAddMyNatNat

/-!
"Mixin" instances
-/
class C1 {α : Sort _} [DecidableEq α] (β : α → Type _)
instance : C1 Fin := {}

def MyFin'' := Fin
deriving C1

/--
info: @[implicit_reducible] def instC1NatMyFin'' : @C1 Nat instDecidableEqNat MyFin'' :=
instC1NatFin
-/
#guard_msgs in set_option pp.explicit true in #print instC1NatMyFin''

/-!
Can catch mixin failure
-/
instance (inst : DecidableEq (Type _)) : C1 List := {}

/--
error: failed to synthesize instance of type class
  DecidableEq (Type u_1)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: Failed to delta derive `C1` instance for `MyList'`.

Note: Delta deriving tries the following strategies: (1) inserting the definition into each explicit non-out-param parameter of a class and (2) unfolding definitions further.
-/
#guard_msgs in
def MyList' := List
deriving C1

/-!
Can use explicit argument that's not the first.
-/
class OfNat' (n : Nat) (α : Type) where
instance (n : Nat) : OfNat' n Int := {}
def MyInt := Int
deriving OfNat', OfNat
/--
info: @[implicit_reducible] def instOfNat'MyInt : (_x_1 : Nat) → OfNat' _x_1 MyInt :=
fun _x_1 => instOfNat'Int _x_1
-/
#guard_msgs in #print instOfNat'MyInt
/--
info: @[implicit_reducible] def instOfNatMyInt : (_x_1 : Nat) → OfNat MyInt _x_1 :=
fun _x_1 => instOfNat
-/
#guard_msgs in #print instOfNatMyInt

/-!
Deriving `Module` over different base rings.
-/
class Semiring (R : Type _) where
class Module (R : Type _) [Semiring R] (α : Type _) where
instance : Semiring Nat := {}
instance : Semiring Int := {}
opaque V : Type
instance : Module Nat V := {}
instance : Module Int V := {}

def W := V
deriving Module Nat, Module Int

/-- info: instModuleNatW -/
#guard_msgs in #synth Module Nat W
/-- info: instModuleIntW -/
#guard_msgs in #synth Module Int W

/-!
Deriving and making use of binders.
-/
instance (R : Type _) [Semiring R] : Module R R := {}
def NewRing (R : Type _) [Semiring R] := R
deriving Module R

/--
info: @[implicit_reducible] def instModuleNewRing.{u_1} : (R : Type u_1) → [inst : Semiring R] → Module R (NewRing R) :=
fun R [Semiring R] => instModule R
-/
#guard_msgs in #print instModuleNewRing

/-!
`deriving instance` cannot make use of the definition's parameter names (they're introduced hygienically)
-/
/-- error: Unknown identifier `R` -/
#guard_msgs in deriving instance Module R for NewRing

/-!
Can make use of section variables when using the `deriving instance` command.
-/
section
variable (R : Type _) [Semiring R]
def NewRing' (R : Type _) := R
deriving instance Module R for NewRing' R

/--
info: @[implicit_reducible] def instModuleNewRing'.{u_1} : (R : Type u_1) → [inst : Semiring R] → Module R (NewRing' R) :=
fun R [Semiring R] => instModule R
-/
#guard_msgs in #print instModuleNewRing'
end

/-!
Multiple options, one works due to dependent types.
-/
class C2 (α : Sort _) (β : α) where
instance : C2 Type Prop := {}
-- set_option trace.Elab.Deriving true
def Prop' := Prop
deriving C2
/--
info: @[implicit_reducible] def instC2TypeProp' : C2 Type Prop' :=
instC2TypeProp
-/
#guard_msgs in #print instC2TypeProp'

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
/-- error: Unknown identifier `NotAClass` -/
#guard_msgs in deriving instance NotAClass for D1

/-!
Not a class
-/
/--
error: Failed to delta derive instance for `D1`, not a class:
  Nat
-/
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
error: failed to synthesize instance of type class
  Inhabited (Fin n)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: Failed to delta derive `Inhabited` instance for `D2`.

Note: Delta deriving tries the following strategies: (1) inserting the definition into each explicit non-out-param parameter of a class and (2) unfolding definitions further.
-/
#guard_msgs in
def D2 (n : Nat) := Fin n
deriving Inhabited

/--
error: failed to synthesize instance of type class
  Inhabited (D2 n)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: Failed to delta derive `Inhabited` instance for `D2'`.

Note: Delta deriving tries the following strategies: (1) inserting the definition into each explicit non-out-param parameter of a class and (2) unfolding definitions further.
-/
#guard_msgs in
def D2' (n : Nat) := D2 n
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
