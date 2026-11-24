/-!
When no alternatives are left, the match compiler splits first a discriminant whose split leaves
no subproblems, instead of splitting the discriminants before it and all their fields.
-/

inductive Kind where | float | double | longDouble
inductive Sign where | positive | negative
inductive NanKind where | quiet | signalling
inductive FloatClass where
  | zero
  | subnormal (significand : Nat)
  | normal (exponent : Int) (significand : Nat)
  | infinity
  | notANumber (kind : NanKind) (payload : Nat)
structure FloatDatum where
  sign : Sign
  floatClass : FloatClass
inductive FloatingValue where
  | real (part : FloatDatum)
  | imaginary (part : FloatDatum)
  | complex (realPart imaginaryPart : FloatDatum)
structure FloatValue where
  kind : Kind
  value : FloatingValue
  heldAt : Kind

set_option maxHeartbeats 1000

-- `nofun` takes `v` and `h : none = some v` as discriminants; only `h` needs to be split.
theorem ctorMismatch : ∀ v : FloatValue, (none : Option FloatValue) ≠ some v := nofun

def OnlyEmpty : List FloatValue → Prop
  | [] => True
  | _ :: _ => False

-- `h : OnlyEmpty (v :: vs)` reduces to `False`.
theorem reducesToFalse : ∀ (v : FloatValue) (vs : List FloatValue), ¬ OnlyEmpty (v :: vs) := nofun

structure Position where
  target : Nat
  datum : FloatDatum
  kind : Kind

-- `h : w ∈ []` is `List.Mem w []`, whose constructors' indices are all `_ :: _`.
theorem memNil (t : Nat) : ∀ w ∈ ([] : List (Position × FloatValue)), w.1.target ≠ t := nofun

-- Equations whose sides differ below the head constructor.
theorem nestedMismatch :
    ∀ v : FloatValue, (some none : Option (Option FloatValue)) ≠ some (some v) := nofun
theorem pairMismatch : ∀ v : FloatValue, ((1 : Nat), (none : Option FloatValue)) ≠ (1, some v) :=
  nofun
theorem natLiterals : ∀ v : FloatValue, ((2 : Nat), v) ≠ (3, v) := nofun
theorem ctorIdxMismatch :
    ∀ (_ : FloatValue) (d : FloatDatum),
      (FloatingValue.real d).ctorIdx ≠ (FloatingValue.complex d d).ctorIdx := nofun
theorem heqMismatch : ∀ v : FloatValue, ¬ HEq (none : Option FloatValue) (some v) := nofun

-- Families whose constructors' indices are literals or offsets.
inductive Two : Nat → Bool → Prop where
  | a : Two 0 true
  | b : Two 1 false
theorem literalIndex : ∀ _ : FloatValue, ¬ Two 0 false := nofun

inductive Even : Nat → Prop where
  | zero : Even 0
  | ss : Even n → Even (n + 2)
theorem offsetIndex : ∀ _ : FloatValue, ¬ Even 1 := nofun
