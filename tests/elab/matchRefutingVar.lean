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
