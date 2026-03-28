/-!
# Tests of generalized field notation in recursive functions
-/

namespace Test1
/-!
We do not consider dot notation for local decls corresponding to recursive functions being defined.
The following example would not be elaborated correctly without this case.
-/
def foo.aux := 1
def foo : Nat → Nat
  | n => foo.aux -- should not be interpreted as `(foo).bar`
end Test1

namespace Issue10044
/-!
Private recursive definitions on private types.
-/
private inductive IfExpr
  | lit : Bool → IfExpr
  | var : Nat → IfExpr
  | ite : IfExpr → IfExpr → IfExpr → IfExpr

namespace IfExpr

private def hasNestedIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite (ite _ _ _) _ _ => true
  | ite _ t e => t.hasNestedIf || e.hasNestedIf --- Invalid field `hasNestedIf`

end IfExpr
end Issue10044

/-!
Checking that the name of the function being defined is reported.
-/
/--
error: Invalid field notation: Function `testError1` does not have a usable parameter of type `Bool` for which to substitute `true`

Note: Such a parameter must be explicit, or implicit with a unique name, to be used by field notation
-/
#guard_msgs in
def Bool.testError1 (n : Nat) : Nat :=
  (true).testError1

/-!
Checking that the name of the function being defined is reported, even if it is a `private` definition.
This used to print with a `_private` prefix.
-/
/--
error: Invalid field notation: Function `testError2` does not have a usable parameter of type `Bool` for which to substitute `true`

Note: Such a parameter must be explicit, or implicit with a unique name, to be used by field notation
-/
#guard_msgs in
private def Bool.testError2 (n : Nat) : Nat :=
  (true).testError2
