module

import Module.Basic

/-! `private import` should allow only private access to imported decls. -/

public def g : Nat := f

/--
error: Unknown identifier `f`

Note: A private declaration `f` exists but is not accessible in the current context.
-/
#guard_msgs in
set_option autoImplicit false in
public theorem t2 : f = 1 := sorry

/--
error: Unknown identifier `f`

Note: A private declaration `f` exists but is not accessible in the current context.
-/
#guard_msgs in
@[expose] public def pexp : True := f

/-! Private references should not be allowed to escape via the inferred type. -/

/-- error: Type must be specified explicitly for public definition `inferredType` -/
#guard_msgs in
public def inferredType := Eq.refl f
