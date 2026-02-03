module

import Module.Basic

/-! `private import` should allow only private access to imported decls. -/

public def g := f

/--
error: Unknown identifier `f`

Note: A public declaration `f` exists but is imported privately; consider adding `public import Module.Basic`.
-/
#guard_msgs in
public theorem t2 : f = 1 := sorry

/--
error: Unknown identifier `f`

Note: A public declaration `f` exists but is imported privately; consider adding `public import Module.Basic`.
-/
#guard_msgs in
@[expose] public def h : True := f

/-! `initialize` should be run even if imported IR-only. -/

public def publicDefOfPrivatelyInitialized := initialized

/-! #12198: `local simp` should be accepted on privately imported theorem -/

attribute [local simp] t
