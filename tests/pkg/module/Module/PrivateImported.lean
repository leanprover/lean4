module

import Module.Basic

/-! `private import` should allow only private access to imported decls. -/

public def g := f

/-- error: unknown identifier 'f' -/
#guard_msgs in
set_option autoImplicit false in
public theorem t2 : f = 1 := sorry

/-- error: unknown identifier 'f' -/
#guard_msgs in
@[expose] public def h : True := f
