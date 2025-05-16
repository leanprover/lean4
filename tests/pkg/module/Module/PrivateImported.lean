module

private import Module.Basic

/-! `private import` should allow only private access to imported decls. -/

def g := f

/-- error: unknown identifier 'f' -/
#guard_msgs in
set_option autoImplicit false in
theorem t2 : f = 1 := sorry

/-- error: unknown identifier 'f' -/
#guard_msgs in
@[expose] def h : True := f
