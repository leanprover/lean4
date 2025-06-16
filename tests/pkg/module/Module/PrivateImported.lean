module

private import Module.Basic

/-! `private import` should allow only private access to imported decls. -/

/--
error: type mismatch
  f
has type
  Nat : Type
but is expected to have type
  True : Prop
-/
#guard_msgs in
theorem g : True := f

/- FIXME: visibility for def bodies is wrong
/-- error: unknown identifier 'f' -/
#guard_msgs in
@[reducible] def h : True := f
-/
