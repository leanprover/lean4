/-
Declare a `Sym.simp` theorem set.
-/
module

public import Lean
public meta import Lean.Meta.Sym.Simp.Attr

register_sym_simp_attr my_sym_simp

public def privTarget (x : Nat) : Nat := x + 1
@[reducible] public def redId (x : Nat) : Nat := x
@[sym_simp, grind norm] private theorem privTarget_eq (x : Nat) : privTarget x = redId x + 1 := rfl
