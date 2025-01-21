import Lean

set_option compiler.enableNew true

/--
info: [Compiler.result] size: 1
    def f x : Nat :=
      let _x.1 := Nat.add x x;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
opaque f : Nat → Nat :=
  fun x => Nat.add x x

/--
info: [Compiler.result] size: 0
    def g a._@.opaqueNewCodeGen._hyg.1 a._@.opaqueNewCodeGen._hyg.2 : Nat :=
      extern
-/
#guard_msgs in
set_option trace.Compiler.result true in
@[extern "lean_nat_gcd"]
opaque g : Nat → Nat → Nat
