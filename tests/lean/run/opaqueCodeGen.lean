import Lean

/--
trace: [Compiler.saveMono] size: 1
    def f x : Nat :=
      let _x.1 := Nat.add x x;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
opaque f : Nat → Nat :=
  fun x => Nat.add x x

/--
trace: [Compiler.saveMono] size: 0
    def g a._@._internal._hyg.1 a._@._internal._hyg.2 : Nat :=
      extern
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
@[extern "lean_nat_gcd"]
opaque g : Nat → Nat → Nat
