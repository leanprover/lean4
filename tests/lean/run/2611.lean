/-!
# Structure copied parents should be able to refer to other parents as instances
Issue: https://github.com/leanprover/lean4/issues/2611
-/

/-!
Example that worked before the fixes for 2611. The projection `D.toC` refers to `D.toA` for the `A` instance.
This is a natural consequence to the way subobject projection functions are added by `mkProjections`.
-/
class A
class C [A]
class D extends A, C

/-!
This example did not work. Since `C` provides a `B` field, it's a copied parent.
Now there is a step where the fvar for the `A` instance is replaced by the `D.toA` constant.
-/
namespace Ex2
class A
class B
class C [A] extends B
class D extends A, B, C
end Ex2

/-!
A test that this still works even when there are parameters on the structure.
-/
namespace Ex3
class A where
  x : Nat
class B [A] where
  x : Nat
class C (α : Type) extends A, B where
  y : α
/-- info: Ex3.C.toB {α : Type} [self : C α] : @B (@C.toA α self) -/
#guard_msgs in set_option pp.explicit true in #check C.toB
end Ex3

/-!
A test that this still works even when there are parameters on the parents.
-/
namespace Ex4
class A (n : Nat) where
  x : Nat
class B (n : Nat) [A n] where
  x : Nat
class C extends A 3, B 3
/--
info: Ex4.C.toB [self : C] : @B (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@C.toA self)
-/
#guard_msgs in set_option pp.explicit true in #check C.toB
end Ex4
