import Lean.Expr
open Lean

def main : IO Unit :=
do let f   := mkConst `f [];
   let x   := mkConst `x [];
   let y   := mkConst `y [];
   let t1  := mkApp f x;
   let t2  := t1.updateApp! f y;
   let t3  := t1.updateApp! f x;
   let t4  := mkProj `Prod 1 x;
   let t5  := t4.updateProj! y;
   let t6  := t4.updateProj! x;
   let x₁  := x.updateConst! [levelOne];
   let x₂  := x.updateConst! [];
   let s   := mkSort levelOne;
   let s₁  := s.updateSort! levelOne;
   let s₂  := s.updateSort! levelZero;
   let a   := mkForall `x BinderInfo.default s s;
   let a₁  := a.updateForall! BinderInfo.default s s;
   let a₂  := a.updateForall! BinderInfo.default s₂ s;
   let nat := mkConst `Nat [];
   let id  := mkLambda `x BinderInfo.default nat (mkBVar 0);
   let id₁ := id.updateLambda! BinderInfo.default s (mkBVar 0);
   let id₂ := id.updateLambda! BinderInfo.default nat (mkBVar 0);
   let l   := mkLet `z nat x t1;
   let l₁  := l.updateLetE! nat x t2;
   let l₂  := l.updateLetE! nat x t1;
   IO.println [t1, t2, t3, t5, t6, x₁, x₂, s₁, s₂, a₁, a₂, id₁, id₂, l₁, l₂];
   pure ()

/--
info: [f x, f y, f x, y.2, x.2, x.{1}, x, Type, Prop, Type -> Type, Prop -> Type, fun (x : Type) => x, fun (x : Nat) => x, let z : Nat := x; f y, let z : Nat := x; f x]
-/
#guard_msgs in
#eval main
