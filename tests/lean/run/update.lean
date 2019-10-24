import Init.Lean.Expr
open Lean

def main : IO Unit :=
do let f   := Expr.const `f [];
   let x   := Expr.const `x [];
   let y   := Expr.const `y [];
   let t1  := Expr.app f x;
   let t2  := t1.updateApp! f y;
   let t3  := t1.updateApp! f x;
   let t4  := Expr.proj `Prod 1 x;
   let t5  := t4.updateProj! y;
   let t6  := t4.updateProj! x;
   let x₁  := x.updateConst! [Level.one];
   let x₂  := x.updateConst! [];
   let s   := Expr.sort Level.one;
   let s₁  := s.updateSort! Level.one;
   let s₂  := s.updateSort! Level.zero;
   let a   := Expr.forallE `x BinderInfo.default s s;
   let a₁  := a.updateForall! BinderInfo.default s s;
   let a₂  := a.updateForall! BinderInfo.default s₂ s;
   let nat := Expr.const `Nat [];
   let id  := Expr.lam `x BinderInfo.default nat (Expr.bvar 0);
   let id₁ := id.updateLambda! BinderInfo.default s (Expr.bvar 0);
   let id₂ := id.updateLambda! BinderInfo.default nat (Expr.bvar 0);
   let l   := Expr.letE `z nat x t1;
   let l₁  := l.updateLet! nat x t2;
   let l₂  := l.updateLet! nat x t1;
   IO.println [t1, t2, t3, t5, t6, x₁, x₂, s₁, s₂, a₁, a₂, id₁, id₂, l₁, l₂];
   pure ()

#eval main
