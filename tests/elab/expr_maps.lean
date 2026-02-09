import Lean.Expr

open Lean

def exprType : Expr := mkSort levelOne
def biDef           := BinderInfo.default
def exprNat         := mkConst `Nat []
-- Type -> Type
def TypeArrowType   := mkForall `α biDef exprType exprType
-- Type -> Type
def TypeArrowType2  := mkForall `β biDef exprType exprType
-- fun (x : Nat) => x
def exprT1          := mkLambda `x biDef exprNat (mkBVar 0)
-- fun (y : Nat) => x
def exprT2          := mkLambda `y biDef exprNat (mkBVar 0)
-- fun (x : Nat) => (f x)
def exprT3          := mkLambda `x biDef exprNat (mkApp (mkConst `f []) (mkBVar 0))
-- fun (x : Nat) => (f x)
def exprT4          := mkLambda `x BinderInfo.implicit exprNat (mkApp (mkConst `f []) (mkBVar 0))

def check (b : Bool) : IO Unit :=
unless b do throw $ IO.userError "failed"

def tst1 : IO Unit :=
do IO.println TypeArrowType;
   IO.println exprT1;
   IO.println exprT2;
   IO.println exprT3;
   IO.println exprT4;
   check (TypeArrowType == TypeArrowType2);
   check (ExprStructEq.mk TypeArrowType != ExprStructEq.mk TypeArrowType2);
   check (!Expr.equal TypeArrowType TypeArrowType2);
   check (exprT1 == exprT2);
   check (ExprStructEq.mk exprT1 != ExprStructEq.mk exprT2);
   check (ExprStructEq.mk exprT1 == ExprStructEq.mk exprT1);
   check (exprT3 == exprT4);
   check (ExprStructEq.mk exprT3 != ExprStructEq.mk exprT4);
   pure ()

/--
info: Type -> Type
fun (x : Nat) => x
fun (y : Nat) => y
fun (x : Nat) => f x
fun {x : Nat} => f x
-/
#guard_msgs in
#eval tst1

def tst2 : IO Unit :=
do let m1 : ExprMap Nat := {};
   let m1 := m1.insert exprT1 10;
   check (m1[exprT1]? == some 10);
   check (m1[exprT2]? == some 10);
   check (m1[exprT3]? == none);
   let m1 := m1.insert exprT4 20;
   check (m1[exprT1]? == some 10);
   check (m1[exprT3]? == some 20);
   IO.println m1[exprT1]?;
   pure ()

/-- info: (some 10) -/
#guard_msgs in
#eval tst2

def tst3 : IO Unit :=
do let m1 : ExprStructMap Nat := {};
   let m1 := m1.insert exprT1 10;
   check (m1.get? exprT1 == some 10);
   check (m1.get? exprT2 == none);
   check (m1.get? exprT3 == none);
   let m1 := m1.insert exprT4 20;
   check (m1.get? exprT1 == some 10);
   check (m1.get? exprT4 == some 20);
   check (m1.get? exprT3 == none);
   IO.println (m1.get? exprT1);
   pure ()

/-- info: (some 10) -/
#guard_msgs in
#eval tst3

def tst4 : IO Unit :=
do let m1 : PersistentExprMap Nat := {};
   let m1 := m1.insert exprT1 10;
   check (m1.find? exprT1 == some 10);
   check (m1.find? exprT2 == some 10);
   check (m1.find? exprT3 == none);
   let m1 := m1.insert exprT4 20;
   check (m1.find? exprT1 == some 10);
   check (m1.find? exprT3 == some 20);
   IO.println (m1.find? exprT1);
   pure ()

/-- info: (some 10) -/
#guard_msgs in
#eval tst4

def tst5 : IO Unit :=
do let m1 : PersistentExprStructMap Nat := {};
   let m1 := m1.insert exprT1 10;
   check (m1.find? exprT1 == some 10);
   check (m1.find? exprT2 == none);
   check (m1.find? exprT3 == none);
   let m1 := m1.insert exprT4 20;
   check (m1.find? exprT1 == some 10);
   check (m1.find? exprT4 == some 20);
   check (m1.find? exprT3 == none);
   IO.println (m1.find? exprT1);
   pure ()

/-- info: (some 10) -/
#guard_msgs in
#eval tst5
