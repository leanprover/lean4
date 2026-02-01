import Lean

namespace A

structure A (α : Type u) where
  a : α
deriving Lean.ToExpr, Inhabited

-- same namespace for instance and aux decls

/--
info: @[instance_reducible] def A.instToExprA.{u} : {α : Type u} → [Lean.ToExpr α] → [Lean.ToLevel] → Lean.ToExpr (A α) :=
fun {α} [Lean.ToExpr α] [inst_1 : Lean.ToLevel] =>
  { toExpr := instToExprA.toExpr inst_1, toTypeExpr := (Lean.Expr.const `A.A [Lean.toLevel]).app (Lean.toTypeExpr α) }
-/
#guard_msgs in #print A.instToExprA


/--
info: @[instance_reducible] def A.instInhabitedA.{u_1} : {a : Type u_1} → [Inhabited a] → Inhabited (A a) :=
fun {a} [Inhabited a] => { default := instInhabitedA.default }
-/
#guard_msgs in #print A.instInhabitedA

end A

mutual
inductive B (α : Type u) : Type _ where
  | leaf
  | mk (a : C α)
deriving Lean.ToExpr, Inhabited
inductive C (α : Type u) : Type _ where
  | mk (b : B α)
deriving Lean.ToExpr, Inhabited
end

/--
info: @[instance_reducible] def instToExprB.{u} : {α : Type u} → [Lean.ToExpr α] → [Lean.ToLevel] → Lean.ToExpr (B α) :=
fun {α} [Lean.ToExpr α] [inst_1 : Lean.ToLevel] =>
  { toExpr := instToExprB.toExpr_1 inst_1, toTypeExpr := (Lean.Expr.const `B [Lean.toLevel]).app (Lean.toTypeExpr α) }
-/
#guard_msgs in
#print instToExprB
/--
info: @[instance_reducible] def instToExprC.{u} : {α : Type u} → [Lean.ToExpr α] → [Lean.ToLevel] → Lean.ToExpr (C α) :=
fun {α} [Lean.ToExpr α] [inst_1 : Lean.ToLevel] =>
  { toExpr := instToExprB.toExpr_2 inst_1, toTypeExpr := (Lean.Expr.const `C [Lean.toLevel]).app (Lean.toTypeExpr α) }
-/
#guard_msgs in
#print instToExprC


/--
info: @[instance_reducible] def instInhabitedB.{u_1} : {a : Type u_1} → Inhabited (B a) :=
fun {a} => { default := instInhabitedB.default_1 }
-/
#guard_msgs in
#print instInhabitedB

/--
info: @[instance_reducible] def instInhabitedC.{u_1} : {a : Type u_1} → Inhabited (C a) :=
fun {a} => { default := instInhabitedC.default_1 }
-/
#guard_msgs in
#print instInhabitedC
