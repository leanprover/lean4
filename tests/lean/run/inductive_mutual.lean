/-!
# Tests of `mutual` for inductive types (both with `inductive` and `structure`)
-/


/-!
Mutual inductive types
-/
mutual
inductive I1 (α : Type _) where
  | nil1
  | cons1 (x : α) (xs : I2 α)
inductive I2 (α : Type _) where
  | cons2 (x : α) (xs : I1 α)
end
/--
info: inductive I1.{u_1} : Type u_1 → Type u_1
number of parameters: 1
constructors:
I1.nil1 : {α : Type u_1} → I1 α
I1.cons1 : {α : Type u_1} → α → I2 α → I1 α
-/
#guard_msgs in #print I1
/--
info: inductive I2.{u_1} : Type u_1 → Type u_1
number of parameters: 1
constructors:
I2.cons2 : {α : Type u_1} → α → I1 α → I2 α
-/
#guard_msgs in #print I2


/-!
Mutual nested inductive types
-/
mutual
inductive N1 where
  | mk (xs : List N2)
inductive N2 where
  | mk (ys : List N1)
end

/--
info: inductive N1 : Type
number of parameters: 0
constructors:
N1.mk : List N2 → N1
-/
#guard_msgs in #print N1
/--
info: inductive N2 : Type
number of parameters: 0
constructors:
N2.mk : List N1 → N2
-/
#guard_msgs in #print N2
/-- info: N1.mk [N2.mk [N1.mk []]] : N1 -/
#guard_msgs in #check N1.mk [N2.mk [N1.mk []]]


/-!
Mutual with `structure` and with `variable`
-/
variable (α : Type _)
mutual
structure S1 (β : Type _) where
  x : α
  ys : Nat → I3 β
inductive I3 (β : Type _) where
  | s : S1 β → I3 β
end
/--
info: structure S1.{u_1, u_2} (α : Type u_1) (β : Type u_2) : Type u_1
number of parameters: 2
fields:
  S1.x : α
  S1.ys : Nat → I3 α β
constructor:
  S1.mk.{u_1, u_2} {α : Type u_1} {β : Type u_2} (x : α) (ys : Nat → I3 α β) : S1 α β
-/
#guard_msgs in #print S1
/--
info: inductive I3.{u_1, u_2} : Type u_1 → Type u_2 → Type u_1
number of parameters: 2
constructors:
I3.s : {α : Type u_1} → {β : Type u_2} → S1 α β → I3 α β
-/
#guard_msgs in #print I3

/-!
Mutual `structure`s
-/
mutual
structure S2 where
  xs : List S3
structure S3 where
  ys : List S2
  zs : List S3
end
/--
info: structure S2 : Type
number of parameters: 0
fields:
  S2.xs : List S3
constructor:
  S2.mk (xs : List S3) : S2
-/
#guard_msgs in #print S2
/--
info: structure S3 : Type
number of parameters: 0
fields:
  S3.ys : List S2
  S3.zs : List S3
constructor:
  S3.mk (ys : List S2) (zs : List S3) : S3
-/
#guard_msgs in #print S3

/-!
Regression test: make sure `structure` with an explicit resultant type doesn't erroneously reject the type.
(Fixed by https://github.com/leanprover/lean4/pull/2689)
-/
structure SR1 (α : Type u) (Hom : α → α → Sort v) : Type (max u v) where
  id : (X : α) → Hom X X
