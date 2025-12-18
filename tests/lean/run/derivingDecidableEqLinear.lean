module

set_option deriving.decEq.linear_construction_threshold 0

public section

inductive Foo
  | mk1 | mk2 | mk3
  deriving @[expose] DecidableEq

namespace Foo
theorem ex1 : (mk1 == mk2) = false := rfl
theorem ex2 : (mk1 == mk1) = true := rfl
theorem ex3 : (mk2 == mk2) = true := rfl
theorem ex4 : (mk3 == mk3) = true := rfl
theorem ex5 : (mk2 == mk3) = false := rfl
end Foo

inductive L (α : Type u) : Type u
  | nil  : L α
  | cons : α → L α → L α
  deriving @[expose] DecidableEq

namespace L
theorem ex1 : (L.cons 10 L.nil == L.cons 20 L.nil) = false := rfl
theorem ex2 : (L.cons 10 L.nil == L.nil) = false := rfl
end L

inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)
  deriving @[expose] DecidableEq

namespace Vec
theorem ex1 : (cons 10 Vec.nil == cons 20 Vec.nil) = false := rfl
theorem ex2 : (cons 10 Vec.nil == cons 10 Vec.nil) = true := rfl
theorem ex3 : (cons 20 (cons 11 Vec.nil) == cons 20 (cons 10 Vec.nil)) = false := rfl
theorem ex4 : (cons 20 (cons 11 Vec.nil) == cons 20 (cons 11 Vec.nil)) = true := rfl
end Vec

mutual
inductive Tree (α : Type u) where
  | node : TreeList α → Tree α
  | leaf : α → Tree α
  deriving DecidableEq

inductive TreeList (α : Type u) where
  | nil : TreeList α
  | cons : Tree α → TreeList α → TreeList α
  deriving DecidableEq
end

def ex1 [DecidableEq α] : DecidableEq (Tree α) :=
  inferInstance

def ex2 [DecidableEq α] : DecidableEq (TreeList α) :=
  inferInstance


inductive Tyₛ : Type (u+1)
| SPi : (T : Type u) -> (T -> Tyₛ) -> Tyₛ

/--
error: Dependent elimination failed: Failed to solve equation
  A✝ arg✝ = A arg
-/
#guard_msgs in
inductive Tmₛ.{u} :  Tyₛ.{u} -> Type (u+1)
| app : Tmₛ (.SPi T A) -> (arg : T) -> Tmₛ (A arg)
deriving DecidableEq


/-! Private fields should yield public, no-expose instances. -/

structure PrivField where
  private a : Nat
deriving DecidableEq

/-- info: fun a => instDecidableEqPrivField.decEq a a -/
#guard_msgs in
#with_exporting
#reduce fun (a : PrivField) => decEq a a

private structure PrivStruct where
  a : Nat
deriving DecidableEq

end

-- Try again without `public section`

public structure PrivField2 where
  private a : Nat
deriving DecidableEq

/-- info: fun a => instDecidableEqPrivField2.decEq a a -/
#guard_msgs in
#with_exporting
#reduce fun (a : PrivField2) => decEq a a
