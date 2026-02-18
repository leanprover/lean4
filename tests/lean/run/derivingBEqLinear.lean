module

set_option deriving.beq.linear_construction_threshold 0

public section

inductive Foo
  | mk1 | mk2 | mk3
  deriving @[expose] BEq

/-- info: instBEqFoo.beq_spec (x✝ y✝ : Foo) : (x✝ == y✝) = (x✝.ctorIdx == y✝.ctorIdx) -/
#guard_msgs in
#check instBEqFoo.beq_spec

namespace Foo
theorem ex1 : (mk1 == mk2) = false :=
  rfl
theorem ex2 : (mk1 == mk1) = true :=
  rfl
theorem ex3 : (mk2 == mk2) = true :=
  rfl
theorem ex4 : (mk3 == mk3) = true :=
  rfl
theorem ex5 : (mk2 == mk3) = false :=
  rfl
end Foo

inductive L (α : Type u) : Type u
  | nil  : L α
  | cons : α → L α → L α
  deriving @[expose] BEq

/--
info: instBEqL.beq_spec.{u_1} {α✝ : Type u_1} [BEq α✝] (x✝ x✝¹ : L α✝) :
  (x✝ == x✝¹) =
    match decEq x✝.ctorIdx x✝¹.ctorIdx with
    | isTrue h =>
      match x✝, x✝¹, h with
      | L.nil, L.nil, ⋯ => true
      | L.cons a a_1, L.cons a' a'_1, ⋯ => a == a' && a_1 == a'_1
    | isFalse h => false
-/
#guard_msgs in #check instBEqL.beq_spec

/-- error: Unknown identifier `instBEqL.beq_spec_2` -/
#guard_msgs in #check instBEqL.beq_spec_2

namespace L
theorem ex1 : (L.cons 10 L.nil == L.cons 20 L.nil) = false := rfl
theorem ex2 : (L.cons 10 L.nil == L.nil) = false := rfl
end L

namespace InNamespace
inductive L' (α : Type u) : Type u
  | nil  : L' α
  | cons : α → L' α → L' α
  deriving @[expose] BEq

end InNamespace
/--
info: @[implicit_reducible, expose] def InNamespace.instBEqL'.{u_1} : {α : Type u_1} → [BEq α] → BEq (InNamespace.L' α)
-/
#guard_msgs in #print sig InNamespace.instBEqL'
/--
info: theorem InNamespace.instBEqL'.beq_spec.{u_1} : ∀ {α : Type u_1} [inst : BEq α] (x x_1 : InNamespace.L' α),
  (x == x_1) =
    match decEq x.ctorIdx x_1.ctorIdx with
    | isTrue h =>
      match x, x_1, h with
      | InNamespace.L'.nil, InNamespace.L'.nil, ⋯ => true
      | InNamespace.L'.cons a a_1, InNamespace.L'.cons a' a'_1, ⋯ => a == a' && a_1 == a'_1
    | isFalse h => false
-/
#guard_msgs in #print sig InNamespace.instBEqL'.beq_spec

inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)
  deriving @[expose] BEq

/--
info: instBEqVec.beq_spec.{u_1} {α✝ : Type u_1} {a✝ : Nat} [BEq α✝] (x✝ x✝¹ : Vec α✝ a✝) :
  (x✝ == x✝¹) =
    match decEq x✝.ctorIdx x✝¹.ctorIdx with
    | isTrue h =>
      match a✝, x✝, x✝¹ with
      | 0, Vec.nil, Vec.nil, ⋯ => true
      | x + 1, Vec.cons a a_1, Vec.cons a' a'_1, ⋯ => a == a' && a_1 == a'_1
    | isFalse h => false
-/
#guard_msgs in
#check instBEqVec.beq_spec

namespace Vec
theorem ex1 : (cons 10 Vec.nil == cons 20 Vec.nil) = false := rfl

theorem ex2 : (cons 10 Vec.nil == cons 10 Vec.nil) = true := rfl

theorem ex3 : (cons 20 (cons 11 Vec.nil) == cons 20 (cons 10 Vec.nil)) = false :=
  rfl

theorem ex4 : (cons 20 (cons 11 Vec.nil) == cons 20 (cons 11 Vec.nil)) = true :=
  rfl
end Vec

inductive Bla (α : Type u) where
  | node : List (Bla α) → Bla α
  | leaf : α → Bla α
  deriving BEq

namespace Bla

#guard node [] != leaf 10
#guard node [leaf 10] == node [leaf 10]
#guard node [leaf 10] != node [leaf 10, leaf 20]

end Bla

mutual
inductive Tree (α : Type u) where
  | node : TreeList α → Tree α
  | leaf : α → Tree α
  deriving BEq

inductive TreeList (α : Type u) where
  | nil : TreeList α
  | cons : Tree α → TreeList α → TreeList α
  deriving BEq
end

def ex1 [BEq α] : BEq (Tree α) :=
  inferInstance

def ex2 [BEq α] : BEq (TreeList α) :=
  inferInstance

/-! Private fields should yield public, no-expose instances. -/

structure PrivField where
  private a : Nat
deriving BEq

/-- info: fun a => instBEqPrivField.beq a a -/
#guard_msgs in
#with_exporting
#reduce fun (a : PrivField) => a == a

private structure PrivStruct where
  a : Nat
deriving BEq

-- Instance and spec should be private
/-- info: @[implicit_reducible] private def instBEqPrivStruct : BEq PrivStruct -/
#guard_msgs in
#print sig instBEqPrivStruct

/-- info: private def instBEqPrivStruct.beq : PrivStruct → PrivStruct → Bool -/
#guard_msgs in
#print sig instBEqPrivStruct.beq
/--
info: private theorem instBEqPrivStruct.beq_spec : ∀ (x x_1 : PrivStruct), (x == x_1) = (x.a == x_1.a)
-/
#guard_msgs in
#print sig instBEqPrivStruct.beq_spec

end

-- Try again without `public section`

public structure PrivField2 where
  private a : Nat
deriving BEq

/-- info: fun a => instBEqPrivField2.beq a a -/
#guard_msgs in
#with_exporting
#reduce fun (a : PrivField2) => a == a
