module

inductive Foo (α : Type u) (β : Type v) where
  | mk₁ : α → Foo α β
  | mk₂ : List β → Foo α β

deriving instance Inhabited for Foo

def ex1 : Inhabited (Foo α β) :=
  inferInstance

inductive Bla (α : Type u) (β : Type v) where
  | mk₁ : α → Bla α β
  | mk₂ : β → Bla α β

deriving instance Inhabited for Bla

def ex2 [Inhabited α] : Inhabited (Foo α β) :=
  inferInstance

structure Point (α : Type) where
  x : α
  y : α
  deriving Inhabited

def ex3 [Inhabited α] : Inhabited (Point α) :=
  inferInstance

inductive Lst (α : Type) where
  | nil
  | cons : α → Lst α → Lst α
  deriving Inhabited

def ex4 : Inhabited (Lst α) :=
  inferInstance

mutual

inductive FooLst (α : Type) where
  | nil
  | cons : Boo α → FooLst α → FooLst α
  deriving Inhabited

inductive Boo (α : Type) where
  | node : FooLst α → Boo α
  deriving Inhabited

end

def ex5 : Inhabited (Boo α) :=
  inferInstance

structure A where
deriving Inhabited

/--
info: private def instInhabitedA : Inhabited A :=
{ default := defaultA✝ }
-/
#guard_msgs in
#print instInhabitedA

/-! Public structures with private fields should yield public opaque instances. -/

public structure PrivField where
  private a : Nat
deriving Inhabited

/-- info: defaultPrivField✝ -/
#guard_msgs in
#with_exporting
#reduce (default : PrivField)

/-! ...which should not be compatible with explicit `@[expose]`. -/

/--
error: cannot use `deriving ... @[expose]` with `PrivFieldExp` as it has one or more private constructors
-/
#guard_msgs in
public structure PrivFieldExp where
  private a : Nat
deriving @[expose] Inhabited
