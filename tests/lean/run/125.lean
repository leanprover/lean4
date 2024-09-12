class HasElems (α : Type) : Type := (elems : Array α)
def elems (α : Type) [HasElems α] : Array α := HasElems.elems

inductive Foo : Type
| mk1 : Bool → Foo
| mk2 : Bool → Foo

open Foo

instance BoolElems : HasElems Bool := ⟨#[false, true]⟩
instance FooElems  : HasElems Foo  := ⟨(elems Bool).map mk1 ++ (elems Bool).map mk2⟩

def fooRepr (foo : Foo) :=
  match foo with
  | mk1 b => f!"OH {b}"
  | mk2 b => f!"DR {b}"

instance : Repr Foo := ⟨fun s _ => fooRepr s⟩

/-- info: #[OH false, OH true, DR false, DR true] -/
#guard_msgs in
#eval elems Foo

/-- info: #[OH false, OH true] -/
#guard_msgs in
#eval #[false, true].map Foo.mk1

def Foo.toBool : Foo → Bool
| Foo.mk1 b => b
| Foo.mk2 b => b

/-- info: #[false, true] -/
#guard_msgs in
#eval #[Foo.mk1 false, Foo.mk2 true].map Foo.toBool
