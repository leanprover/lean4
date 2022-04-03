inductive Bla : Type u where
  | nil  : Bla
  | cons : (α : Type u) → (a : α) → Bla → Bla -- Error

inductive Foo : Type where
  | leaf
  | mk (α : Type) (a : α) -- Error
  | mk₂

inductive Foo' : Type u where
  | leaf
  | mk : Sort (max u v) → a → Foo' -- Error
  | mk₂

inductive Boo : Type u where
  | nil  : Boo
  | cons : (α : Sort u) → (a : α) → Boo → Boo

namespace Ex1
inductive Member : α → List α → Type u
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

#check @Member.head
end Ex1

namespace Ex2
inductive Member : α → List α → Type
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)
end Ex2

namespace Ex3
inductive Member : α → List α → Type (max u v)
  | head : Member a (a::as) -- Error
  | tail : Member a bs → Member a (b::bs)
end Ex3

namespace Ex4
inductive Member : α → List α → Type (u+1)
  | head : Member a (a::as) -- Error
  | tail : Member a bs → Member a (b::bs)
end Ex4

namespace Ex5
inductive Member : α → List α → Type 1
  | head : Member a (a::as) -- Error
  | tail : Member a bs → Member a (b::bs)
end Ex5
