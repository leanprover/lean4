inductive Foo1 (F : {n : Nat} → Type) : Type where
| bar : Foo1 _

#check @Foo1.bar

inductive Foo2 (F : {n : Nat} → Type) : Type where
| bar : Foo2 F

#check @Foo2.bar

inductive Foo3 (F : {n : Nat} → Type) : Type where
| bar : Foo3 @F

#check @Foo3.bar

inductive Bla1 (F : {n : Nat} → Type) : Type where
| mk  : Bla1 _
| bar : Bla1 _ → Bla1 _

#check @Bla1.bar

mutual

inductive Boo1 (F : {n : Nat} → Type) : Type where
| mk  : Boo1 _
| bar : Zoo1 _ → Boo1 F → Boo1 _

inductive Zoo1 (F : {n : Nat} → Type) : Type where
| bar : Boo1 _ → Zoo1 _

end

#check @Boo1.bar