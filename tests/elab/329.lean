inductive Foo1 (F : {n : Nat} → Type) : Type where
| bar : Foo1 _

/-- info: @Foo1.bar : {F : {n : Nat} → Type} → Foo1 F -/
#guard_msgs in
#check @Foo1.bar

inductive Foo2 (F : {n : Nat} → Type) : Type where
| bar : Foo2 F

/-- info: @Foo2.bar : {F : {n : Nat} → Type} → Foo2 F -/
#guard_msgs in
#check @Foo2.bar

inductive Foo3 (F : {n : Nat} → Type) : Type where
| bar : Foo3 @F

/-- info: @Foo3.bar : {F : {n : Nat} → Type} → Foo3 F -/
#guard_msgs in
#check @Foo3.bar

inductive Bla1 (F : {n : Nat} → Type) : Type where
| mk  : Bla1 _
| bar : Bla1 _ → Bla1 _

/-- info: @Bla1.bar : {F : {n : Nat} → Type} → Bla1 F → Bla1 F -/
#guard_msgs in
#check @Bla1.bar

mutual

inductive Boo1 (F : {n : Nat} → Type) : Type where
| mk  : Boo1 _
| bar : Zoo1 _ → Boo1 F → Boo1 _

inductive Zoo1 (F : {n : Nat} → Type) : Type where
| bar : Boo1 _ → Zoo1 _

end

/-- info: @Boo1.bar : {F : {n : Nat} → Type} → Zoo1 F → Boo1 F → Boo1 F -/
#guard_msgs in
#check @Boo1.bar
