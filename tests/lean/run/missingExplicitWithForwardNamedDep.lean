class Foo (α : Type) (β : Type)  where
  val : Nat
  a   : α
  b   : β

/-- info: Foo.val (α β : Type) [self : Foo α β] : Nat -/
#guard_msgs in #check Foo.val

def valOf [s : Foo α β] : Nat :=
  s.val

/-- info: 10 -/
#guard_msgs in #eval valOf (s := { val := 10, a := true, b := false : Foo Bool Bool })

def valOf2 (α β : Type) [s : Foo α β] : Nat :=
  s.val

/-- info: valOf2 Bool Bool : Nat -/
#guard_msgs in #check valOf2 (s := { val := 10, a := true, b := false : Foo Bool Bool })

def f (x y z : Nat) := x + y + z

/-- info: fun x y => f x y 10 : Nat → Nat → Nat -/
#guard_msgs in
#check f (z := 10)

def g {α : Type} (a b : α) := b
/-- info: fun a => g a 10 : Nat → Nat -/
#guard_msgs in #check g (b := 10)

def h (α : Type) (a b : α) := b
/-- info: fun a => h Bool a true : Bool → Bool -/
#guard_msgs in #check h (b := true)
