class Foo (α : Type) (β : Type)  where
  val : Nat
  a   : α
  b   : β

#check Foo.val

def valOf [s : Foo α β] : Nat :=
  s.val

#eval valOf (s := { val := 10, a := true, b := false : Foo Bool Bool })

def valOf2 (α β : Type) [s : Foo α β] : Nat :=
  s.val

#check valOf2 (s := { val := 10, a := true, b := false : Foo Bool Bool })
-- valOf2 Bool Bool

def f (x y z : Nat) := x + y + z

#check f (z := 10)
-- fun (x y : Nat) => f x y 10 : Nat → Nat → Nat

def g {α : Type} (a b : α) := b
#check g (b := 10)
-- fun (a : Nat) => g a 10

def h (α : Type) (a b : α) := b
#check h (b := true)
-- fun a => h Bool a true
