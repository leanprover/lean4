class foo (F : Type) where
  foo : F

class foobar (F : outParam Type) [foo F] where
  bar : F

class C (α : Type) where
  val : α

class D (α : Type) (β : outParam Type) [C β] where
  val1 : α
  val2 : β := C.val

instance : C String where
  val := "hello"

instance : C Nat where
  val := 42

instance : D Nat String where
  val1 := 37

def f (α : Type) {β : Type} {_ : C β} [D α β] : α × β :=
  (D.val1, D.val2 α)

example : f Nat = (37, "hello") := rfl
