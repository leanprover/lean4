

structure Var : Type := (name : String)
instance Var.nameCoe : Coe String Var := ⟨Var.mk⟩

structure A : Type := (u : Unit)
structure B : Type := (u : Unit)

def a : A := A.mk ()
def b : B := B.mk ()

def Foo.chalk : A → List Var → Unit := fun _ _ => ()
def Bar.chalk : B → Unit := fun _ => ()

instance listCoe {α β} [Coe α β] : Coe (List α) (List β) :=
⟨fun as => as.map fun a => coe a⟩

open Foo
open Bar

#check Foo.chalk a ["foo"] -- works

#check chalk a ["foo"] -- works
