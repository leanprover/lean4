/-!
# Verify that `below` lemmas work in cases where they may need to δ-reduce things
Fixes issue #2990
-/

def Foo (F : α -> Prop) : Prop :=
  ∀ x , F x

inductive Bad : Nat -> Prop :=
  | bar e : Foo (fun _ => Bad e) -> Bad e
