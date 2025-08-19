namespace Lean
set_option trace.Elab.Deriving.beq true in
inductive List  where
  | nil : List
  | cons : Nat -> List -> List
  deriving BEq
end Lean
#check _root_.Lean.Lean.List._beq -- right namespace?
def Lean.Lean.boo := 1

namespace Lean
inductive Foo
open Lean (Foo)
