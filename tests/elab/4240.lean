/-! Check for bug accidentally marking `m` as owned. -/

class MyClass (α : Type u) where

instance : MyClass Nat where

inductive MyOption (α : Type u) where
  | none
  | some (key : α)

namespace MyOption

def isSomeWithInstance [MyClass α] : MyOption α → Bool
  | none => false
  | some _ => true

def isSome : MyOption α → Bool
  | none => false
  | some _ => true

end MyOption

set_option trace.compiler.ir.result true in
def isSomeWithInstanceNat (m : { m : Array (MyOption Nat) // 0 < m.size }) : Bool :=
  (m.1.uget 0 m.2).isSomeWithInstance
