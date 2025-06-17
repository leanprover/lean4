prelude
import Init.Data.Range.New.RangeIterator
--import Init.Data.Range.New.Nat
import Init.System.IO
import Init.Data.Iterators

open Std.Iterators Types

def it := (⟨⟨some 0⟩⟩ : Iter (α := RangeIterator Nat inferInstance (· < 5)) Nat)

set_option trace.compiler.ir true in
set_option compiler.small 1000 in
def f (it : Iter (α := RangeIterator Nat (some <| · + 1) (· < 5)) Nat) : Nat := Id.run do
  let mut acc := 0
  for x in it do
    acc := acc + x
  return acc

#eval! f it

#eval! it.toList

#eval "b" ∈ ("a",,"c")

#eval "a"

#eval! (1<,,<4).iter.toList

#eval! (2<,,<5).size

-- #eval (,,<5).iter.toList

#eval 1 ∈ (1,,5)

-- TODO:
instance [Pure m] : MonadLiftT Id m where
  monadLift := pure

def f : IO Unit := do
  for h : x in ((2 : Nat),,8) do -- ugly: For some reason, we need a type hint here
    IO.println x

#synth ForIn IO (type_of% (2,,8)) _ -- Note that we don't need the type hint this time

def testArray : Array Nat := #[0, 1, 2, 3, 4, 5, 6]

-- #eval testArray[[2<,,]].iter.toList
