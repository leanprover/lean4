prelude
import Init.Data.Range.New.Nat
import Init.System.IO

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
