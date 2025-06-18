prelude
import Init.Data.Range.Polymorphic.Nat
import Init.Data.Range.Polymorphic.Basic
import Init.System.IO
import Init.Data.Iterators
import Std.Data.Iterators

def ex1 : IO Unit := do
IO.println "example 1"
for x in [:100:10] do
  IO.println s!"x: {x}"

/--
info: example 1
x: 0
x: 10
x: 20
x: 30
x: 40
x: 50
x: 60
x: 70
x: 80
x: 90
-/
#guard_msgs in
#eval ex1

def ex2 : IO Unit := do
IO.println "example 2"
for x in [:10] do
  IO.println s!"x: {x}"

/--
info: example 2
x: 0
x: 1
x: 2
x: 3
x: 4
x: 5
x: 6
x: 7
x: 8
x: 9
-/
#guard_msgs in
#eval ex2

def ex3 : IO Unit := do
IO.println "example 3"
for x in [1:10] do
  IO.println s!"x: {x}"

/--
info: example 3
x: 1
x: 2
x: 3
x: 4
x: 5
x: 6
x: 7
x: 8
x: 9
-/
#guard_msgs in
#eval ex3

def ex4 : IO Unit := do
IO.println "example 4"
for x in [1:10:3] do
  IO.println s!"x: {x}"

/--
info: example 4
x: 1
x: 4
x: 7
-/
#guard_msgs in
#eval ex4

-- NEW


open Std.Iterators

-- def it := (⟨⟨some 0⟩⟩ : Iter (α := RangeIterator Nat inferInstance (· < 5)) Nat)

-- set_option trace.compiler.ir true in
-- set_option compiler.small 1000 in
-- def f (it : Iter (α := RangeIterator Nat inferInstance (· < 5)) Nat) : Nat := Id.run do
--   let mut acc := 0
--   for x in it do
--     acc := acc + x
--   return acc

-- #eval! f it

-- #eval! it.toList

#eval "b" ∈ ("a",,"c")

#eval (1 ,,4).iter.toList

#eval (1<,,<4).iter.toList

#eval (2<,,<5).size

#eval (2 ,,5).toList

-- TODO: make 1,,5 work
#eval 1 ∈ (1 ,,5)

-- TODO:
instance [Pure m] : MonadLiftT Id m where
  monadLift := pure

def g : IO Unit := do
  for h : x in ((2 : Nat),,8) do -- ugly: For some reason, we need a type hint here
    IO.println x

#synth ForIn IO (type_of% (2 ,,8)) _ -- Note that we don't need the type hint this time

/-- info: [2, 3, 4, 5, 6, 7, 8] -/
#guard_msgs in
#eval! (2 ,,8).toList
