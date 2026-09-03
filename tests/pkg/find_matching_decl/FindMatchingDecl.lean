import FindMatchingDecl.Linter

/-! Declarations of various shapes for `Linter.findMatchingDecl?` to match: plain definitions,
an inductive, a mutual block whose definitions are compiled via `partial_fixpoint`, a class,
and an anonymous instance. -/

def a := 1
def b := 2
def c := 3

inductive Foo where
  | mk : Foo

mutual
  def hello2 : Option Nat := hello1
    partial_fixpoint

  def hello1 : Option Nat := hello2
    partial_fixpoint
end

class Magma (carrier : Type u) where
  op : carrier → carrier → carrier

instance : Magma Nat where
  op := (· + ·)
