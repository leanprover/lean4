import ModLinter.Def

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
