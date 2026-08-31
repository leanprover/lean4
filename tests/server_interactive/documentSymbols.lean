def a := 1

namespace Foo

def b := 2

section Foobar

def c := 3

end Foobar

def d := 4

end Foo

def e := 5

namespace Bar

def f := 6
theorem g : True := True.intro
instance : Coe Nat Nat := sorry

--^ textDocument/documentSymbol
