-- Note: these tests do not work in the current test suite, you have
-- to run them inside a project

variable (a : Nat)
def foo :=
  let a := 1; a
            --^ textDocument/prepareRename
            --^ textDocument/rename: {"newName": "blue"}

structure Foo where
        --^ textDocument/rename: {"newName": "Bar"}
  a : Nat
  deriving Repr

#eval Foo.mk 1

namespace B

structure Foo where
  a : Nat
  b : Nat

def bar (x y : Nat) : Foo :=
  ⟨x, y⟩
    --^ textDocument/rename: {"newName": "z"}

end B

namespace Bar

  structure Foo where
          --^ textDocument/rename: {"newName": "X"}
    a : Nat

  def foobar (f : Foo) : Foo := f

end Bar

def foobar (f : Bar.Foo) : Bar.Foo := f
