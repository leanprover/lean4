import A
import B
import Foo.Bar
import Foo.Baz

def main : IO Unit :=
  IO.println s!"Hello, {foo} {a} {b}!"
