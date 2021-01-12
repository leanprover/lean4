import A
import B.Foo

def main : IO Unit :=
  IO.println s!"Hello, {foo} {name}!"
