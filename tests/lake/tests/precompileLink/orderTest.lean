-- import a module of lib `Foo`  which does not import `FooDep`
import Foo.Bar
-- then, import a module which does
import Foo.Baz

def main : IO Unit := do
  IO.println (← greetingRef.get)
