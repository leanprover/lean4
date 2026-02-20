

namespace Foo

initialize ref : IO.Ref Nat ← IO.mkRef 10

initialize vals : IO.Ref (Array String) ← IO.mkRef #[]

def registerVal (s : String) : IO Unit := do
if (← vals.get).contains s then
  throw $ IO.userError "value already registered"
vals.modify (·.push s)

initialize
  IO.println "started the program"
  ref.modify (· + 20)
  registerVal "hello"

initialize
  registerVal "world"

initialize
  registerVal "foo"

end Foo
open Foo

def main : IO Unit := do
IO.println "hello world"
IO.println (← ref.get)
IO.println (← vals.get)
