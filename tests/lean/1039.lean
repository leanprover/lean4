import Lean.Elab.BuiltinCommand

open Lean.Elab.Command
open Lean

namespace Something

namespace MyNamespace

local elab "end" id:ident : command => do
  println!"foo"
  let node := mkNode ``Lean.Parser.Command.end
    #[Lean.mkAtom "end", mkOptionalNode id]
  elabEnd node

end MyNamespace -- print "foo"

end Something -- nothing

namespace Something

namespace MyNamespace

@[local command_elab Lean.Parser.Command.end] def elabEnd' : CommandElab := fun stx =>
  match stx with
  | `(end $id:ident) => do
    println!"boo"
    let node := mkNode ``Lean.Parser.Command.end
      #[Lean.mkAtom "end", mkOptionalNode id]
    elabEnd node
  | _ => Elab.throwUnsupportedSyntax

end MyNamespace -- print "boo"

end Something -- print nothing as expected

namespace Something'

namespace MyNamespace

local elab_rules : command
| `(end $id:ident) => do
  println!"hello"
  let node := mkNode ``Lean.Parser.Command.end
    #[Lean.mkAtom "end", mkOptionalNode id]
  elabEnd node

end MyNamespace -- print "hello"

end Something' -- print nothing as expected

namespace Something''

namespace MyNamespace

scoped elab_rules : command
| `(end $id:ident) => do
  println!"bla"
  let node := mkNode ``Lean.Parser.Command.end
    #[Lean.mkAtom "end", mkOptionalNode id]
  elabEnd node

end MyNamespace -- print "bla"

end Something'' -- should print nothing

namespace Something''
namespace MyNamespace
end MyNamespace -- print "bla"
end Something'' -- should print nothing
