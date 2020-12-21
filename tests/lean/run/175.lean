import Lean


namespace Foo
open Lean.Elab.Term

syntax (name := fooKind) "foo!" term : term

@[termElab fooKind] def elabFoo : TermElab :=
fun stx expectedType? => elabTerm (stx.getArg 1) expectedType?

#check foo! 10

end Foo

namespace Lean
namespace Elab
namespace Tactic
open Meta

@[builtinTactic clear] def myEvalClear : Tactic := -- this fails in the old-frontend because it eagerly resolves `clear` as `Lean.Meta.clear`.
fun _ => pure ()

end Tactic
end Elab
end Lean
