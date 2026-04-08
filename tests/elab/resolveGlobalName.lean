import Lean



def Boo.x := 1
def Foo.x := 2
def Foo.x.y := 3
def Bla.x := 4

namespace Test
export Bla (x)
end Test
open Lean
open Lean.Elab.Term
open Lean.Elab.Command

syntax (name := resolveKind) "#resolve " ident : command

@[command_elab resolveKind] def elabResolve : CommandElab :=
fun stx => liftTermElabM do
  let cs ← resolveGlobalName $ stx.getIdAt 1;
  Lean.logInfo $ toString cs;
  pure ()

#resolve x.y
#resolve x

open Foo
#resolve x
#resolve x.y
#resolve x.z.w

open Boo
#resolve x
#resolve x.y
#resolve x.z.w

open Test
#resolve x
#resolve x.w.h.r
#resolve x.y
