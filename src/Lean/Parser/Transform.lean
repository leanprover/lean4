/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Basic

namespace Lean
namespace Syntax

def manyToSepBy (stx : Syntax) (sepTk : String) : Syntax := do
  match stx with
  | node k args =>
    if args.size == 0 then
      stx
    else
      let argsNew := #[args[0]]
      for i in [1:args.size] do
        let arg  := args[i]
        let prev := argsNew.back
        match prev.getTailInfo with
        | some info =>
          let prevArg := prev.setTailInfo { trailing := none }
          argsNew := argsNew.set! (argsNew.size - 1) prev
          argsNew := argsNew.push (atom info sepTk)
          argsNew := argsNew.push arg
        | none =>
          argsNew := argsNew.push (atom {} sepTk)
          argsNew := argsNew.push arg
      node k argsNew
  | stx => stx

def removeParen (stx : Syntax) : Syntax :=
  stx.ifNodeKind `Lean.Parser.Term.paren
    (fun stx =>
      let body := stx.getArg 1
      if body.getNumArgs != 2 then stx.val
      else if (body.getArg 1).isNone then
        let body := body.getArg 0
        match stx.getArg 2, body.getTailInfo with
        | atom { trailing := some outer } ")", some bodyInfo@{ trailing := some inner } =>
          let bodyInfoTrail := inner.toString ++ "  "  -- add whithespaces for removed parentheses
          let bodyInfoTrail := bodyInfoTrail ++ outer.toString -- add close paren trailing spaces
          body.setTailInfo { bodyInfo with trailing := bodyInfoTrail.toSubstring }
        | _, _ => stx.val
      else stx.val)
    (fun _ => stx)

end Syntax
end Lean
