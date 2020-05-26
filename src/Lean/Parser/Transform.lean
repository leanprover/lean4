/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Parser

namespace Lean
namespace Syntax

def manyToSepBy (stx : Syntax) (sepTk : String) : Syntax :=
match stx with
| node k args =>
  let args := args.foldlFrom (fun (newArgs : Array Syntax) arg =>
    let prevArg := newArgs.back;
    match prevArg.getTailInfo with
    | some info =>
      let prevArg := prevArg.setTailInfo { trailing := none };
      let newArgs := newArgs.set! (newArgs.size - 1) prevArg;
      let newArgs := newArgs.push (atom info sepTk);
      newArgs.push arg
    | none =>
      let newArgs := newArgs.push (atom {} sepTk);
      newArgs.push arg)
    #[args.get! 0]
    1;
  node k args
| stx => stx

def removeParen (stx : Syntax) : Syntax :=
stx.ifNodeKind `Lean.Parser.Term.paren
  (fun stx =>
    let body := stx.getArg 1;
    if body.getNumArgs != 2 then stx.val
    else if (body.getArg 1).isNone then
      let body := body.getArg 0;
      match stx.getArg 2, body.getTailInfo with
      | atom { trailing := some outer } ")", some bodyInfo@{ trailing := some inner } =>
        let bodyInfoTrail := inner.toString ++ "  ";  -- add whithespaces for removed parentheses
        let bodyInfoTrail := bodyInfoTrail ++ outer.toString; -- add close paren trailing spaces
        body.setTailInfo { bodyInfo with trailing := bodyInfoTrail.toSubstring }
      | _, _ => stx.val
    else stx.val)
  (fun _ => stx)

end Syntax
end Lean
