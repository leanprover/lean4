/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Init.Lean.Parser.Parser

namespace Lean
namespace Syntax

def manyToSepBy (stx : Syntax) (sepTk : String) : Syntax :=
match stx with
| node k args =>
  let args := args.foldlFrom (fun (newArgs : Array Syntax) arg =>
    let prevArg := newArgs.back;
    match prevArg.getTailInfo with
    | some info =>
      let prevArg := prevArg.setTailInfo info.truncateTrailing;
      let newArgs := newArgs.set! (newArgs.size - 1) prevArg;
      let newArgs := newArgs.push (atom info sepTk);
      newArgs.push arg
    | none =>
      let newArgs := newArgs.push (atom none sepTk);
      newArgs.push arg)
    (Array.singleton (args.get! 0))
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
      | atom (some info) ")", some bodyInfo =>
        let bodyInfoTrail := bodyInfo.trailing.toString ++ "  ";      -- add whithespaces for removed parentheses
        let bodyInfoTrail := bodyInfoTrail ++ info.trailing.toString; -- add close paren trailing spaces
        body.setTailInfo (some { trailing := bodyInfoTrail.toSubstring, .. bodyInfo })
      | _, _ => stx.val
    else stx.val)
  (fun _ => stx)

end Syntax
end Lean
