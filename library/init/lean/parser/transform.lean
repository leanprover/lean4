/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import init.lean.parser.parser

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
      let newArgs := newArgs.set (newArgs.size - 1) prevArg;
      let newArgs := newArgs.push (atom info sepTk);
      newArgs.push arg
    | none =>
      let newArgs := newArgs.push (atom none sepTk);
      newArgs.push arg)
    (Array.singleton (args.get 0))
    1;
  node k args
| stx => stx

end Syntax
end Lean
