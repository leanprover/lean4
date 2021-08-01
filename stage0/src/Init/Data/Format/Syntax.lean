/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.Format.Macro
import Init.Data.Format.Instances
import Init.Meta

namespace Lean.Syntax

open Std
open Std.Format

private def formatInfo (showInfo : Bool) (info : SourceInfo) (f : Format) : Format :=
  match showInfo, info with
  | true, SourceInfo.original lead pos trail endPos => f!"{lead}:{pos}:{f}:{endPos}:{trail}"
  | true, SourceInfo.synthetic pos endPos           => f!"{pos}:{f}:{endPos}"
  | _,    _                                         => f

partial def formatStxAux (maxDepth : Option Nat) (showInfo : Bool) : Nat → Syntax → Format
  | _,     atom info val     => formatInfo showInfo info $ format (repr val)
  | _,     ident info _ val pre => formatInfo showInfo info $ format "`" ++ format val
  | _,     missing           => "<missing>"
  | depth, node kind args    =>
    let depth := depth + 1;
    if kind == nullKind then
      sbracket $
        if args.size > 0 && depth > maxDepth.getD depth then
          ".."
        else
          joinSep (args.toList.map (formatStxAux maxDepth showInfo depth)) line
    else
      let shorterName := kind.replacePrefix `Lean.Parser Name.anonymous;
      let header      := format shorterName;
      let body : List Format :=
        if args.size > 0 && depth > maxDepth.getD depth then [".."] else args.toList.map (formatStxAux maxDepth showInfo depth);
      paren $ joinSep (header :: body) line

def formatStx (stx : Syntax) (maxDepth : Option Nat := none) (showInfo := false) : Format :=
  formatStxAux maxDepth showInfo 0 stx

instance : ToFormat (Syntax) := ⟨formatStx⟩
instance : ToString (Syntax) := ⟨@toString Format _ ∘ format⟩

end Lean.Syntax
