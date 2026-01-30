/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
meta import Lean.Meta.Tactic.Grind.Attr
public section
namespace Lean.Meta.Grind

macro (name := _root_.Lean.Parser.Command.registerGrindAttr) doc:(docComment)?
  "register_grind_attr" id:ident : command => do
  let str1 := id.getId.toString
  let idParser1 := mkIdentFrom id (`Lean.Parser.Attr ++ id.getId)
  let str2 := id.getId.toString ++ "!"
  let idParser2 := mkIdentFrom id (`Lean.Parser.Attr ++ (id.getId.appendAfter "!"))
  let str3 := id.getId.toString ++ "?"
  let idParser3 := mkIdentFrom id (`Lean.Parser.Attr ++ (id.getId.appendAfter "?"))
  let str4 := id.getId.toString ++ "!?"
  let idParser4 := mkIdentFrom id (`Lean.Parser.Attr ++ (id.getId.appendAfter "!?"))
  `($[$doc:docComment]? initialize ext : Extension ← registerAttr $(quote id.getId) (ref := $(quote id.getId))
    $[$doc:docComment]? syntax (name := $idParser1:ident) $(quote str1):str (ppSpace Lean.Parser.Attr.grindMod)? : attr
    $[$doc:docComment]? syntax (name := $idParser2:ident) $(quote str2):str (ppSpace Lean.Parser.Attr.grindMod)? : attr
    $[$doc:docComment]? syntax (name := $idParser3:ident) $(quote str3):str (ppSpace Lean.Parser.Attr.grindMod)? : attr
    $[$doc:docComment]? syntax (name := $idParser4:ident) $(quote str4):str (ppSpace Lean.Parser.Attr.grindMod)? : attr
    )

end Lean.Meta.Grind
