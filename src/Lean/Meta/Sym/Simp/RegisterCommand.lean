/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.Attr
public import Lean.Meta.Sym.Simp.Variant
public meta import Init.Data.ToString.Name
public meta import Init.Data.String.Extra
public section
namespace Lean.Meta.Sym.Simp

macro (name := _root_.Lean.Parser.Command.registerSymSimpAttr) doc:(docComment)?
  "register_sym_simp_attr" id:ident : command => do
  let str := id.getId.toString
  let idParser := mkIdentFrom id (`Parser.Attr ++ id.getId)
  let descr := quote ((doc.map (·.getDocString) |>.getD s!"Sym.simp set for {id.getId.toString}").removeLeadingSpaces)
  `($[$doc:docComment]? public meta initialize ext : SymSimpExtension ← registerSymSimpAttr $(quote id.getId) $descr
    $[$doc:docComment]? syntax (name := $idParser:ident) $(quote str):str : attr)

end Lean.Meta.Sym.Simp
