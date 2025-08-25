/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Meta
public import Lean.Data.Name

public section

namespace Lean

/-- Data for representing `open` commands -/
inductive OpenDecl where
  | simple   (ns : Name) (except : List Name)
  | explicit (id : Name) (declName : Name)
  deriving BEq

namespace OpenDecl
instance : Inhabited OpenDecl := ⟨simple Name.anonymous []⟩

instance : ToString OpenDecl := ⟨fun decl =>
  match decl with
  | explicit id decl => toString id ++ " → " ++ toString decl
  | simple ns ex     => toString ns ++ (if ex == [] then "" else " hiding " ++ toString ex)⟩

end OpenDecl

def rootNamespace := `_root_

/--
Checks to see if the name has the `_root_` prefix.
-/
def Name.hasRoot : Name → Bool
  | .anonymous => false
  | .num p _ => p.hasRoot
  | .str .anonymous s => s == "_root_"
  | .str p _ => p.hasRoot

/--
Removes the `_root_` prefix.

`Name.removeRoot n` is a specialized version of `n.replacePrefix rootNamespace Name.anonymous`.
-/
def Name.removeRoot : Name → Name
  | .anonymous => .anonymous
  | .num p i => .num p.removeRoot i
  | .str .anonymous "_root_" => .anonymous
  | .str p s => .str p.removeRoot s

/--
If `n` has the `_root_` prefix, removes it, otherwise returns `none`.
-/
def Name.removeRoot? (n : Name) : Option Name :=
  if n.hasRoot then some n.removeRoot else none

end Lean
