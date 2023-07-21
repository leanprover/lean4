/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.Name

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

def removeRoot (n : Name) : Name :=
  n.replacePrefix rootNamespace Name.anonymous

/-- `addNamespaceUnlessRoot ns n` adds namespace `ns` prefix unless `n` has a `_root_` prefix.
If `n` has a `_root_` prefix then it is removed and `ns` is not added. The end result is a fully
qualified name assuming that `ns` is a fully qualified namespace prefix.
```
addNamespaceUnlessRoot `a.b `c.d = `a.b.c.d
addNamespaceUnlessRoot `a.b `_root_.c.d = `c.d
```
-/
def addNamespaceUnlessRoot (ns n : Name) : Name :=
  if rootNamespace.isPrefixOf n then removeRoot n else ns ++ n

end Lean
