/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Init.Meta

namespace Lean

/--
Data for representing `export` commands.
-/
inductive ExportDecl where
  /-- The name `aDeclName` is an alias for the declaration `declName`. -/
  | explicit (aDeclName : Name) (declName : Name)
  /-- The namespace `ans` is an alias for the namespace `ns`,
  except, if `e` is in `except`, `ans ++ e` is not an alias for `ns ++ e`.
  Alias resolution is recursive. `ns` must be a registered namespace. -/
  | namespace (ans ns : Name) (except : List Name)
  deriving BEq

namespace ExportDecl

instance : ToString ExportDecl := ⟨fun decl =>
  match decl with
  | .explicit adecl decl => toString adecl ++ " → " ++ toString decl
  | .namespace ans ns ex  => toString ans ++ ".* → " ++ toString ns ++ ".*" ++ (if ex == [] then "" else " hiding " ++ toString ex)⟩

end ExportDecl

end Lean
