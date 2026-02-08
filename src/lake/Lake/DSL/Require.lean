/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.DSL.Syntax
import Lake.Config.Dependency

open Lean Parser Command

namespace Lake.DSL

/-! # The `require` syntax

This module contains the expansion of the `require` DSL syntax used to specify package dependencies.
-/

@[inline] private def quoteOptTerm [Monad m] [MonadQuotation m] (term? : Option Term) : m Term :=
  if let some term := term? then withRef term ``(some $term) else ``(none)

def expandDepSpec (stx : TSyntax ``depSpec) (doc? : Option DocComment) : MacroM Command := do
  let `(depSpec| $fullNameStx $[@ $ver?]? $[from $src?]? $[with $opts?]?) := stx
    | Macro.throwErrorAt stx "ill-formed require syntax"
  let src? ← src?.mapM fun src =>
    match src with
    | `(fromSource|git%$tk $url $[@ $rev?]? $[/ $subDir?]?) => withRef tk do
      let rev ← quoteOptTerm rev?
      let subDir ← quoteOptTerm subDir?
      ``(DependencySrc.git $url $rev $subDir)
    | `(fromSource|$path:term) => withRef src do
      ``(DependencySrc.path $path)
    | _ => Macro.throwErrorAt src "ill-formed from syntax"
  let `(depName|$[$scope? /]? $nameStx) := fullNameStx
    | Macro.throwErrorAt fullNameStx "ill-formed name syntax"
  let scope :=
    match scope? with
    | some scope => scope
    | none => Syntax.mkStrLit "" (.fromRef fullNameStx)
  let ver ←
    if let some ver := ver? then withRef ver do
      match ver with
      | `(verSpec|git $ver) => ``(some ("git#" ++ $ver))
      | `(verSpec|$ver:term) => ``(some $ver)
      | _ => Macro.throwErrorAt ver "ill-formed version syntax"
    else
      ``(none)
  let name := expandIdentOrStrAsIdent nameStx
  `($[$doc?:docComment]? @[package_dep] def $name : $(mkCIdent ``Dependency) := {
    name :=  $(quote name.getId),
    scope := $scope,
    version? := $ver,
    src? := $(← quoteOptTerm src?),
    opts := $(opts?.getD <| ← `({})),
  })

@[builtin_macro requireDecl]
def expandRequireDecl : Macro := fun stx => do
  let `(requireDecl|$(doc?)? require%$kw $spec) := stx
    | Macro.throwErrorAt stx "ill-formed require declaration"
  withRef kw do expandDepSpec spec doc?
