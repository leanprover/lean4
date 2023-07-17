/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.DSL.DeclUtil
import Lake.DSL.Attributes
import Lake.Config.LeanExeConfig
import Lake.Config.LeanLibConfig
import Lake.Config.ExternLibConfig

namespace Lake.DSL
open Lean Parser Command

--------------------------------------------------------------------------------
/-! # Lean Library & Executable Targets -/
--------------------------------------------------------------------------------

/--
Define a new Lean library target for the package.
Can optionally be provided with a configuration of type `LeanLibConfig`.
Has many forms:

```lean
lean_lib «target-name»
lean_lib «target-name» { /- config opts -/ }
lean_lib «target-name» where /- config opts -/
lean_lib «target-name» := /- config -/
```
-/
scoped macro (name := leanLibDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
"lean_lib " sig:structDeclSig : command => do
  let attr ← `(Term.attrInstance| lean_lib)
  let ty := mkCIdentFrom (← getRef) ``LeanLibConfig
  let attrs := #[attr] ++ expandAttrs attrs?
  mkConfigStructDecl none doc? attrs ty sig

/--
Define a new Lean binary executable target for the package.
Can optionally be provided with a configuration of type `LeanExeConfig`.
Has many forms:

```lean
lean_exe «target-name»
lean_exe «target-name» { /- config opts -/ }
lean_exe «target-name» where /- config opts -/
lean_exe «target-name» := /- config -/
```
-/
scoped macro (name := leanExeDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
"lean_exe " sig:structDeclSig : command => do
  let attr ← `(Term.attrInstance| lean_exe)
  let ty := mkCIdentFrom (← getRef) ``LeanExeConfig
  let attrs := #[attr] ++ expandAttrs attrs?
  mkConfigStructDecl none doc? attrs ty sig
