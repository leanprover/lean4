/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Package
import Lake.DSL.Attributes
import Lake.DSL.DeclUtil

namespace Lake.DSL
open Lean Parser Command

/-- The name given to the definition created by the `package` syntax. -/
def packageDeclName := `_package

/--
Defines the configuration of a Lake package.  Has many forms:

```lean
package «pkg-name»
package «pkg-name» { /- config opts -/ }
package «pkg-name» where /- config opts -/
package «pkg-name» : PackageConfig := /- config -/
```

There can only be one `package` declaration per Lake configuration file.
The defined package configuration will be available for reference as `_package`.
-/
scoped macro (name := packageDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
"package " sig:structDeclSig : command => do
  let attr ← `(Term.attrInstance| «package»)
  let ty := mkCIdentFrom (← getRef) ``PackageConfig
  let attrs := #[attr] ++ expandAttrs attrs?
  mkConfigStructDecl packageDeclName doc? attrs ty sig
