/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Meta.Sym.Simp.Attr

/-!
The `@[vcgen_simp]` attribute registers the `Sym.simp` theorems that `vcgen` rewrites hypotheses,
state arguments and verification conditions with.
-/

public section

namespace Lean.Elab.Tactic.VCGen

builtin_initialize vcgenSimpExt : Meta.Sym.Simp.SymSimpExtension ←
  Meta.Sym.Simp.registerSymSimpAttr `vcgen_simp "simp theorems used by vcgen"

end Lean.Elab.Tactic.VCGen
