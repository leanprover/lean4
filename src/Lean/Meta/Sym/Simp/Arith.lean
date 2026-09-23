/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.Arith.Norm
public section
namespace Lean.Meta.Sym.Simp

/--
Normalizes ring and semiring terms into polynomial normal form (`Sym.Arith.normalize?`),
simplifying the atoms with `simp`. Intended as a `pre` simproc: it sees the maximal
arithmetic subtree first and reifies it once. The result is final (`done := true`), so
`post` does not run on normal forms, and the normal form is cached so that reaching it again
costs a lookup.
-/
def simpArith : Simproc := fun e => do
  let r ← Arith.normalize? e simp
  if let .step e' _ true cd := r then
    discard <| cacheResult e' (mkRflResult (done := true) (contextDependent := cd))
  return r

end Lean.Meta.Sym.Simp
