/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Init.Control
import Init.LeanInit
import Init.Lean.Syntax

namespace Lean
/- Remark: `MonadQuotation` class is part of the `Init` package and loaded by default since it is used in the builtin command `macro`. -/

/-- Simplistic MonadQuotation that does not guarantee globally fresh names, that
    is, between different runs of this or other MonadQuotation implementations.
    It is only safe if the syntax quotations do not introduce bindings around
    antiquotations, and if references to globals are prefixed with `_root_.`
    (which is not allowed to refer to a local variable).

    `Unhygienic` can also be seen as a model implementation of `MonadQuotation`
    (since it is completely hygienic as long as it is "run" only once and can
    assume that there are no other implentations in use, as is the case for the
    elaboration monads that carry their macro scope state through the entire
    processing of a file). It uses the state monad to query and allocate the
    next macro scope, and uses the reader monad to store the stack of scopes
    corresponding to `withFreshMacroScope` calls. -/
abbrev Unhygienic := ReaderT MacroScope $ StateM MacroScope
namespace Unhygienic
instance MonadQuotation : MonadQuotation Unhygienic := {
  getCurrMacroScope   := read,
  getMainModule       := pure `UnhygienicMain,
  withFreshMacroScope := fun α x => do
    fresh ← modifyGet (fun n => (n, n + 1));
    adaptReader (fun _ => fresh) x
}
protected def run {α : Type} (x : Unhygienic α) : α := run x 0 1
end Unhygienic

instance monadQuotationTrans {m n : Type → Type} [MonadQuotation m] [HasMonadLift m n] [MonadFunctorT m m n n] : MonadQuotation n :=
{ getCurrMacroScope   := liftM (getCurrMacroScope : m MacroScope),
  getMainModule       := liftM (getMainModule : m Name),
  withFreshMacroScope := fun α => monadMap (fun α => (withFreshMacroScope : m α → m α)) }

end Lean
