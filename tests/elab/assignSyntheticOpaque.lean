
import Lean
/-! Ensures `withAssignableSyntheticOpaque` works, including when encountering trying to assign synthetic opaque metavariables in a different lctx to the one they were first constructed in.-/

open Lean Meta Elab Command


theorem foo (x : Nat) (_h : x = x) : True := .intro

elab "#test_natural" : command => liftTermElabM do
  let e ← withLocalDeclD `x (mkConst `Nat) fun x => do
    let mvar ← mkFreshExprMVar none .natural
    --fun x => foo x (Eq.refl ?m)
    mkLambdaFVars #[x] (mkApp2 (mkConst `foo) x (mkApp2 (mkConst `Eq.refl [1]) (mkConst `Nat) mvar))
  check e

elab "#test_opaque_works" : command => liftTermElabM do
  withLocalDeclD `x (mkConst `Nat) fun x => do
    let mvar ← mkFreshExprMVar none .syntheticOpaque
    -- foo x (Eq.refl ?m)
    let e := mkApp2 (mkConst `foo) x (mkApp2 (mkConst `Eq.refl [1]) (mkConst `Nat) mvar)
    -- If the check is done in the same context the synthetic opaque mvar is constructed in, it works
    withAssignableSyntheticOpaque do check e

elab "#test_opaque" : command => liftTermElabM do
  let e ← withLocalDeclD `x (mkConst `Nat) fun x => do
    let mvar ← mkFreshExprMVar none .syntheticOpaque
    --fun x => foo x (Eq.refl ?m)
    mkLambdaFVars #[x] (mkApp2 (mkConst `foo) x (mkApp2 (mkConst `Eq.refl [1]) (mkConst `Nat) mvar))
  -- If done outside of `x`'s scope, this used to fail, the test ensures this case works correctly
  withAssignableSyntheticOpaque do check e

#test_natural --works as expected
#test_opaque_works --works as expected
#test_opaque --used to fail
