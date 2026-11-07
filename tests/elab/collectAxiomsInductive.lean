module

import Lean
import all Lean.Util.CollectAxioms

/-! Regression tests for #15226: cache all members of an inductive block together,
regardless of which type or constructor is visited first. -/

public section

namespace CollectAxiomsInductive

axiom axA : Nat
axiom axB : Nat

inductive Single where
  | first : Fin axA → Single
  | second : Fin axB → Single

mutual
inductive MutualA where
  | mk : Fin axA → MutualB → MutualA
inductive MutualB where
  | mk : Fin axB → MutualA → MutualB
end

-- Even siblings without references to one another share the block's axiom set.
mutual
inductive SeparateA where
  | mk : Fin axA → SeparateA
inductive SeparateB where
  | mk : Fin axB → SeparateB
end

inductive Nested where
  | mk : Fin axA → List Nested → Nested

inductive Indexed : Fin axB → Type where
  | mk (i : Fin axB) : Indexed i

inductive EmptyIndexed : Fin axA → Type

inductive Pure where
  | leaf
  | node : Pure → Pure

open Lean in
private meta def checkBlock (names expected : Array Name) : CoreM Unit := do
  let env := (← getEnv).setExporting false
  let s := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  for first in names do
    let order := #[first] ++ names
    let actual := CollectAxioms.runM env do
      order.mapM (CollectAxioms.collectAndGet s.find?)
    unless actual.all (· == expected) do
      throwError "collecting {order}: expected {expected} for each member, got {actual}"

run_meta do
  checkBlock #[``Single, ``Single.first, ``Single.second] #[``axA, ``axB]
  checkBlock #[``MutualA, ``MutualA.mk, ``MutualB, ``MutualB.mk] #[``axA, ``axB]
  checkBlock #[``SeparateA, ``SeparateA.mk, ``SeparateB, ``SeparateB.mk] #[``axA, ``axB]
  checkBlock #[``Nested, ``Nested.mk] #[``axA]
  checkBlock #[``Indexed, ``Indexed.mk] #[``axB]
  checkBlock #[``EmptyIndexed] #[``axA]
  checkBlock #[``Pure, ``Pure.leaf, ``Pure.node] #[]

end CollectAxiomsInductive
