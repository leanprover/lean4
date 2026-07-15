import Lean

/-!
Tests that the free-variable normalization of the type class resolution cache traverses
DAG-shared query types in DAG size, not tree size. `grind` builds heavily shared terms by
substitution (e.g. deeply nested `if`-terms whose tree size is exponential in their DAG size);
an unmemoized traversal exhausts the heartbeat budget or hangs. Synthesizing `Foo t` for a
`Prod` tower `t` of depth 64 (tree size `2^64`, DAG size 65) must complete instantly.
-/

class Foo (α : Type) : Prop where

instance instFoo (α : Type) : Foo α := ⟨⟩

open Lean Meta

run_meta do
  withLocalDeclD `α (mkSort .one) fun α => do
    let mut t := α
    for _ in [0:64] do
      t := mkApp2 (mkConst ``Prod [.zero, .zero]) t t
    discard <| synthInstance (mkApp (mkConst ``Foo) t)
