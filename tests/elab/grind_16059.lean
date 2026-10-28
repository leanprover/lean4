/-!
`mkInjEq` internalized `f⁻¹ (f a)` built with `mkApp`, without hash-consing it (since #10483).
This became a crash in v4.35.0, when #14727 added the `grind hom` layer: when the same term was
built again in another case-split branch, `processNewEq` re-shared it to the copy registered in
the first branch, which this branch's E-graph did not contain. The two copies got separate
`ENode`s, the congruence table linked them, and proof reconstruction panicked in
`mkCongrDefaultProof` (v4.35.0 through v4.36.0-rc2; v4.34.0 is unaffected). `grind.debug`
checks that internalized terms are hash-consed.
-/
set_option grind.debug true

-- regression: injectivity over `if` expressions (closed by grind on v4.34.0, panicked on v4.35.0)
def g (n : Nat) (f : Fin (n + 1) → Fin (n + 1)) (x : Fin n) : Nat :=
  if (f ⟨x, by omega⟩).val < n then (f ⟨x, by omega⟩).val else (f ⟨n, by omega⟩).val
example (n : Nat) (f : Fin (n + 1) → Fin (n + 1)) (h : Function.Injective f) (x y : Fin n)
    (e : g n f x = g n f y) : x = y := by
  grind [g]

-- regression: same injectivity with a `let`-bound function and a dependent `if`
example (n : Nat) (f : Fin (n + 1) → Fin (n + 1)) (h : Function.Injective f) : True := by
  let f' (x : Fin n) : Fin n :=
    let x' : Fin (n + 1) := ⟨x.val, by grind⟩
    let y := f x'
    if isLt : y.val < n then ⟨y.val, isLt⟩ else ⟨f ⟨n, by grind⟩, by grind⟩
  have inj' : Function.Injective f' := by
    intro x y eq
    grind
  trivial
