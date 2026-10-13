/-!
Regression test: every builtin instance known to the `grind` canonicalizer must be a fixpoint
of canonicalization. The elaborator uses the builtin `Pow Int Nat` instance for `x ^ 2` even
though a user instance has higher priority, because `instPowNat` is a default instance. The
pattern of `sq4` internalizes that builtin instance as a ground term, which re-synthesizes its
`Pow Int Nat` component. If the component is not builtin, the user instance is picked and the
goal's `x ^ 2` is canonicalized with it, while the `x ^ 2 / 4` atom that cutsat builds when
eliminating `%` is canonicalized with the builtin instance. The ring solver then receives a
term that was never internalized.
-/

instance (priority := high) : Pow Int Nat := ⟨fun x n => x.pow n⟩

axiom sq4 (b : Int) : b ^ 2 % 4 = b % 2

example {x : Int} (hx : x % 2 = 1) : x ^ 2 % 4 = 1 := by grind [sq4]

example {x : Int} (hx : x ^ 2 = 9) : x ^ 2 % 4 = 1 := by grind [sq4]
