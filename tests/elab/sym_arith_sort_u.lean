/-!
`Sym.Arith.classify?` is asked whether the carrier of a relation is a ring or semiring. For a
type in `Sort u`, as in `{α : Sort u}`, `getDecLevel` fails with "invalid universe level, u is
not greater than 0"; the classifier must answer "no structure" instead. Both `sym` with `arith`
and `grind` with the `Sym.simp`-based normalizer failed on these goals.
-/

register_sym_simp arithSimp where
  pre := arith
  post := ground

example {α : Sort u} (f : α → Nat) (a : α) : f a + 0 = f a := by
  sym => simp arithSimp

set_option backward.grind.normalizer false

example {α : Sort u} (a b c : α) (h₁ : a = b) (h₂ : b = c) : a = c := by grind
example {α : Sort u} (f : α → Nat) (a b : α) (h : a = b) : f a ≤ f b := by grind
example {α} (op : α → α → α) [Std.Associative op] (a b c d : α)
   : op a b = c →
     op b a = d →
     op (op c a) (op b c) = op (op a d) (op d b) := by
  grind
