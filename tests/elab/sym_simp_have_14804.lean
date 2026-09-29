/-!
Regression tests for #14804.

`Sym.Simp.toHave` used to pass the dependencies of a `have` to `Expr.betaRev` in forward
order, but `betaRev` expects them reversed. Any `have` whose value depends on two or more
earlier `have`s of the same telescope was therefore rebuilt with its dependencies swapped.
-/

/-! The arguments of `f` have different types, so swapping them makes the reconstructed
`have` ill-typed and the kernel rejects the proof term. -/

def f (a : Nat) (b : Bool) : Nat := if b then a else 0

example :
    (have a := 1 + 1
     have b := true
     have c := f a b
     c = 2) := by
  sym =>
    simp [f]
    finish

/-! The arguments of `g` have the same type, so swapping them is silent: `c` is rebuilt as
`2 * b + a` and the goal becomes unprovable. -/

def g (a b : Nat) : Nat := 2 * a + b

example :
    (have a := 1 + 1
     have b := 3
     have c := g a b
     c = 7) := by
  sym =>
    simp [g]
    finish
