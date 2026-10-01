/-!
`Sym.simp` indexes a pattern subterm `?m + ?n` over `Nat` as a wildcard: once the pattern
variables are instantiated it may match a numeral, e.g. `8 + 8 =?= 16`, which the unifier
solves as a postponed offset constraint. Here the width of `(x ++ y).toNat` is `16` while the
left-hand side of `BitVec.toNat_append` has width `m + n`.
-/

example (x y : BitVec 8) : (x ++ y).toNat = x.toNat <<< 8 ||| y.toNat := by
  show @BitVec.toNat 16 (x ++ y) = _
  sym => simp [BitVec.toNat_append]

example (x y : BitVec 8) : (x ++ y).toNat = x.toNat * 2 ^ 8 + y.toNat := by grind
example (x : BitVec 8) (y : BitVec 4) : (x ++ y).toNat = x.toNat * 16 + y.toNat := by grind
example (x y : BitVec 8) : (x ++ y).toNat < 2 ^ 16 := by grind
