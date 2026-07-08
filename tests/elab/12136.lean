/-!
# Regression test for perm lemma fvar ordering

This test guards against a regression where `simp` incorrectly rejects valid rewrites
for perm lemmas when fvar ids don't maintain declaration order in their `Name.lt` comparison.

The issue was introduced when `NameGenerator.mkChild` started being used for async elaboration,
creating fvar names like `_uniq.102.2` that compare smaller than `_uniq.7` under `Name.lt`,
even though they were created later.

This breaks the assumption in `acLt` that later-declared fvars compare greater,
causing perm lemmas like `Nat.add_comm` to be incorrectly rejected.

See https://github.com/leanprover/lean4/issues/12136
-/

variable {a : Nat}

theorem permLemmaFvarOrderingTest (b : Nat) (h : a + b = 3) : b + a = 3 := by
  simp [Nat.add_comm, h]
