module

/-!
Enum `deriving` in a `meta` section: the derived `ofNat` is added via raw `addAndCompile` without
`markMeta`, so `leanir` checks it as non-`meta` while the enum ctors it references are tagged.
`leanir` must exempt such would-be-local ctor refs like `lean` does for local ones.
-/

public meta section

/-- Test enum. -/
inductive MetaEnum
  /-- Constructor. -/
  | low
  /-- Constructor. -/
  | medium
  deriving Inhabited, DecidableEq, Repr
