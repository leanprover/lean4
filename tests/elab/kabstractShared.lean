import Lean
/-!
Tests that `kabstract` does not revisit shared subterms without matches, and that occurrence numbering
is preserved when a matching subterm is shared.
-/
open Lean Meta

opaque g : Nat → Nat → Nat

/-- `g (g x x) (g x x)` nested `n` times, with maximal sharing. -/
def mkShared (x : Expr) : Nat → Expr
  | 0 => x
  | n+1 => let e := mkShared x n; mkApp2 (mkConst ``g) e e

-- 2^64 occurrences of `g _ _`, but only 64 distinct subterms.
run_meta withLocalDeclD `x (mkConst ``Nat) fun x => do
  let p := mkApp2 (mkConst ``g) (mkNatLit 1) (mkNatLit 2)
  let r ← kabstract (mkShared x 64) p
  assert! !r.hasLooseBVars

/--
info: g (g x x) #0
---
info: g #0 (g x x)
---
info: g #0 #0
---
info: g (g x x) (g x x)
-/
#guard_msgs in
run_meta withLocalDeclD `x (mkConst ``Nat) fun x => do
  let e := mkShared x 2
  let p := mkShared x 1
  for occs in [.pos [2], .pos [1], .all, .pos [3]] do
    logInfo m!"{← kabstract e p occs}"

-- Matches that are not abstracted still count, also inside shared subterms.
/--
info: g (g (g x x) (g x x)) (g #0 (g x x))
-/
#guard_msgs in
run_meta withLocalDeclD `x (mkConst ``Nat) fun x => do
  logInfo m!"{← kabstract (mkShared x 3) (mkShared x 1) (.pos [3])}"
