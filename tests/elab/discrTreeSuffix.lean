import Lean
import Lean.Meta.Sym

/-!
Lookups in discrimination trees whose paths end in suffix leaves (`DiscrTree.Trie.suffix`), which
`getMatch`, `getMatchWithExtra`, `getUnify` and `Sym.getMatch` traverse without unfolding them.
-/

open Lean Meta DiscrTree

opaque f : Nat → Nat → Nat
opaque g : Nat → Nat
opaque a : Nat
opaque b : Nat
opaque Q : Nat → Prop

/-- The number of suffix leaves in `d`. -/
partial def numSuffixes (d : DiscrTree α) : Nat :=
  d.root.toList.foldl (fun n (_, t) => go n t) 0
where
  go (n : Nat) : Trie α → Nat
    | .suffix .. => n + 1
    | .chain _ c => go n c
    | .node _ cs => cs.foldl (fun n (_, c) => go n c) n
    | .lazy t => go n t.get

def fE (x y : Expr) : Expr := mkApp2 (mkConst ``f) x y
def gE (x : Expr) : Expr := mkApp (mkConst ``g) x
def aE : Expr := mkConst ``a
def bE : Expr := mkConst ``b

/--
The patterns, as values with their names. They share the prefix `f` and branch on its first
argument, so each ends in a suffix starting after a branch; the suffix of `f a (g ?z)` is `g, *`.
-/
def patterns : MetaM (Array (String × Expr)) := do
  let x ← mkFreshExprMVar (mkConst ``Nat)
  let y ← mkFreshExprMVar (mkConst ``Nat)
  let z ← mkFreshExprMVar (mkConst ``Nat)
  return #[("f ?x (g a)", fE x (gE aE)), ("f b (g b)", fE bE (gE bE)),
    ("f (g b) (g a)", fE (gE bE) (gE aE)), ("f (g ?y) b", fE (gE y) bE),
    ("f a (g ?z)", fE aE (gE z))]

def tree : MetaM (DiscrTree String) := do
  let mut d := {}
  for (n, p) in ← patterns do
    d ← d.insert p n
  return d

/-- info: suffix leaves: 5 -/
#guard_msgs in
#eval show MetaM Unit from do
  logInfo m!"suffix leaves: {numSuffixes (← tree)}"

/--
info: f b (g a): [f ?x (g a)]
---
info: f (g b) (g a): [f (g b) (g a), f ?x (g a)]
---
info: f (g a) b: [f (g ?y) b]
---
info: f b (g b): [f b (g b)]
---
info: f b b: []
---
info: f a (g b): [f a (g ?z)]
---
info: f a (g (g b)): [f a (g ?z)]
---
info: f a b: []
-/
#guard_msgs in
#eval show MetaM Unit from do
  let d ← tree
  for q in [fE bE (gE aE), fE (gE bE) (gE aE), fE (gE aE) bE, fE bE (gE bE), fE bE bE,
      fE aE (gE bE), fE aE (gE (gE bE)), fE aE bE] do
    logInfo m!"{q}: {(← d.getMatch q).qsort (· < ·)}"

-- A metavariable in the query unifies with whole subterms of the patterns, including subterms with
-- arguments (`g b`) inside a suffix.
/--
info: f ?m (g a): [f (g b) (g a), f ?x (g a), f a (g ?z)]
---
info: f b ?m: [f ?x (g a), f b (g b)]
---
info: f ?m b: [f (g ?y) b]
---
info: f ?m ?m: [f (g ?y) b, f (g b) (g a), f ?x (g a), f a (g ?z), f b (g b)]
---
info: f (g ?m) ?m: [f (g ?y) b, f (g b) (g a), f ?x (g a)]
-/
#guard_msgs in
#eval show MetaM Unit from do
  let d ← tree
  let m ← mkFreshExprMVar (mkConst ``Nat) (userName := `m)
  for q in [fE m (gE aE), fE bE m, fE m bE, fE m m, fE (gE m) m] do
    logInfo m!"{q}: {(← d.getUnify q).qsort (· < ·)}"

-- `getMatchWithExtra` matches a partial application ending in a suffix, with extra arguments.
/--
info: f b (g a): [(f ?x, 1), (f ?x (g a), 0), (f b, 1), (f b (g a), 0)]
---
info: f a (g a): [(f ?x, 1), (f ?x (g a), 0)]
-/
#guard_msgs in
#eval show MetaM Unit from do
  let x ← mkFreshExprMVar (mkConst ``Nat)
  let mut d : DiscrTree String := {}
  for (n, p) in #[("f ?x (g a)", fE x (gE aE)), ("f b (g a)", fE bE (gE aE)),
      ("f ?x", mkApp (mkConst ``f) x), ("f b", mkApp (mkConst ``f) bE)] do
    d ← d.insert p n
  unless numSuffixes d > 0 do throwError "no suffix leaves"
  for q in [fE bE (gE aE), fE aE (gE aE)] do
    logInfo m!"{q}: {(← d.getMatchWithExtra q).qsort (fun x y => x.1 < y.1)}"

/-! The same patterns in `Sym.getMatch`, whose suffix loop is separate. -/

axiom p₁ : ∀ x, Q (f x (g a))
axiom p₂ : Q (f b (g b))
axiom p₃ : Q (f (g b) (g a))
axiom p₄ : ∀ y, Q (f (g y) b)
axiom p₅ : ∀ z, Q (f a (g z))

/--
info: suffix leaves: 5
---
info: Q (f b (g a)): [p₁]
---
info: Q (f (g b) (g a)): [p₁, p₃]
---
info: Q (f (g a) b): [p₄]
---
info: Q (f b (g b)): [p₂]
---
info: Q (f b b): []
---
info: Q (f a (g (g b))): [p₅]
---
info: Q (f a b): []
-/
#guard_msgs in
#eval show MetaM Unit from do
  let mut d : DiscrTree Name := {}
  for n in [``p₁, ``p₂, ``p₃, ``p₄, ``p₅] do
    d := Sym.insertPattern d (← Sym.mkPatternFromDecl n) n
  logInfo m!"suffix leaves: {numSuffixes d}"
  for q in [fE bE (gE aE), fE (gE bE) (gE aE), fE (gE aE) bE, fE bE (gE bE), fE bE bE,
      fE aE (gE (gE bE)), fE aE bE] do
    let q := mkApp (mkConst ``Q) q
    logInfo m!"{q}: {(Sym.getMatch (← getMCtx) d q).qsort Name.lt}"
