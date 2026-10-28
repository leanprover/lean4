import Lean.Meta.DiscrTree

/-!
Merging per-module discrimination trees with `DiscrTree.ofModuleRoots` gives the same tree as
inserting all entries in module order: the same structure, the same values in the same order
(including in-place replacement of `==`-equal values), and the same results after further
insertions into the merged tree.
-/

open Lean Meta DiscrTree

/-- Values compare by `id` only, so a later duplicate replaces an earlier one, keeping its position. -/
structure V where
  id : Nat
  tag : Nat
  deriving Repr, Inhabited

instance : BEq V := ⟨fun a b => a.id == b.id⟩
instance : ToFormat V := ⟨fun v => s!"{v.id}/{v.tag}"⟩

def keyPool : Array Key :=
  #[.star, .other, .arrow, .const `f 2, .const `g 1, .const `a 0, .const `b 0, .lit (.natVal 3),
    .proj `S 0 1]

def next (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Pseudo-random entries with key sequences of length 1 to 4 and colliding value ids. -/
def genEntries (seed n : Nat) : Array (Array Key × V) := Id.run do
  let mut s := next seed
  let mut out := #[]
  for i in *...n do
    s := next s
    let len := s / 7 % 4 + 1
    let mut ks := #[]
    for _ in *...len do
      s := next s
      ks := ks.push keyPool[s / 11 % keyPool.size]!
    s := next s
    out := out.push (ks, { id := s / 13 % (n / 2 + 1), tag := i })
  return out

/-- Splits `es` into `n` consecutive modules of pseudo-random sizes, some of them empty. -/
def splitModules (seed n : Nat) (es : Array α) : Array (Array α) := Id.run do
  let mut s := next (seed + 17)
  let mut cuts := #[]
  for _ in *...(n - 1) do
    s := next s
    cuts := cuts.push (s / 7 % (es.size + 1))
  let bounds := #[0] ++ cuts.qsort (· < ·) ++ #[es.size]
  return (Array.range n).map fun i => es.extract bounds[i]! bounds[i + 1]!

def insertAll (d : DiscrTree V) (es : Array (Array Key × V)) : DiscrTree V :=
  es.foldl (init := d) fun d (ks, v) => d.insertKeyValue ks v

/-- Contents in fold order, comparing values by all fields. -/
def contents (d : DiscrTree V) : List (List String × Nat × Nat) :=
  d.toArray.toList.map fun (ks, v) => (ks.toList.map (toString <| Std.format ·), v.id, v.tag)

def same (d₁ d₂ : DiscrTree V) (es : Array (Array Key × V)) : Bool :=
  contents d₁ == contents d₂ && toString (Std.format d₁) == toString (Std.format d₂) &&
    d₁.size == d₂.size &&
    es.all fun (ks, _) =>
      (d₁.getEntriesWithKeys ks).map (fun v => (v.id, v.tag)) ==
        (d₂.getEntriesWithKeys ks).map (fun v => (v.id, v.tag))

def check (seed nMods nEntries : Nat) : Bool :=
  let es := genEntries seed nEntries
  let mods := splitModules seed nMods es
  let seq := insertAll {} es
  let merged := ofModuleRoots (mods.map fun es => moduleRootsOf es)
  let more := genEntries (seed + 1) 30
  same seq merged es && same (insertAll seq more) (insertAll merged more) (es ++ more)

#guard (List.range 50).all fun seed => check seed 1 40
#guard (List.range 50).all fun seed => check seed 2 40
#guard (List.range 50).all fun seed => check seed 5 60
#guard (List.range 20).all fun seed => check seed 30 300
#guard (List.range 5).all fun seed => check seed 100 2000
#guard check 0 0 0
#guard check 1 3 0

-- Inserting into the merged tree before forcing it gives the same result as afterwards.
#guard
  let es := genEntries 7 200
  let mods := splitModules 7 6 es
  let merged := ofModuleRoots (mods.map fun es => moduleRootsOf es)
  let more := genEntries 8 50
  let r₁ := insertAll merged more
  let _ := merged.size
  contents r₁ == contents (insertAll merged more)

/-! Lookups of actual terms return the same values in the same order. -/

def terms : MetaM (Array Expr) := do
  let x ← mkFreshExprMVar (mkConst ``Nat)
  let y ← mkFreshExprMVar (mkConst ``Nat)
  let n (k : Nat) := mkNatLit k
  let add a b := mkAppN (mkConst ``Nat.add) #[a, b]
  let mul a b := mkAppN (mkConst ``Nat.mul) #[a, b]
  let succ a := mkApp (mkConst ``Nat.succ) a
  return #[add x (n 0), add (n 0) x, add x y, add (succ x) y, mul x (n 1), mul x y, succ (n 3),
    add (mul x y) (n 0), x, add x (succ y), mul (n 0) x]

#eval show MetaM Unit from do
  let ts ← terms
  let es ← ts.mapIdxM fun i t => return ((← mkPath t), ({ id := i % 7, tag := i } : V))
  let es := es ++ es.reverse.mapIdx fun i (ks, v) => (ks, { v with tag := 100 + i })
  for nMods in [1, 2, 3, 8] do
    let mods := splitModules nMods nMods es
    let seq := insertAll {} es
    let merged := ofModuleRoots (mods.map fun es => moduleRootsOf es)
    let queries ← terms
    for q in queries ++ ts do
      let r₁ := (← seq.getMatch q).map (·.tag)
      let r₂ := (← merged.getMatch q).map (·.tag)
      unless r₁ == r₂ do throwError "getMatch mismatch for {q}: {r₁} vs {r₂}"
      let u₁ := (← seq.getUnify q).map (·.tag)
      let u₂ := (← merged.getUnify q).map (·.tag)
      unless u₁ == u₂ do throwError "getUnify mismatch for {q}: {u₁} vs {u₂}"
      let e₁ := (← seq.getMatchWithExtra q).map (·.1.tag)
      let e₂ := (← merged.getMatchWithExtra q).map (·.1.tag)
      unless e₁ == e₂ do throwError "getMatchWithExtra mismatch for {q}: {e₁} vs {e₂}"
