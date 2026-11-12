import Lean.Meta.DiscrTree

/-!
Checks the properties of `DiscrTree.ofModuleRoots` not covered by `Verif.Lean.Meta.DiscrTree.Merge`,
which shows that each merged trie agrees with inserting all entries in module order: the iteration
order of the merged root map, insertion into a merged tree with nodes that are still lazy, and lookups
of terms in merged trees.
-/

open Lean Meta DiscrTree

/-- Values compare by `id` only, so a later duplicate replaces an earlier one, keeping its position. -/
structure V where
  id : Nat
  tag : Nat
  deriving Repr, Inhabited

instance : BEq V := ⟨fun a b => a.id == b.id⟩
instance : ToFormat V := ⟨fun v => s!"{v.id}/{v.tag}"⟩

def f : Key := .const `f 2
def g : Key := .const `g 1
def a : Key := .const `a 0
def b : Key := .const `b 0

/-- An entry with keys `ks` and a value with `id` and `tag`. -/
def e (ks : List Key) (id tag : Nat) : Array Key × V := (ks.toArray, { id, tag })

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

/-- Merging `mods` agrees with inserting their entries in order, also after inserting `more`. -/
def check (mods : Array (Array (Array Key × V))) (more : Array (Array Key × V) := #[]) : Bool :=
  let es := mods.flatten
  let seq := insertAll {} es
  let merged := ofModuleRoots (mods.map fun es => moduleRootsOf es)
  same seq merged es && same (insertAll seq more) (insertAll merged more) (es ++ more)

-- the iteration order of the root map, with root keys shared between modules, occurring in only
-- one module, and of several arities and kinds
#guard check #[#[e [f, a, a] 1 0, e [g, a] 2 1, e [.const `f 1, a] 3 2], #[],
  #[e [.lit (.natVal 3)] 4 3, e [f, a, b] 5 4, e [.proj `S 0 1, a] 6 5],
  #[e [.other] 7 6, e [g, b] 8 7, e [.arrow, a, b] 9 8]]

-- inserting into nodes that are still lazy, including at paths of earlier values
#guard check #[#[e [f, a, a] 1 0, e [g, a] 2 1], #[e [f, a, b] 3 2, e [g, b] 4 3]]
  #[e [f, a, a] 5 4, e [f, a, a] 1 5, e [f, b, b] 6 6, e [g, a] 7 7, e [a] 8 8]

-- Inserting into the merged tree before forcing it gives the same result as afterwards.
#guard
  let mods := #[#[e [f, a, a] 1 0, e [f, b, a] 2 1], #[e [f, a, b] 3 2], #[e [f, b, b] 4 3]]
  let merged := ofModuleRoots (mods.map fun es => moduleRootsOf es)
  let more := #[e [f, a, a] 5 4, e [f, b, a] 2 5]
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

/-- Splits `es` into consecutive modules of `k` entries. -/
def chunks (es : Array α) (k : Nat) : Array (Array α) :=
  (Array.range ((es.size + k - 1) / k)).map fun i => es.extract (i * k) ((i + 1) * k)

#eval show MetaM Unit from do
  let ts ← terms
  let es ← ts.mapIdxM fun i t => return ((← mkPath t), ({ id := i % 7, tag := i } : V))
  let es := es ++ es.reverse.mapIdx fun i (ks, v) => (ks, { v with tag := 100 + i })
  for k in [es.size, 7, 3, 1] do
    let mods := chunks es k
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
