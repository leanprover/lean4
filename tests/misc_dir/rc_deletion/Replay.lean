import Schedule

/-!
Replay what `heaps.c` prints through `drain`, and require the same results.

`heaps.c` releases the roots of random heaps through the runtime's `lean_dec_ref`, and prints each
heap, the objects each release reclaims and the counts it leaves. Each heap here becomes an
ownership graph whose fields are the slots that hold nodes, and each release runs through `drop`
and `drain`. Every heap must meet the hypothesis of `drain_released`, so that the theorems describe
every release replayed. `drain` must reclaim the same objects, in any order, and leave the same
counts.
-/

open RcGraph

namespace Replay

instance (g : Graph α objects roots fields) (s : State objects roots fields) :
    Decidable (Valid g s) := by
  unfold Valid; infer_instance

instance (s : State objects roots fields) : Decidable (QueueSafe s) := by
  unfold QueueSafe; infer_instance

/-- Whether `s` meets the hypothesis of `drain_released`. -/
def quiescent (g : Graph α objects roots fields) (s : State objects roots fields) : Bool :=
  decide (Valid g s) && decide (QueueSafe s) && s.todo.isEmpty &&
    decide (∀ f, .field f ∈ s.own → (s.rc (g.source f)).isSome)

theorem quiescent_spec {g : Graph α objects roots fields} {s : State objects roots fields}
    (h : quiescent g s = true) : Quiescent g s := by
  simp only [quiescent, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

structure Case where
  roots : List Nat
  counts : Array Int32
  edges : Array (List Nat)
  /-- What each release reclaims, and the counts it leaves, `f` for a reclaimed node. -/
  releases : Array (List Nat × List String)

def words (line : String) : List String :=
  (line.splitOn " ").filter (· ≠ "")

def parseNat (w : String) : Except String Nat :=
  match w.toNat? with
  | some n => pure n
  | none => throw s!"not a number: {w}"

def parseInt (w : String) : Except String Int :=
  match w.toInt? with
  | some i => pure i
  | none => throw s!"not a number: {w}"

/-- The case that starts at line `i`, and the line after it. -/
def parseCase (lines : Array String) (i : Nat) : Except String (Case × Nat) := do
  let roots ← match words lines[i]! with
    | "heap" :: roots => roots.mapM parseNat
    | _ => throw s!"expected a heap: {lines[i]!}"
  let mut j := i + 1
  let mut counts := #[]
  let mut edges := #[]
  while j < lines.size && (words lines[j]!).head? == some "node" do
    match words lines[j]! with
    | _ :: rc :: targets =>
      counts := counts.push (Int32.ofInt (← parseInt rc))
      edges := edges.push (← targets.mapM parseNat)
    | _ => throw s!"expected a node: {lines[j]!}"
    j := j + 1
  let mut releases := #[]
  for _ in roots do
    match words lines[j]! with
    | "free" :: rest =>
      let (freed, rc) := rest.span (· ≠ "rc")
      releases := releases.push (← freed.mapM parseNat, rc.drop 1)
    | _ => throw s!"expected a release: {lines[j]!}"
    j := j + 1
  pure ({ roots, counts, edges, releases }, j)

def fin (n : Nat) (i : Nat) : Except String (Fin n) :=
  if h : i < n then pure ⟨i, h⟩ else throw s!"no node {i}"

/--
A count read from a table. Releases replace `rc` by `lookup (Array.ofFn rc)`, so that reading a
count does not run through every earlier release.
-/
def lookup {n : Nat} (a : Array (Option Int32)) (o : Fin n) : Option Int32 := a[o.val]!

def runCase (c : Case) : Except String Unit := do
  let n := c.counts.size
  let roots ← c.roots.toArray.mapM (fin n)
  let mut fields := #[]
  for h : i in [0:n] do
    for j in c.edges[i]! do
      fields := fields.push ((⟨i, h.upper⟩ : Fin n), ← fin n j)
  let g : Graph Nat n roots.size fields.size :=
    { payload := Fin.val, root := (roots[·]), source := (fields[·].1), target := (fields[·].2) }
  let own :=
    (List.finRange roots.size).map Token.root ++ (List.finRange fields.size).map Token.field
  let mut s : State n roots.size fields.size :=
    { own, rc := lookup (Array.ofFn fun (o : Fin n) => some c.counts[o]!) }
  unless quiescent g s do
    throw "the heap does not meet the hypothesis of `drain_released`"
  for h : r in [0:roots.size] do
    let s' := drain g (drop g s (.root ⟨r, h.upper⟩))
    let (freed, rc) := c.releases[r]!
    let reclaimed := (s'.freed.take (s'.freed.length - s.freed.length)).map Fin.val
    unless reclaimed.isPerm freed do
      throw s!"release {r}: `drain` reclaims {reclaimed}, the runtime {freed}"
    let counts := (List.finRange n).map fun o =>
      if o ∈ s'.freed then "f" else match s'.rc o with | some rc => toString rc | none => "-"
    unless counts == rc do
      throw s!"release {r}: `drain` leaves {counts}, the runtime {rc}"
    s := { s' with rc := lookup (Array.ofFn s'.rc) }

end Replay

open Replay in
def main (args : List String) : IO UInt32 := do
  let [corpus] := args | throw <| .userError "expected the output of heaps.c"
  let lines ← IO.FS.lines corpus
  let mut i := 0
  let mut cases := 0
  let mut releases := 0
  while i < lines.size do
    match parseCase lines i >>= fun (c, j) => runCase c *> pure (c, j) with
    | .ok (c, j) =>
      cases := cases + 1
      releases := releases + c.roots.length
      i := j
    | .error e => throw <| .userError s!"line {i + 1}: {e}"
  if cases == 0 then throw <| .userError "no heaps"
  IO.println s!"{cases} heaps and {releases} releases agree with `drain`"
  return 0
