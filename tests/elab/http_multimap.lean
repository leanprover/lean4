import Std.Http.Internal.MultiMap

/-!
Behaviour of `Std.Internal.MultiMap`: lookups on absent keys, single values and repeated keys
interleaved with other keys, and a differential check of every operation against a list model on
pseudo-random operation sequences.
-/

open Std.Internal

def m : MultiMap String Nat :=
  MultiMap.ofList [("a", 1), ("b", 2), ("a", 3), ("c", 4), ("a", 5)]

#guard m.getAll? "a" == some #[1, 3, 5]
#guard m.getAll? "b" == some #[2]
#guard m.getAll? "z" == none

#guard m.get? "a" == some 1
#guard m.get? "c" == some 4
#guard m.get? "z" == none

#guard m.getLast? "a" == some 5
#guard m.getLast? "b" == some 2
#guard m.getLast? "z" == none

#guard m.getD "a" 0 == 1
#guard m.getD "z" 0 == 0
#guard m.get! "c" == 4

#guard m.hasEntry "a" 3
#guard !m.hasEntry "a" 2
#guard !m.hasEntry "z" 1

#guard (MultiMap.empty : MultiMap String Nat).getAll? "a" == none
#guard (MultiMap.empty : MultiMap String Nat).getLast? "a" == none

#guard (m.erase "a").get? "a" == none
#guard (m.erase "a").getAll? "c" == some #[4]
#guard (m.erase "a").getLast? "b" == some 2

#guard (m.replaceLast "a" 9).getAll? "a" == some #[1, 3, 9]
#guard (m.replaceLast "a" 9).get? "a" == some 1
#guard (m.replaceLast "a" 9).getLast? "a" == some 9
#guard (m.replaceLast "z" 9).toList == m.toList

-- Two maps grown from the shared empty value do not see each other's entries.
#guard
  let e : MultiMap String Nat := .empty
  let x := e.insert "a" 1
  let y := e.insert "b" 2
  x.toList == [("a", 1)] && y.toList == [("b", 2)] && e.size == 0

/-! ## Differential check against a list model -/

/-- The reference semantics: entries in insertion order. -/
abbrev Model := List (String × Nat)

def Model.getAll (l : Model) (k : String) : List Nat := l.filterMap fun (k', v) => if k' == k then some v else none

def Model.replaceLast (l : Model) (k : String) (v : Nat) : Model :=
  match (l.zipIdx.filter (·.1.1 == k)).getLast? with
  | some (_, i) => l.set i (k, v)
  | none => l

inductive Op where
  | insert (k : String) (v : Nat)
  | insertMany (k : String) (vs : Array Nat)
  | erase (k : String)
  | eraseMany (ks : Array String)
  | update (k : String) (d : Nat)
  | replaceLast (k : String) (v : Nat)
  | merge (other : List (String × Nat))

def keys : Array String := #["host", "connection", "content-length", "x-a", "x-b"]

def nextRand (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def genOp (s : Nat) : Op × Nat :=
  let s1 := nextRand s
  let s2 := nextRand s1
  let s3 := nextRand s2
  let k := keys[s2 % keys.size]!
  let v := s3 % 100
  let op := match s1 % 16 with
    | 0 => .erase k
    | 1 => .eraseMany #[k, keys[(s3 / 7) % keys.size]!]
    | 2 => .update k v
    | 3 => .replaceLast k v
    | 4 => .insertMany k #[v, v + 1]
    | 5 => .merge [(k, v), (keys[(s3 / 11) % keys.size]!, v + 2)]
    | _ => .insert k v
  (op, s3)

def apply (op : Op) (map : MultiMap String Nat) (model : Model) : MultiMap String Nat × Model :=
  match op with
  | .insert k v => (map.insert k v, model ++ [(k, v)])
  | .insertMany k vs => (map.insertMany k vs, model ++ vs.toList.map (k, ·))
  | .erase k => (map.erase k, model.filter (·.1 != k))
  | .eraseMany ks => (map.eraseMany ks, model.filter (!ks.contains ·.1))
  | .update k d => (map.update k (· + d), model.map fun (k', v) => if k' == k then (k', v + d) else (k', v))
  | .replaceLast k v => (map.replaceLast k v, model.replaceLast k v)
  | .merge other => (map ∪ MultiMap.ofList other, model ++ other)

/-- Every query agrees with the model, for every key. -/
def agrees (map : MultiMap String Nat) (model : Model) : Bool :=
  map.toList == model && map.size == model.length && map.isEmpty == model.isEmpty &&
  (Id.run do
    let mut acc := #[]
    for e in map do acc := acc.push e
    return acc.toList == model) &&
  keys.all fun k =>
    let all := Model.getAll model k
    map.getAll? k == (if all.isEmpty then none else some all.toArray) &&
    map.get? k == all.head? &&
    map.getLast? k == all.getLast? &&
    map.contains k == !all.isEmpty &&
    decide (k ∈ map) == !all.isEmpty &&
    map.getD k 1000 == all.headD 1000 &&
    (all.all fun v => map.hasEntry k v) &&
    !map.hasEntry k 1000 &&
    (if h : k ∈ map then map.get k h == all.head! && map.getAll k h == all.toArray else true)

def check (runs steps : Nat) : Except String Unit := do
  let mut seed := 42
  for run in [0:runs] do
    let mut map : MultiMap String Nat := .empty
    let mut model : Model := []
    for step in [0:steps] do
      let (op, s) := genOp seed
      seed := s
      (map, model) := apply op map model
      unless agrees map model do
        throw s!"run {run}, step {step}: {map.toList} vs model {model}"

#eval show IO Unit from IO.ofExcept (check 200 40)
