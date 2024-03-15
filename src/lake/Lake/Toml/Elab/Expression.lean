/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Toml.Elab.Value

/-!
# TOML Expression Elaboration

Elaborates top-level TOML syntax into a Lean `Toml.Table`.
-/

open Lean

namespace Lake.Toml

/-- The manner in which a TOML key was declared. -/
inductive KeyTy
/-- A key declared via `key = v`. -/
| value
/-- A key declared via `[key]`. -/
| stdTable
/-- A key declared via `[[key]]`. -/
| array
/-- A key declared via `key.foo`. -/
| dottedPrefix
/-- A key declared via `[key.foo]` or `[[key.foo]]`. -/
| headerPrefix
deriving Inhabited

protected def KeyTy.toString (ty : KeyTy) :=
  match ty with
  | .value => "value"
  | .stdTable => "table"
  | .array => "array"
  | .dottedPrefix => "dotted"
  | .headerPrefix => "dotted"

instance : ToString KeyTy := ⟨KeyTy.toString⟩

def KeyTy.isValidPrefix (ty : KeyTy) :=
  match ty with
  | .stdTable | .headerPrefix | .dottedPrefix  => true
  | _ => false

structure ElabState where
  keyTys : NameMap KeyTy := {}
  arrKeyTys : NameMap (NameMap KeyTy) := {}
  arrParents : NameMap Name := {}
  currArrKey : Name := .anonymous
  currKey : Name := .anonymous
  items : Array (Name × Value) := {}
  deriving Inhabited

abbrev TomlElabM := StateT ElabState CoreM

def elabSubKeys (ks : Array (TSyntax ``simpleKey)) : TomlElabM Name := do
  ks.foldlM (init := (← get).currKey) fun k kStx => do
    let k := k.str <| ← elabSimpleKey kStx
    if let some ty := (← get).keyTys.find? k then
      unless ty matches .dottedPrefix do
        throwErrorAt kStx "cannot redefine {ty} key '{k}'"
    else
      modify fun s => {s with keyTys := s.keyTys.insert k .dottedPrefix}
    return k

def elabKeyval (kv : TSyntax ``keyval) : TomlElabM Unit := do
  let `(keyval|$k = $v) := kv
    | throwErrorAt kv "ill-formed key-value pair syntax"
  let `(key|$[$ks:simpleKey].*) := k
    | throwErrorAt k "ill-formed key syntax"
  let tailKeyStx := ks.back
  let k ← elabSubKeys ks.pop
  let k := k.str <| ← elabSimpleKey tailKeyStx
  if let some ty := (← get).keyTys.find? k then
    throwErrorAt tailKeyStx "cannot redefine {ty} key '{k}'"
  else
    let v ← elabVal v
    modify fun s => {
      s with
      items := s.items.push (k, v)
      keyTys := s.keyTys.insert k .value
  }

def elabHeaderKeys (ks : Array (TSyntax ``simpleKey)) : TomlElabM Name := do
  modify fun s =>
    let arrKeyTys := s.arrKeyTys.insert s.currArrKey s.keyTys
    {
      s with
      arrKeyTys
      currArrKey := .anonymous
      keyTys := arrKeyTys.find? .anonymous |>.getD {}
    }
  ks.foldlM (init := Name.anonymous) fun k kStx => do
    let k ← k.str <$> elabSimpleKey kStx
    if let some ty := (← get).keyTys.find? k then
      match ty with
      | .array =>
        let some keyTys := (← get).arrKeyTys.find? k
          | throwError "(internal) bad array key '{k}'"
        modify fun s => {s with keyTys, currArrKey := k}
      | .stdTable | .headerPrefix | .dottedPrefix  => pure ()
      | _ => throwErrorAt kStx m!"cannot redefine {ty} key '{k}'"
    else
      modify fun s => {s with keyTys := s.keyTys.insert k .headerPrefix}
    return k

def elabStdTable (x : TSyntax ``stdTable) : TomlElabM Unit := withRef x do
  let `(stdTable|[$k]) := x
    | throwErrorAt x "ill-formed table syntax"
  let `(key|$[$ks:simpleKey].*) := k
    | throwErrorAt k "ill-formed key syntax"
  let tailKey := ks.back
  let k ← elabHeaderKeys ks.pop
  let k ← k.str <$> elabSimpleKey tailKey
  if let some ty := (← get).keyTys.find? k then
    unless ty matches .headerPrefix do
      throwErrorAt tailKey m!"cannot redefine {ty} key '{k}'"
  modify fun s => {
    s with
    currKey := k
    keyTys := s.keyTys.insert k .stdTable
    items := s.items.push (k, .table x {})
  }

def elabArrayTableKey (x : TSyntax ``key) : TomlElabM Name := do
  let `(key|$[$ks:simpleKey].*) := x
    | throwErrorAt x "ill-formed key syntax"
  let tailKey := ks.back
  let k ← elabHeaderKeys ks.pop
  let k := k.str (← elabSimpleKey tailKey)
  if let some ty := (← get).keyTys.find? k then
    if ty matches .array then
      let s ← get
      let some keyTys := s.arrParents.find? k >>= s.arrKeyTys.find?
        | throwError "(internal) bad array key '{k}'"
      modify fun s => {
        s with
        keyTys, currArrKey := k
        items := s.items.push (k, .array x #[.table x {}])
      }
    else
      throwErrorAt tailKey s!"cannot redefine {ty} key '{k}'"
  else
    modify fun s =>
      let keyTys := s.keyTys.insert k .array
      {
        s with
        keyTys
        currArrKey := k
        arrKeyTys := s.arrKeyTys.insert s.currArrKey keyTys
        arrParents := s.arrParents.insert k s.currArrKey
        items := s.items.push (k, .array x #[.table x {}])
      }
  return k

def elabArrayTable (x : TSyntax ``arrayTable) : TomlElabM Unit := withRef x do
  let `(arrayTable|[[$k]]) := x
    | throwErrorAt x "ill-formed array table syntax"
  let k ← elabArrayTableKey k
  modify fun s => {s with currKey := k}

def elabExpression (x : TSyntax ``expression) : TomlElabM Unit := do
  match x with
  | `(expression|$x:keyval) => elabKeyval x
  | `(expression|$x:stdTable) => elabStdTable x
  | `(expression|$x:arrayTable) => elabArrayTable x
  | _ => throwErrorAt x "ill-formed expression syntax"

partial def mkSimpleTable (items : Array (Name × Value)) : Table :=
  items.foldl (init := {}) fun t (k,v) =>
    match k.components with
    | .nil => t
    | .cons k ks => insert t k ks v
where
  insert (t : Table) k ks newV :=
    match ks with
    | .nil =>
      match newV with
      | .table _ newT =>
        let newT := mkSimpleTable newT.items
        t.insertMap k fun v? =>
          match v? with
          | some (.table ref vt) => .table ref <| vt ++ newT
          | _ => newT
      | _ =>
        t.insertMap k fun v? =>
          match v? with
          | some (.array _ vs) => vs.push {}
          | _ => newV
    | k' :: ks => t.insertMap k fun v? =>
      if let some v := v? then
        match v with
        | .array ref vs =>
          .array ref <| vs.modify (vs.size-1) fun
          | .table ref t' => .table ref <| insert t' k' ks newV
          | _ => {}
        | .table ref t' => .table ref <| insert t' k' ks newV
        | _ => {}
      else
        insert {} k' ks newV

nonrec def TomlElabM.run (x : TomlElabM Unit) : CoreM Table := do
  let (_,s) ← x.run {}
  return mkSimpleTable s.items

def elabToml (x : TSyntax ``toml) : CoreM Table := do
  let `(toml|$xs*) := x
    | throwErrorAt x "ill-formed TOML syntax"
  TomlElabM.run do
  let mut recovering := false
  for x in xs.getElems do
    try
      match x with
      | `(expression|$x:keyval) =>
        unless recovering do
          elabKeyval x
      | `(expression|$x:stdTable) =>
        elabStdTable x
        recovering := false
      | `(expression|$x:arrayTable) =>
        elabArrayTable x
        recovering := false
      | _ =>
        logErrorAt x "ill-formed expression syntax"
    catch e : Exception =>
      recovering := true
      logErrorAt e.getRef e.toMessageData
