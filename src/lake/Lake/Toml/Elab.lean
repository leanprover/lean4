/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.CoreM
import Lake.Toml.Value
import Lake.Toml.Grammar

/-!
# TOML Elaboration

Elaborates TOML syntax into Lean data types.
At top-level, elaborates a whole TOML file into a `Toml.Table`.
-/

open Lean

namespace Lake.Toml

@[inline] def elabLit {k : SyntaxNodeKind} (x : TSyntax k) (name : String) : CoreM String := do
  let some spelling := x.raw.isLit? k
    | throwErrorAt x s!"ill-formed {name} syntax"
  return spelling

def elabBoolean (x : TSyntax ``boolean) : CoreM Bool := do
  match x with
  | `(boolean|true)=> return true
  | `(boolean|false) => return false
  | _ => throwErrorAt x "invalid boolean"

--------------------------------------------------------------------------------
/-! ## Numerals -/
--------------------------------------------------------------------------------

def decodeDecNum (s : String) : Nat :=
  s.foldl (init := 0) fun n c =>
    if c == '_' then n else n*10 + (c.val - '0'.val).toNat

def decodeSign (s : String) : Bool × String :=
  if s.front == '-' then
    (true, s.drop 1)
  else if s.front == '+' then
    (false, s.drop 1)
  else
    (false, s)

def decodeDecInt (s : String) : Int :=
  let (sign, s) := decodeSign s
  if sign then
    .negOfNat <| decodeDecNum s
  else
    .ofNat <| decodeDecNum s

def elabDecInt (x : TSyntax ``decInt) : CoreM Int := do
  return decodeDecInt <| ← elabLit x "decimal integer"

def decodeMantissa (s : String) : Nat × Nat :=
  let (m,e) := s.foldl (init := (0,s.length)) fun (m,e) c =>
    match c with
    | '_' => (m,e)
    | '.' => (m,0)
    | c => (m*10 + (c.val - '0'.val).toNat, e+1)
  (m, if e ≥ s.length then 0 else e)

def decodeFrExp (s : String) : Nat × Int :=
  match s.split (fun c => c == 'E' || c == 'e') with
  | [m,exp] =>
    let exp := decodeDecInt exp
    let (m,dotExp) := decodeMantissa m
    (m, Int.negOfNat dotExp + exp)
  | [m] =>
    let (m, e) := decodeMantissa m
    (m, Int.negOfNat e)
  | _ => (0,0)

def decodeFloat (s : String) : Float :=
  let (sign, s) := decodeSign s
  if s.toLower = "inf" then
    if sign then -1.0/0 else 1.0/0
  else if s.toLower = "nan" then
    if sign then -(0.0/0) else 0.0/0
  else
    let (m,e) := decodeFrExp s
    let flt := Float.ofScientific m (e < 0) e.natAbs
    if sign then -flt else flt

def elabFloat (x : TSyntax ``float) : CoreM Float := do
  return decodeFloat <| ← elabLit x "float"

def elabBinNum (x : TSyntax ``binNum) : CoreM Nat := do
  let spelling ← elabLit x "binary number"
  return spelling.drop 2 |>.foldl (init := 0) fun n c =>
    if c == '_' then n else n*2 + (c.val - '0'.val).toNat

def elabOctNum (x : TSyntax ``octNum) : CoreM Nat := do
  let spelling ← elabLit x "octal number"
  return spelling.drop 2 |>.foldl (init := 0) fun n c =>
    if c == '_' then n else n*8 + (c.val - '0'.val).toNat

def decodeHexDigit (c : Char) : Nat :=
  if c  ≤ '9' then (c.val - '0'.val).toNat
  else if c  ≤ 'F' then 10 + (c.val - 'A'.val).toNat
  else 10 + (c.val - 'a'.val).toNat

def elabHexNum (x : TSyntax ``hexNum) : CoreM Nat := do
  let spelling ← elabLit x "hexadecimal number"
  return spelling.drop 2 |>.foldl (init := 0) fun n c =>
    if c == '_' then n else n*16 + decodeHexDigit c

def elabDateTime (x : TSyntax ``dateTime) : CoreM DateTime := do
  let spelling ← elabLit x "date-time"
  let some dt := DateTime.ofString? spelling
    | throwErrorAt x "invalid date-time"
  return dt

--------------------------------------------------------------------------------
/-! ## Strings & Simple Keys -/
--------------------------------------------------------------------------------

def elabLiteralString (x : TSyntax ``literalString) : CoreM String := do
  return (← elabLit x "literalString").drop 1 |>.dropRight 1

def decodeHexDigits (s : Substring) : Nat :=
  s.foldl (init := 0) fun n c => n*16 + decodeHexDigit c

partial def elabBasicStringCore (lit : String) (i : String.Pos := 0) (out := "") : CoreM String := do
  if h : lit.atEnd i then
    return out
  else
    let curr := lit.get' i h
    let i := lit.next' i h
    if curr == '\\' then
      if h : lit.atEnd i then
        return out
      else
        let curr := lit.get' i h
        let elabUnicodeEscape escape :=
          let val := decodeHexDigits escape
          if h : val.isValidChar then
            let ch := Char.ofNatAux val h
            elabBasicStringCore lit escape.stopPos (out.push ch)
          else
            throwError "invalid unicode escape '{escape}'"
        match curr with
        | 'b'  => elabBasicStringCore lit (lit.next' i h) (out.push '\x08')
        | 't'  => elabBasicStringCore lit (lit.next' i h) (out.push '\t')
        | 'n'  => elabBasicStringCore lit (lit.next' i h) (out.push '\n')
        | 'f'  => elabBasicStringCore lit (lit.next' i h) (out.push '\x0C')
        | 'r'  => elabBasicStringCore lit (lit.next' i h) (out.push '\r')
        | '\"' => elabBasicStringCore lit (lit.next' i h) (out.push '"')
        | '\\' => elabBasicStringCore lit (lit.next' i h) (out.push '\\')
        | 'u'  => elabUnicodeEscape (Substring.mk lit (lit.next' i h) lit.endPos |>.take 4)
        | 'U'  => elabUnicodeEscape (Substring.mk lit (lit.next' i h) lit.endPos |>.take 8)
        | _ =>
          let i := Substring.mk lit i lit.endPos |>.trimLeft |>.startPos
          elabBasicStringCore lit i out
    else
      elabBasicStringCore lit i (out.push curr)

def elabBasicString (x : TSyntax ``basicString) : CoreM String := do
  let spelling ← elabLit x "basic string"
  withRef x <| elabBasicStringCore (spelling.drop 1 |>.dropRight 1)

def dropInitialNewline (s : String) : String :=
  if s.front == '\r' then
    s.drop 2
  else if s.front == '\n' then
    s.drop 1
  else
    s

def elabMlLiteralString (x : TSyntax ``mlLiteralString) : CoreM String := do
  let spelling ← elabLit x "multi-line literal string"
  return dropInitialNewline (spelling.drop 3 |>.dropRight 3)

def elabMlBasicString (x : TSyntax ``mlBasicString) : CoreM String := do
  let spelling ← elabLit x "multi-line basic string"
  withRef x <| elabBasicStringCore (dropInitialNewline (spelling.drop 3 |>.dropRight 3))

def elabString (x : TSyntax ``string) : CoreM String := do
  match x with
  | `(val|$x:literalString) => elabLiteralString x
  | `(val|$x:basicString) => elabBasicString x
  | `(val|$x:mlLiteralString) => elabMlLiteralString x
  | `(val|$x:mlBasicString) => elabMlBasicString x
  | _ => throwErrorAt x "ill-formed string syntax"

@[inline] def elabUnquotedKey (x : TSyntax ``unquotedKey) : CoreM String := do
  elabLit x "unquoted key"

def elabSimpleKey (x : TSyntax ``simpleKey) : CoreM String := do
  match x with
  | `(simpleKey|$x:unquotedKey) => elabUnquotedKey x
  | `(simpleKey|$x:literalString) => elabLiteralString x
  | `(simpleKey|$x:basicString) => elabBasicString x
  | _ => throwErrorAt x "ill-formed simple key syntax"

--------------------------------------------------------------------------------
/-! ## Complex Values -/
--------------------------------------------------------------------------------

def elabArray (x : TSyntax ``array) (elabVal : TSyntax ``val → CoreM α) : CoreM (Array α) := do
  let `(val|[$xs,*]) := x
    | throwErrorAt x "ill-formed array syntax"
  xs.getElems.mapM elabVal

def elabInlineTable (x : TSyntax ``inlineTable) (elabVal : TSyntax ``val → CoreM Value) : CoreM Table := do
  let `(val|{$kvs,*}) := x
    | throwErrorAt x "ill-formed inline table syntax"
  let t : NameDict (Option Value) := {}  -- some: static value, none: partial table
  let t ← kvs.getElems.foldlM (init := t) fun t kv => do
    let `(keyval|$k = $v) := kv
      | throwErrorAt kv "ill-formed key-value pair syntax"
    let `(key|$[$ks].*) := k
      | throwErrorAt k "ill-formed key syntax"
    let tailKey := ks.back
    let (k, t) ← StateT.run (s := t) <| ks.pop.foldlM (init := Name.anonymous) fun k p => do
      let k ← k.str <$> elabSimpleKey p
      if let some v := t.find? k then
        unless v.isNone do throwErrorAt p m!"cannot redefine key '{k}'"
      else
        modify fun t => t.push k none
      return k
    let k ← k.str <$> elabSimpleKey tailKey
    if t.contains k then
      throwErrorAt tailKey m!"cannot redefine key '{k}'"
    else
      return t.push k (← elabVal v)
  return t.filterMap id

partial def elabVal (x : TSyntax ``val) : CoreM Value := do
  match x with
  | `(val|$x:float) => .float <$> elabFloat x
  | `(val|$x:decInt) => .integer <$> elabDecInt x
  | `(val|$x:binNum) => .integer <$> .ofNat <$> elabBinNum x
  | `(val|$x:octNum) => .integer <$> .ofNat <$> elabOctNum x
  | `(val|$x:hexNum) => .integer <$> .ofNat <$> elabHexNum x
  | `(val|$x:dateTime) => .dateTime <$> elabDateTime x
  | `(val|$x:string) => .string <$> elabString x
  | `(val|$x:boolean) => .boolean <$> elabBoolean x
  | `(val|$x:array) => .array <$> elabArray x elabVal
  | `(val|$x:inlineTable) => .table <$> elabInlineTable x elabVal
  | _ => throwErrorAt x "ill-formed value syntax"

--------------------------------------------------------------------------------
/-! ## Expressions -/
--------------------------------------------------------------------------------

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
    items := s.items.push (k, {})
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
        items := s.items.push (k, .array #[{}])
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
        items := s.items.push (k, .array #[{}])
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
      | .table newT =>
        let newT := mkSimpleTable newT.items
        t.insertMap k fun v? =>
          match v? with
          | some (.table vt) => vt ++ newT
          | _ => newT
      | _ =>
        t.insertMap k fun v? =>
          match v? with
          | some (.array vs) => vs.push {}
          | _ => newV
    | k' :: ks => t.insertMap k fun v? =>
      if let some v := v? then
        match v with
        | .array vs =>
          vs.modify (vs.size-1) fun
          | .table t' => insert t' k' ks newV
          | _ => {}
        | .table t' => insert t' k' ks newV
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
