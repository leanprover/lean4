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

def elabDecInt (x : TSyntax ``decInt) : CoreM Int := do
  let spelling ← elabLit x "decimal integer"
  let (sign, spelling) := decodeSign spelling
  if sign then
    return .negOfNat <| decodeDecNum <| spelling
  else
    return .ofNat <| decodeDecNum <| spelling

def elabFloat (x : TSyntax ``float) : CoreM Float := do
  let spelling ← elabLit x "float"
  let (sign, spelling) := decodeSign spelling
  if spelling == "inf" then
    if sign then return -1.0/0 else return 1.0/0
  else if spelling = "nan" then
    if sign then return -(0.0/0) else return 0.0/0
  else
    let flt ← id do
      match spelling.split (fun c => c == 'E' || c == 'e') with
      | [m,exp] =>
        let (m,e) ← decodeMantissa m
        let (expSign, exp) := decodeSign exp
        let exp := decodeDecNum exp
        if expSign then
          return Float.ofScientific m true (exp + e)
        else if exp ≥ e then
          return Float.ofScientific m false (exp - e)
        else
          return Float.ofScientific m false (e - exp)
      | [m] =>
        let (m,e) ← decodeMantissa m
        return Float.ofScientific m true e
      | _ => throwErrorAt x "invalid float"
    return if sign then -flt else flt
where
  decodeMantissa m := do
    match m.split (· == '.') with
    | [s,m] =>
      let sn := decodeDecNum s
      let mn := decodeDecNum m
      return (sn * (10 ^ s.length) + mn, m.length)
    | [s] => return (decodeDecNum s, 0)
    | _ => throwErrorAt x "invalid float"

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
  let t : NameDict (Option Value) := {}  -- some: value value, none: partial table
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
  rootTable : Table := {}
  currTable : Table := {}
  currKey : Name := .anonymous
  deriving Inhabited

abbrev TomlElabM := StateT ElabState CoreM

def elabSubKeys (ks : Array (TSyntax ``simpleKey)) : TomlElabM (Name × Name) := do
  let iniCurrKey := (← get).currKey
  try
    let subKey ← ks.foldlM (init := Name.anonymous) fun subKey kStx => do
      let kPart ← elabSimpleKey kStx
      let subKey := subKey.str kPart
      let currKey := (← get).currKey.str kPart
      if let some v := (← get).keyTys.find? currKey then
        unless v matches .dottedPrefix do
          throwErrorAt kStx "cannot redefine key '{currKey}'"
        modify fun s => {s with currKey}
      else
        modify fun s => {s with currKey, keyTys := s.keyTys.insert currKey .dottedPrefix}
      return subKey
    return ((← get).currKey, subKey)
  finally
    modify fun s => {s with currKey := iniCurrKey}

def elabKeyval (kv : TSyntax ``keyval) : TomlElabM Unit := do
  let `(keyval|$k = $v) := kv
    | throwErrorAt kv "ill-formed key-value pair syntax"
  let `(key|$[$ks:simpleKey].*) := k
    | throwErrorAt k "ill-formed key syntax"
  let tailKeyStx := ks.back
  let (rootKey, subKey) ← elabSubKeys ks.pop
  let tailKey ← elabSimpleKey tailKeyStx
  let subKey := subKey.str tailKey
  let rootKey := rootKey.str tailKey
  if (← get).keyTys.contains rootKey then
    throwErrorAt tailKeyStx "cannot redefine key '{rootKey}'"
  else
    let v ← elabVal v
    modify fun s => {
      s with
      currTable := s.currTable.push subKey v
      keyTys := s.keyTys.insert rootKey .value
  }

def saveCurrTable : TomlElabM Unit := do
  let currKey ← modifyGet fun s => (s.currKey, {s with currKey := .anonymous})
  let currTable ← modifyGet fun s => (s.currTable, {s with currTable := {}})
  if currKey.isAnonymous then
    modify fun s => {s with rootTable := s.rootTable.append currTable}
  else
    let rootTable ← modifyGet fun s => (s.rootTable, {s with rootTable := {}})
    try
      let rootTable ← rootTable.insertMapM currKey fun (v? : Option Value) => do
        if let some v := v? then
          if let .array ts := v then
            return .array (ts.push currTable)
          else
            let ty := toString <$> (← get).keyTys.find? currKey |>.getD "unknown"
            throwError "attempted to overwrite {ty} key '{currKey}'"
        else
          return .table currTable
      modify fun s => {s with rootTable}
    catch e =>
      modify fun s => {s with rootTable}
      throw e

def elabHeaderKeys (ks : Array (TSyntax ``simpleKey)) : TomlElabM Name := do
  ks.foldlM (init := Name.anonymous) fun k kStx => do
    let k ← k.str <$> elabSimpleKey kStx
    if let some v := (← get).keyTys.find? k then
      unless v.isValidPrefix do
        throwErrorAt kStx m!"cannot redefine key '{k}'"
    else
      modify fun s => {s with keyTys := s.keyTys.insert k .headerPrefix}
    return k

def elabStdTable (x : TSyntax ``stdTable) : TomlElabM Unit := withRef x do
  let `(stdTable|[$k]) := x
    | throwErrorAt x "ill-formed table syntax"
  let `(key|$[$ks:simpleKey].*) := k
    | throwErrorAt k "ill-formed key syntax"
  saveCurrTable
  let tailKey := ks.back
  let k ← elabHeaderKeys ks.pop
  let k ← k.str <$> elabSimpleKey tailKey
  if let some v := (← get).keyTys.find? k then
    unless v matches .headerPrefix do
      throwErrorAt tailKey m!"cannot redefine key '{k}'"
  modify fun s => {s with  currKey := k, keyTys := s.keyTys.insert k .stdTable}

def elabArrayTableKey (x : TSyntax ``key) : TomlElabM Name := do
  let `(key|$[$ks:simpleKey].*) := x
    | throwErrorAt x "ill-formed key syntax"
  let tailKey := ks.back
  let k ← elabHeaderKeys ks.pop
  let k := k.str (← elabSimpleKey tailKey)
  if let some v := (← get).keyTys.find? k then
    unless v matches .array do
      throwErrorAt tailKey s!"cannot redefine key '{k}'"
  else
    modify fun s => {
      s with
      keyTys := s.keyTys.insert k .array
      rootTable := s.rootTable.insert k (.array #[])
    }
  return k

def elabArrayTable (x : TSyntax ``arrayTable) : TomlElabM Unit := withRef x do
  let `(arrayTable|[[$k]]) := x
    | throwErrorAt x "ill-formed array table syntax"
  saveCurrTable
  let k ← elabArrayTableKey k
  modify fun s => {s with currKey := k}

def elabExpression (x : TSyntax ``expression) : TomlElabM Unit := do
  match x with
  | `(expression|$x:keyval) => elabKeyval x
  | `(expression|$x:stdTable) => elabStdTable x
  | `(expression|$x:arrayTable) => elabArrayTable x
  | _ => throwErrorAt x "ill-formed expression syntax"

nonrec def TomlElabM.run (x : TomlElabM Unit) : CoreM Table :=
  (·.2.rootTable) <$> (x *> saveCurrTable).run {}

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
