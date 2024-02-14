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

structure ElabState where
  rootTable : Table := {}
  currTable : Table := {}
  currKey : Name := .anonymous

abbrev TomlElabM := StateT ElabState CoreM

@[inline] def elabLit {k : SyntaxNodeKind} (x : TSyntax k) (name : String) : TomlElabM String := do
  let some spelling := x.raw.isLit? k
    | throwErrorAt x s!"ill-formed {name} syntax"
  return spelling

def elabBoolean (x : TSyntax ``boolean) : TomlElabM Bool := do
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

def elabDecInt (x : TSyntax ``decInt) : TomlElabM Int := do
  let spelling ← elabLit x "decimal integer"
  let (sign, spelling) := decodeSign spelling
  if sign then
    return .negOfNat <| decodeDecNum <| spelling
  else
    return .ofNat <| decodeDecNum <| spelling

def elabFloat (x : TSyntax ``float) : TomlElabM Float := do
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

def elabBinNum (x : TSyntax ``binNum) : TomlElabM Nat := do
  let spelling ← elabLit x "binary number"
  return spelling.drop 2 |>.foldl (init := 0) fun n c =>
    if c == '_' then n else n*2 + (c.val - '0'.val).toNat

def elabOctNum (x : TSyntax ``octNum) : TomlElabM Nat := do
  let spelling ← elabLit x "octal number"
  return spelling.drop 2 |>.foldl (init := 0) fun n c =>
    if c == '_' then n else n*8 + (c.val - '0'.val).toNat

def decodeHexDigit (c : Char) : Nat :=
  if c  ≤ '9' then (c.val - '0'.val).toNat
  else if c  ≤ 'F' then 10 + (c.val - 'A'.val).toNat
  else 10 + (c.val - 'a'.val).toNat

def elabHexNum (x : TSyntax ``hexNum) : TomlElabM Nat := do
  let spelling ← elabLit x "hexadecimal number"
  return spelling.drop 2 |>.foldl (init := 0) fun n c =>
    if c == '_' then n else n*16 + decodeHexDigit c

def elabDateTime (x : TSyntax ``dateTime) : TomlElabM DateTime := do
  let spelling ← elabLit x "date-time"
  let some dt := DateTime.ofString? spelling
    | throwErrorAt x "invalid date-time"
  return dt

--------------------------------------------------------------------------------
/-! ## Strings & Simple Keys -/
--------------------------------------------------------------------------------

def elabLiteralString (x : TSyntax ``literalString) : TomlElabM String := do
  return (← elabLit x "literalString").drop 1 |>.dropRight 1

def decodeHexDigits (s : Substring) : Nat :=
  s.foldl (init := 0) fun n c => if c == '_' then n else n*16 + decodeHexDigit c

partial def elabBasicStringCore (lit : String) (i : String.Pos := 0) (out := "") : TomlElabM String := do
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
        match curr with
        | 'b'  => elabBasicStringCore lit i (out.push '\x08')
        | 't'  => elabBasicStringCore lit i (out.push '\t')
        | 'n'  => elabBasicStringCore lit i (out.push '\n')
        | 'f'  => elabBasicStringCore lit i (out.push '\x0C')
        | 'r'  => elabBasicStringCore lit i (out.push '\r')
        | '\"' => elabBasicStringCore lit i (out.push '"')
        | '\\' => elabBasicStringCore lit i (out.push '\\')
        | 'u' =>
          let hex := Substring.mk lit i lit.endPos |>.take 4
          elabBasicStringCore lit i (out.push <| .ofNat <| decodeHexDigits hex)
        | 'U' =>
          let hex := Substring.mk lit i lit.endPos |>.take 8
          elabBasicStringCore lit i (out.push <| .ofNat <| decodeHexDigits hex)
        | _ =>
          let i := Substring.mk lit i lit.endPos |>.trimLeft |>.startPos
          elabBasicStringCore lit i out
    else
      elabBasicStringCore lit i (out.push curr)

def elabBasicString (x : TSyntax ``basicString) : TomlElabM String := do
  let spelling ← elabLit x "basic string"
  elabBasicStringCore (spelling.drop 1 |>.dropRight 1)

def dropInitialNewline (s : String) : String :=
  if s.front == '\r' then
    s.drop 2
  else if s.front == '\n' then
    s.drop 1
  else
    s

def elabMlLiteralString (x : TSyntax ``mlLiteralString) : TomlElabM String := do
  let spelling ← elabLit x "multi-line literal string"
  return dropInitialNewline (spelling.drop 3 |>.dropRight 3)

def elabMlBasicString (x : TSyntax ``mlBasicString) : TomlElabM String := do
  let spelling ← elabLit x "multi-line basic string"
  elabBasicStringCore (dropInitialNewline (spelling.drop 3 |>.dropRight 3))

def elabString (x : TSyntax ``string) : TomlElabM String := do
  match x with
  | `(val|$x:literalString) => elabLiteralString x
  | `(val|$x:basicString) => elabBasicString x
  | `(val|$x:mlLiteralString) => elabMlLiteralString x
  | `(val|$x:mlBasicString) => elabMlBasicString x
  | _ => throwErrorAt x "ill-formed string syntax"

@[inline] def elabUnquotedKey (x : TSyntax ``unquotedKey) : TomlElabM String := do
  elabLit x "unquoted key"

def elabSimpleKey (x : TSyntax ``simpleKey) : TomlElabM String := do
  match x with
  | `(simpleKey|$x:unquotedKey) => elabUnquotedKey x
  | `(simpleKey|$x:literalString) => elabLiteralString x
  | `(simpleKey|$x:basicString) => elabBasicString x
  | _ => throwErrorAt x "ill-formed simple key syntax"

--------------------------------------------------------------------------------
/-! ## Complex Values -/
--------------------------------------------------------------------------------

def elabArray (x : TSyntax ``array) (elabVal : TSyntax ``val → TomlElabM α) : TomlElabM (Array α) := do
  let `(val|[$xs,*]) := x
    | throwErrorAt x "ill-formed array syntax"
  xs.getElems.mapM elabVal

def elabKey (x : TSyntax ``key) : TomlElabM Name := do
  match x with
  | `(key|$[$ks:simpleKey].*) => ks.foldlM (init := Name.anonymous) fun k kStx => do
    k.str <$> elabSimpleKey kStx
  | _ => throwErrorAt x "ill-formed key syntax"

def elabInlineTable (x : TSyntax ``inlineTable) (elabVal : TSyntax ``val → TomlElabM Value) : TomlElabM Table := do
  let `(val|{$kvs,*}) := x
    | throwErrorAt x "ill-formed inline table syntax"
  kvs.getElems.foldlM (init := {}) fun t kv => do
    let `(keyval|$kStx = $v) := kv
      | logErrorAt x "ill-formed key-value pair syntax"
        return t
    let k ← elabKey kStx
    if t.contains k then
      logErrorAt kStx s!"cannot redefine key '{k}'"
      return t
    else
      return t.push k (← elabVal v)

partial def elabVal (x : TSyntax ``val) : TomlElabM Value := do
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

def elabNewKeys (ks : Array (TSyntax ``simpleKey)) : TomlElabM Name := do
  ks.foldlM (init := Name.anonymous) fun k kStx => do
    let k ← k.str <$> elabSimpleKey kStx
    if (← get).currTable.contains k then
      throwErrorAt kStx m!"cannot redefine key '{k}'"
    return k

def elabNewKey (x : TSyntax ``key) : TomlElabM Name := do
  match x with
  | `(key|$[$ks:simpleKey].*) => elabNewKeys ks
  | _ => throwErrorAt x "ill-formed key syntax"

def elabKeyval (x : TSyntax ``keyval) : TomlElabM Unit := do
  let `(keyval|$k = $v) := x
    | throwErrorAt x "ill-formed key-value pair syntax"
  let k ← elabNewKey k; let v ← elabVal v
  modify fun s => {s with currTable := s.currTable.insert k v}

def saveCurrTable : TomlElabM Unit := do
  modify fun s =>
    if s.currKey.isAnonymous then {
      rootTable := s.rootTable.append s.currTable
      currTable := {}, currKey := .anonymous
    } else {
      rootTable := s.rootTable.push s.currKey s.currTable
      currTable := {}, currKey := .anonymous
    }

def elabStdTable (x : TSyntax ``stdTable) : TomlElabM Unit := do
  let `(stdTable|[$k]) := x
    | throwErrorAt x "ill-formed table syntax"
  saveCurrTable
  let k ← elabNewKey k
  modify fun s => {s with currKey := k}

def elabNewArrayKey (x : TSyntax ``key) : TomlElabM Name := do
  let `(key|$[$ks:simpleKey].*) := x
    | throwErrorAt x "ill-formed key syntax"
  let lastKey := ks.back
  let k ← elabNewKeys ks.pop
  let k := k.str (← elabSimpleKey lastKey)
  if let some v := (← get).rootTable.find? k then
    if let .array _ := v then
      return k
    else
      throwErrorAt lastKey s!"cannot redefine key '{k}'"
  else
    modify fun s => {s with rootTable := s.rootTable.push k (.array #[])}
    return k

def elabArrayTable (x : TSyntax ``arrayTable) : TomlElabM Unit := do
  let `(stdTable|[$k]) := x
    | throwErrorAt x "ill-formed array table syntax"
  saveCurrTable
  let k ← elabNewArrayKey k
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
