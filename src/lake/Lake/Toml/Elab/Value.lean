/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.CoreM
import Lake.Toml.Data.Value
import Lake.Toml.Grammar

/-!
# TOML Value Elaboration

Elaborates TOML values into Lean data types.
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
  if s = "inf" then
    if sign then -1.0/0 else 1.0/0
  else if s = "nan" then
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
    let tailKey := ks.back!
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
  return t.filterMap fun _ v => v

partial def elabVal (x : TSyntax ``val) : CoreM Value := do
  match x with
  | `(val|$x:float) => .float x <$> elabFloat x
  | `(val|$x:decInt) => .integer x <$> elabDecInt x
  | `(val|$x:binNum) => .integer x <$> .ofNat <$> elabBinNum x
  | `(val|$x:octNum) => .integer x <$> .ofNat <$> elabOctNum x
  | `(val|$x:hexNum) => .integer x <$> .ofNat <$> elabHexNum x
  | `(val|$x:dateTime) => .dateTime x <$> elabDateTime x
  | `(val|$x:string) => .string x <$> elabString x
  | `(val|$x:boolean) => .boolean x <$> elabBoolean x
  | `(val|$x:array) => .array x <$> elabArray x elabVal
  | `(val|$x:inlineTable) => .table x <$> elabInlineTable x elabVal
  | _ => throwErrorAt x "ill-formed value syntax"
