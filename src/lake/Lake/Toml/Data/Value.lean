/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Toml.Data.Dict
import Lake.Toml.Data.DateTime

/-!
# TOML Value
-/

open Lean

namespace Lake.Toml

/-- A TOML value with optional source info. -/
inductive Value
| string (ref : Syntax) (s : String)
| integer (ref : Syntax) (n : Int)
| float (ref : Syntax) (n : Float)
| boolean (ref : Syntax) (b : Bool)
| dateTime (ref : Syntax) (dt : DateTime)
| array (ref : Syntax) (xs : Array Value)
| private table' (ref : Syntax) (xs : RBDict Name Value Name.quickCmp)
deriving Inhabited, BEq

/-- A TOML table, an ordered key-value map of TOML values (`Lake.Toml.Value`). -/
abbrev Table := NameDict Value

@[inline] def Table.empty : Table := RBDict.empty
@[inline] def Table.mkEmpty (capacity : Nat) : Table := RBDict.mkEmpty capacity

@[match_pattern] abbrev Value.table (ref : Syntax) (t : Table) :=
  Value.table' ref t

@[inline] def Value.ref : Value → Syntax
| .string (ref := ref) .. => ref
| .integer (ref := ref) .. => ref
| .float (ref := ref) .. => ref
| .boolean (ref := ref) .. => ref
| .dateTime (ref := ref) .. => ref
| .array (ref := ref) .. => ref
| .table (ref := ref) .. => ref

--------------------------------------------------------------------------------
/-! ## Pretty Printing -/
--------------------------------------------------------------------------------

def ppString (s : String) : String :=
  let s := s.foldl (init := "\"") fun s c =>
    match c with
    | '\x08' => s ++ "\\b"
    | '\t' => s ++ "\\t"
    | '\n' => s ++ "\\n"
    | '\x0C' => s ++ "\\f"
    | '\r' => s ++ "\\r"
    | '\"' => s ++ "\\\""
    | '\\' => s ++ "\\\\"
    | _ =>
      if c.val < 0x20 || c.val == 0x7F then
        s ++ "\\u" ++ lpad (String.mk <| Nat.toDigits 16 c.val.toNat) '0' 4
      else
        s.push c
  s.push '\"'

def ppSimpleKey (k : String) : String :=
  if k.all (fun c => c.isAlphanum || c == '_' || c == '-') then
    k
  else
    ppString k

partial def ppKey (k : Name) : String :=
  match k with
  | .str p s =>
    if p.isAnonymous then
      ppSimpleKey s
    else
      s!"{ppKey p}.{ppSimpleKey s}"
  | _ => ""

mutual

partial def ppInlineTable (t : Table) : String :=
  let xs := t.items.map fun (k,v) => s!"{ppKey k} = {Value.toString v}"
  "{" ++ ", ".intercalate xs.toList ++ "}"

partial def ppInlineArray (vs : Array Value) : String :=
  let xs := vs.map Value.toString
  "[" ++ ", ".intercalate xs.toList ++ "]"

partial def Value.toString (v : Value) : String :=
  match v with
  | .string _ s => ppString s
  | .integer _ n => toString n
  | .float _ n => toString n
  | .boolean _ b => toString b
  | .dateTime _ dt => toString dt
  | .array _ vs => ppInlineArray vs
  | .table _ t => ppInlineTable t

end

instance : ToString Value := ⟨Value.toString⟩

def ppTable (t : Table) : String :=
  let (ts, fs) := t.items.foldl (init := ("", "")) fun (ts, fs) (k,v) =>
    match v with
    | .array _ vs =>
      if vs.isEmpty then
        (ts.append s!"{ppKey k} = []\n", fs)
      else if vs.all (· matches .table ..) then
        let fs := vs.foldl (init := fs) fun s v =>
          match v with
          | .table _ t =>
            let s := s ++ s!"[[{ppKey k}]]\n"
            let s := t.items.foldl (fun s (k,v) => appendKeyval s k v) s
            s.push '\n'
          | _ => unreachable!
        (ts, fs)
      else
        (ts.append s!"{ppKey k} = {ppInlineArray vs}\n", fs)
    | .table _ t =>
      let fs := fs ++ s!"[{ppKey k}]\n"
      let fs := t.items.foldl (fun s (k,v) => appendKeyval s k v) fs
      (ts, fs.push '\n')
    | _ => (appendKeyval ts k v, fs)
  -- Ensures root table keys come before subtables
  -- See https://github.com/leanprover/lean4/issues/4099
  (ts.push '\n' ++ fs).trimRight.push '\n'
where
  appendKeyval s k v :=
    s.append s!"{ppKey k} = {v}\n"
