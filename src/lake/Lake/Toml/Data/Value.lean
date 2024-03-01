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

/-- A TOML value. -/
inductive Value
| string (s : String)
| integer (n : Int)
| float (n : Float)
| boolean (b : Bool)
| dateTime (dt : DateTime)
| array (xs : Array Value)
| private table' (xs : RBDict Name Value Name.quickCmp)
deriving Inhabited, BEq

/-- A TOML table, an ordered key-value map of TOML values (`Lake.Toml.Value`). -/
abbrev Table := NameDict Value

@[match_pattern] abbrev Value.table (t : Table) := Value.table' t

instance : OfNat Value n := ⟨.integer n⟩
instance : EmptyCollection Value := ⟨.table {}⟩
instance : Coe String Value := ⟨.string⟩
instance : Coe Int Value := ⟨.integer⟩
instance : Coe Float Value := ⟨.float⟩
instance : Coe Bool Value := ⟨.boolean⟩
instance : Coe DateTime Value := ⟨.dateTime⟩
instance : Coe (Array Value) Value := ⟨.array⟩
instance : Coe Table Value := ⟨.table⟩

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
  have : ToString Value := ⟨Value.toString⟩
  let xs := t.items.map fun (k,v) => s!"{ppKey k} = {v}"
  "{" ++ ", ".intercalate xs.toList ++ "}"

partial def Value.toString (v : Value) : String :=
  have : ToString Value := ⟨Value.toString⟩
  match v with
  | .string s => ppString s
  | .integer n => toString n
  | .float n => toString n
  | .boolean b => toString b
  | .dateTime dt => toString dt
  | .array xs => toString xs.toList
  | .table t => ppInlineTable t

end

instance : ToString Value := ⟨Value.toString⟩

def ppTable (t : Table) : String :=
  String.trimLeft <| t.items.foldl (init := "") fun s (k,v) =>
    match v with
    | .array xs => xs.foldl (init := s) fun s v =>
      match v with
      | .table t =>
        let s := s ++ s!"\n[[{ppKey k}]]\n"
        t.items.foldl (fun s (k,v) => appendKeyval s k v) s
      | _ => appendKeyval s k v
    | .table t =>
      let s := s ++ s!"\n[{ppKey k}]\n"
      t.items.foldl (fun s (k,v) => appendKeyval s k v) s
    | _ => appendKeyval s k v
where
  appendKeyval s k v :=
    s.append s!"{ppKey k} = {v}\n"
