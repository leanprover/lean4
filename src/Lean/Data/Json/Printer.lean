/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Marc Huisinga, Wojciech Nawrocki
-/
module

prelude
public import Lean.Data.Format
public import Lean.Data.Json.Basic
public import Init.Data.List.Impl

public section

namespace Lean
namespace Json

set_option maxRecDepth 1024 in
/--
This table contains for each UTF-8 byte whether we need to escape a string that contains it.
-/
private def escapeTable : { xs : ByteArray // xs.size = 256 } :=
  ⟨ByteArray.mk #[
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1
  ], by rfl⟩

private def escapeAux (acc : String) (c : Char) : String :=
  -- escape ", \, \n and \r, keep all other characters ≥ 0x20 and render characters < 0x20 with \u
  if c = '"' then -- hack to prevent emacs from regarding the rest of the file as a string: "
    acc ++ "\\\""
  else if c = '\\' then
    acc ++ "\\\\"
  else if c = '\n' then
    acc ++ "\\n"
  else if c = '\x0d' then
    acc ++ "\\r"
  -- the c.val ≤ 0x10ffff check is technically redundant,
  -- since Lean chars are unicode scalar values ≤ 0x10ffff.
  -- as to whether c.val > 0xffff should be split up and encoded with multiple \u,
  -- the JSON standard is not definite: both directly printing the character
  -- and encoding it with multiple \u is allowed, and it is up to parsers to make the
  -- decision.
  else if 0x0020 ≤ c.val ∧ c.val ≤ 0x10ffff then
    acc.push c
  else
    let n := c.toNat;
    -- since c.val < 0x20 in this case, this conversion is more involved than necessary
    -- (but we keep it for completeness)
    let d1 := Nat.digitChar (n / 4096)
    let d2 := Nat.digitChar ((n % 4096) / 256)
    let d3 := Nat.digitChar ((n % 256) / 16)
    let d4 := Nat.digitChar (n % 16)
    acc ++ "\\u" |>.push d1 |>.push d2 |>.push d3 |>.push d4

private def needEscape (s : String) : Bool :=
  go s 0
where
  go (s : String) (i : Nat) : Bool :=
    if h : i < s.utf8ByteSize then
      let byte := s.getUtf8Byte i h
      have h1 : byte.toNat < 256 := UInt8.toNat_lt_size byte
      have h2 : escapeTable.val.size = 256 := escapeTable.property
      if escapeTable.val.get byte.toNat (Nat.lt_of_lt_of_eq h1 h2.symm) == 0 then
        go s (i + 1)
      else
        true
    else
      false

def escape (s : String) (acc : String := "") : String :=
  -- If we don't have any characters that need to be escaped we can just append right away.
  if needEscape s then
    s.foldl escapeAux acc
  else
    acc ++ s

def renderString (s : String) (acc : String := "") : String :=
  let acc := acc ++ "\""
  let acc := escape s acc
  acc ++ "\""

section

partial def render : Json → Format
  | null       => "null"
  | bool true  => "true"
  | bool false => "false"
  | num s      => s.toString
  | str s      => renderString s
  | arr elems  =>
    let elems := Format.joinSep (elems.map render).toList ("," ++ Format.line);
    Format.bracket "[" elems "]"
  | obj kvs =>
    let renderKV : String → Json → Format := fun k v =>
      Format.group (renderString k ++ ":" ++ Format.line ++ render v);
    let kvs := Format.joinSep (kvs.foldl (fun acc k j => renderKV k j :: acc) []) ("," ++ Format.line);
    Format.bracket "{" kvs "}"
end

def pretty (j : Json) (lineWidth := 80) : String :=
  Format.pretty (render j) lineWidth

protected inductive CompressWorkItem
  | json (j : Json)
  | arrayElem (j : Json)
  | arrayEnd
  | objectField (k : String) (j : Json)
  | objectEnd
  | comma

open Json.CompressWorkItem in
partial def compress (j : Json) : String :=
  go "" #[json j]
where
  go (acc : String) (workItems : Array Json.CompressWorkItem) : String :=
    if h : workItems.size = 0 then
      acc
    else
      let workItem := workItems[workItems.size - 1]
      let workItems := workItems.pop
      match workItem with
      | json j =>
        match j with
        | null =>
          go (acc ++ "null") workItems
        | bool b =>
          go (acc ++ toString b) workItems
        | num n =>
          go (acc ++ toString n) workItems
        | str s =>
          go (renderString s acc) workItems
        | arr elems =>
          go (acc ++ "[") (workItems.push arrayEnd ++ elems.reverse.map arrayElem)
        | obj kvs =>
          let workItems := workItems.push objectEnd
          go (acc ++ "{") (kvs.foldr (init := workItems) fun k j acc => acc.push (objectField k j))
      | arrayElem j =>
        if h : workItems.size = 0 then
          go acc #[comma, json j]
        else
          let workItem := workItems[workItems.size - 1]
          if workItem matches arrayEnd then
            go acc (workItems.pop ++ #[arrayEnd, json j])
          else
            go acc (workItems ++ #[comma, json j])
      | arrayEnd =>
        go (acc ++ "]") workItems
      | objectField k j =>
        if h : workItems.size = 0 then
          go (renderString k acc ++ ":") #[comma, json j]
        else
          let workItem := workItems[workItems.size - 1]
          if workItem matches objectEnd then
            go (renderString k acc ++ ":") (workItems.pop ++ #[objectEnd, json j])
          else
            go (renderString k acc ++ ":") (workItems ++ #[comma, json j])
      | objectEnd =>
        go (acc ++ "}") workItems
      | comma =>
        go (acc ++ ",") workItems


instance : ToFormat Json := ⟨render⟩
instance : ToString Json := ⟨pretty⟩

end Json
end Lean
