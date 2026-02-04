/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Marc Huisinga, Wojciech Nawrocki
-/
module

prelude
public import Lean.Data.Format
public import Lean.Data.Json.Basic
import Init.Data.String.Search
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.UInt.Lemmas
import Init.Omega

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
    0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
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

set_option maxRecDepth 10240 in
private def needEscape (s : String) : Bool :=
  go s 0
where
  go (s : String) (i : Nat) : Bool :=
    if h : i < s.utf8ByteSize then
      let byte := s.getUTF8Byte ⟨i⟩ h
      have h1 : byte.toNat < 256 := UInt8.toNat_lt_size byte
      have h2 : escapeTable.val.size = 256 := escapeTable.property
      if escapeTable.val.get byte.toNat (Nat.lt_of_lt_of_eq h1 h2.symm) == 0 then
        go s (i + 1)
      else
        true
    else
      false

@[inline]
def escape (s : String) (acc : String := "") : String :=
  -- If we don't have any characters that need to be escaped we can just append right away.
  if needEscape s then
    s.foldl escapeAux acc
  else
    acc ++ s

@[inline]
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

private inductive CompressWorkItemKind where
  | json
  | arrayElem
  | arrayEnd
  | objectField
  | objectEnd
  | comma

private structure CompressWorkItemQueue where
  kinds           : Array CompressWorkItemKind
  values          : Array Json
  objectFieldKeys : Array String

@[inline]
private def CompressWorkItemQueue.pushKind (q : CompressWorkItemQueue) (kind : CompressWorkItemKind) :
    CompressWorkItemQueue := {
  q with kinds := q.kinds.push kind
}

@[inline]
private def CompressWorkItemQueue.pushValue (q : CompressWorkItemQueue) (value : Json) :
    CompressWorkItemQueue := {
  q with values := q.values.push value
}

@[inline]
private def CompressWorkItemQueue.pushObjectFieldKey (q : CompressWorkItemQueue) (objectFieldKey : String) :
    CompressWorkItemQueue := {
  q with objectFieldKeys := q.objectFieldKeys.push objectFieldKey
}

@[inline]
private def CompressWorkItemQueue.popKind (q : CompressWorkItemQueue) (h : q.kinds.size ≠ 0) :
    CompressWorkItemKind × CompressWorkItemQueue :=
  let kind := q.kinds[q.kinds.size - 1]
  let q := { q with kinds := q.kinds.pop }
  (kind, q)

@[inline]
private def CompressWorkItemQueue.popValue! (q : CompressWorkItemQueue) :
    Json × CompressWorkItemQueue :=
  let value := q.values[q.values.size - 1]!
  let q := { q with values := q.values.pop }
  (value, q)

@[inline]
private def CompressWorkItemQueue.popObjectFieldKey! (q : CompressWorkItemQueue) :
    String × CompressWorkItemQueue :=
  let objectFieldKey := q.objectFieldKeys[q.objectFieldKeys.size - 1]!
  let q := { q with objectFieldKeys := q.objectFieldKeys.pop }
  (objectFieldKey, q)

partial def compress (j : Json) : String :=
  go "" {
    kinds := #[.json]
    values := #[j]
    objectFieldKeys := #[]
  }
where
  go (acc : String) (q : CompressWorkItemQueue) : String :=
    if h : q.kinds.size = 0 then
      acc
    else
      let (kind, q) := q.popKind h
      match kind with
      | .json =>
        let (j, q) := q.popValue!
        match j with
        | null =>
          go (acc ++ "null") q
        | bool b =>
          go (acc ++ toString b) q
        | num n =>
          go (acc ++ toString n) q
        | str s =>
          go (renderString s acc) q
        | arr elems =>
          let q := q.pushKind .arrayEnd
          go (acc ++ "[") (elems.foldr (init := q) fun e acc => acc.pushKind .arrayElem |>.pushValue e)
        | obj kvs =>
          let q := q.pushKind .objectEnd
          go (acc ++ "{") (kvs.foldr (init := q) fun k j acc => acc.pushKind .objectField |>.pushObjectFieldKey k |>.pushValue j)
      | .arrayElem =>
        let (j, q) := q.popValue!
        if h : q.kinds.size = 0 then
          go acc {
            kinds := #[.comma, .json]
            values := #[j]
            objectFieldKeys := #[]
          }
        else
          let kind := q.kinds[q.kinds.size - 1]
          if kind matches .arrayEnd then
            go acc (q.pushKind .json |>.pushValue j)
          else
            go acc (q.pushKind .comma |>.pushKind .json |>.pushValue j)
      | .arrayEnd =>
        go (acc ++ "]") q
      | .objectField =>
        let (k, q) := q.popObjectFieldKey!
        let (j, q) := q.popValue!
        if h : q.kinds.size = 0 then
          go (renderString k acc ++ ":") {
            kinds := #[.comma, .json]
            values := #[j]
            objectFieldKeys := #[]
          }
        else
          let kind := q.kinds[q.kinds.size - 1]
          if kind matches .objectEnd then
            go (renderString k acc ++ ":") (q.pushKind .json |>.pushValue j)
          else
            go (renderString k acc ++ ":") (q.pushKind .comma |>.pushKind .json |>.pushValue j)
      | .objectEnd =>
        go (acc ++ "}") q
      | .comma =>
        go (acc ++ ",") q

instance : ToFormat Json := ⟨render⟩
instance : ToString Json := ⟨pretty⟩

end Json
end Lean
