/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Marc Huisinga
-/
import Lean.Data.Format
import Lean.Data.Json.Basic

namespace Lean
namespace Json

private def escapeAux (c : Char) (acc : String) : String :=
  -- escape ", \, \n and \r, keep all other characters ≥ 0x20 and render characters < 0x20 with \u
  if c = '"' then -- hack to prevent emacs from regarding the rest of the file as a string: "
    "\\\"" ++ acc
  else if c = '\\' then
    "\\\\" ++ acc
  else if c = '\n' then
    "\\n" ++ acc
  else if c = '\x0d' then
    "\\r" ++ acc
  -- the c.val ≤ 0x10ffff check is technically redundant,
  -- since Lean chars are unicode scalar values ≤ 0x10ffff.
  -- as to whether c.val > 0xffff should be split up and encoded with multiple \u,
  -- the JSON standard is not definite: both directly printing the character
  -- and encoding it with multiple \u is allowed, and it is up to parsers to make the
  -- decision.
  else if 0x0020 ≤ c.val ∧ c.val ≤ 0x10ffff then
    String.singleton c ++ acc
  else
    let n := c.toNat;
    -- since c.val < 0x20 in this case, this conversion is more involved than necessary
    -- (but we keep it for completeness)
    "\\u" ++
    [ Nat.digitChar (n / 4096),
      Nat.digitChar ((n % 4096) / 256),
      Nat.digitChar ((n % 256) / 16),
      Nat.digitChar (n % 16) ].asString ++
    acc

def escape (s : String) : String := do
  s.foldr escapeAux ""

def renderString (s : String) : String :=
  "\"" ++ escape s ++ "\""

section
@[specialize]
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
    let kvs := Format.joinSep (kvs.fold (fun acc k j => renderKV k j :: acc) []) ("," ++ Format.line);
    Format.bracket "{" kvs "}"
end

def pretty (j : Json) (lineWidth := 80) : String :=
  Format.pretty (render j) lineWidth

partial def compress : Json → String
  | null       => "null"
  | bool true  => "true"
  | bool false => "false"
  | num s      => s.toString
  | str s      => renderString s
  | arr elems  =>
    let f := ",".intercalate (elems.map compress).toList
    s!"[{f}]"
  | obj kvs    =>
    let ckvs := kvs.fold (fun acc k j => s!"{renderString k}:{compress j}" :: acc) []
    let ckvs := ",".intercalate ckvs
    s!"\{{ckvs}}"

instance : ToFormat Json := ⟨render⟩
instance : ToString Json := ⟨pretty⟩

end Json
end Lean
