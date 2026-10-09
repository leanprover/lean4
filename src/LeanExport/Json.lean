/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Marc Huisinga, Joachim Breitner
-/
module

prelude
public import Lean.Data.Json.Parser

/-!
# Strict JSON parser for the export format

A copy of the value parser from `Lean.Data.Json.Parser` that rejects objects with duplicate keys.
This duplication is provisional: the check should move into `Lean.Json.parse` once its impact on
the other users of `Lean.Json` has been assessed.
-/

public section

open Std.Internal.Parsec Std.Internal.Parsec.String Lean

namespace LeanExport.Json

mutual

  partial def arrayCore (acc : Array Json) : Parser (Array Json) := do
    let hd ← anyCore
    let acc' := acc.push hd
    let c ← any
    if c == ']' then
      ws
      return acc'
    else if c == ',' then
      ws
      arrayCore acc'
    else
      fail "unexpected character in array"

  partial def objectCore (kvs : Std.TreeMap.Raw String Json) :
      Parser (Std.TreeMap.Raw String Json) := do
    Json.Parser.lookahead (fun c => c == '"') "\""; skip;
    let k ← Json.Parser.str; ws
    if kvs.contains k then fail s!"duplicate object key {k.quote}"
    Json.Parser.lookahead (fun c => c == ':') ":"; skip; ws
    let v ← anyCore
    let c ← any
    if c == '}' then
      ws
      return kvs.insert k v
    else if c == ',' then
      ws
      objectCore (kvs.insert k v)
    else
      fail "unexpected character in object"

  partial def anyCore : Parser Json := do
    let c ← peek!
    if c == '[' then
      skip; ws
      let c ← peek!
      if c == ']' then
        skip; ws
        return Json.arr (Array.mkEmpty 0)
      else
        let a ← arrayCore (Array.mkEmpty 4)
        return Json.arr a
    else if c == '{' then
      skip; ws
      let c ← peek!
      if c == '}' then
        skip; ws
        return Json.obj ∅
      else
        let kvs ← objectCore ∅
        return Json.obj kvs
    else if c == '\"' then
      skip
      let s ← Json.Parser.str
      ws
      return Json.str s
    else if c == 'f' then
      skipString "false"; ws
      return Json.bool false
    else if c == 't' then
      skipString "true"; ws
      return Json.bool true
    else if c == 'n' then
      skipString "null"; ws
      return Json.null
    else if c == '-' || ('0' <= c && c <= '9') then
      let n ← Json.Parser.num
      ws
      return Json.num n
    else
      fail "unexpected input"

end

def parse (s : String) : Except String Json :=
  Parser.run (ws *> anyCore <* eof) s

end LeanExport.Json
