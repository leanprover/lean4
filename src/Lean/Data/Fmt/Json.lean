/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Data.Fmt.Formatter
public import Lean.Data.Json

public section

namespace Lean.Fmt.Json

def isPrimitive (j : Json) : Bool :=
  match j with
  | .arr .. => false
  | .obj .. => false
  | _ => true

partial def format (j : Json) : Doc :=
  match j with
  | .null => .text "null"
  | .bool b => .text (toString b)
  | .num n => .text (toString n)
  | .str s => .join #[.text "\"", .text s, .text "\""]
  | .arr a =>
    let elems := a.map format
    if a.all isPrimitive then
      .join #[
        .text "[",
        .aligned
          (.fillUsing (.text ", ") elems),
        .text "]"
      ]
    else
      .join #[
        .text "[",
        .indented 2
          (.append
            .hardNl
            (.joinUsing
              (.append (.text ",") .hardNl)
              elems)),
        .hardNl,
        .text "]"
      ]
  | .obj kv =>
    let pairs := kv.toArray.map fun (k, v) => formatKvPair k v
    .join #[
      .text "{",
      .indented 2
        (.append
          .hardNl
          (.joinUsing
            (.append (.text ",") .hardNl)
            pairs)),
      .hardNl,
      .text "}"
    ]
where
  formatKvPair (k : String) (v : Json) : Doc :=
    let v' := format v
    let f1 := .join #[
      .text "\"",
      .text k,
      .text "\": ",
      v'
    ]
    if isPrimitive v then
      let f2 := .join #[
        .text "\"",
        .text k,
        .text "\":",
        .indented 2 (.append .hardNl v')
      ]
      .either f1 f2
    else
      f1
