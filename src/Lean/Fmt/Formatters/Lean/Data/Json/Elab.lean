/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Data.Json.Elab
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Json.«termJson%_»]
public def fmtJsonTerm : Fmt := fun
  | `(json%%$jsonTk $json:json) => do
    let jsonTk ← fmt jsonTk
    let json ← fmt json
    return Layouts.pseudoApplication #[jsonTk, json]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Json.«json{_}»]
public def fmtJsonObject : Fmt := fun
  | `(json| {%$lbTk $fields:jsonField,* }%$rbTk) => do
    let lbTk ← fmt lbTk
    let fields ← fmtTSepArray fields
    let rbTk ← fmt rbTk
    let fields := Layouts.sepArray fields <| .joinUsingSep none nl
    return Layouts.bracketed lbTk fields rbTk <| .sparse nl (stickynessKind := .preferSticky)
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Json.jsonField]
public def fmtJsonField : Fmt := fun
  | `(Lean.Json.jsonField| $key:jsonIdent :%$colonTk $value:json) => do
    let key ← fmt key
    let colonTk ← fmt colonTk
    let value ← fmt value
    let lhs := Layouts.atomic #[hardNested key, colonTk]
    return maybeFlattened <| stickyCombine lhs ⟨nl, nested⟩ value
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Json.jsonIdent]
public def fmtJsonIdent : Fmt := fun
  | `(Lean.Json.jsonIdent| $key:ident) => fmt key
  | `(Lean.Json.jsonIdent| $key:str) => fmt key
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Json.«json[_]»]
public def fmtJsonArray : Fmt := fun
  | `(json| [%$lbTk $elems:json,* ]%$rbTk) => fmtArrayLit lbTk elems rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Json.«json-_»]
public def fmtJsonNum : Fmt := fun
  | `(json| $[-%$minusTk?]? $n:num) => do
    let minusTk? ← fmt? minusTk?
    let n ← fmt n
    return Layouts.prefixOperator minusTk? n .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Json.«json-__1»]
public def fmtJsonScientific : Fmt := fun
  | `(json| $[-%$minusTk?]? $n:scientific) => do
    let minusTk? ← fmt? minusTk?
    let n ← fmt n
    return Layouts.prefixOperator minusTk? n .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Json.json_]
public def fmtJsonStr : Fmt := fun
  | `(json| $s:str) => fmt s
  | _ => throw .partialFormatter
