/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Parser.Extra
public import Lean.Fmt.FmtM.Basic
meta import Lean.Parser.Term
meta import Lean.Parser.Extra
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt hygieneInfo]
public def fmtHygieneInfo : Fmt := fun _ => return empty

@[builtin_fmt hexnum]
public def fmtHexnum : Fmt := fmtAtomic

@[builtin_fmt Lean.«termRegister_parser_alias(Kind:=_)______»]
public def fmtRegisterParserAlias : Fmt := fun
  | `(register_parser_alias%$registerTk $[(%$lbTk? kind%$kindTk? :=%$colonEqTk? $kind?:term )%$rbTk?]?
      $[$aliasName?:str]? $declName:ident $[$info?:term]?) => do
    let registerTk ← fmt registerTk
    let namedKind? ← fmtNamedArgumentTerm? lbTk? kindTk? colonEqTk? kind? rbTk?
    let aliasName? ← fmt? aliasName?
    let declName ← fmt declName
    let info? ← fmt? info?
    let registration := Layouts.pseudoApplication #[registerTk, namedKind?]
    return Layouts.pseudoApplication #[registration, aliasName?, declName, info?]
  | _ => throw .partialFormatter
