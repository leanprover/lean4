/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Init.NotationExtra
meta import Std.Internal.Order.Basic
import Init.Data

namespace Lean.Fmt

open Lean.Order in
@[builtin_quantifier_fmt Lean.Order.«term⨅_,_»]
public def fmtIInf : QuantifierFmt := fun
  | `(⨅%$iInfTk $bs:explicitBinders ,%$commaTk $body:term) =>
    some {
      quantifier := iInfTk
      binders := .binders #[#[explicitBindersToGroup bs]]
      typeAscriptionTk? := none
      type? := none
      commaTk
      body
    }
  | _ =>
    none

open Lean.Order in
@[builtin_quantifier_fmt Lean.Order.«term⨆_,_»]
public def fmtISup : QuantifierFmt := fun
  | `(⨆%$iSupTk $bs:explicitBinders ,%$commaTk $body:term) =>
    some {
      quantifier := iSupTk
      binders := .binders #[#[explicitBindersToGroup bs]]
      typeAscriptionTk? := none
      type? := none
      commaTk
      body
    }
  | _ =>
    none
