/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Attributes

namespace Lean.Elab.Command

@[builtin_macro Lean.Parser.Command.mixfix] def expandMixfix : Macro := fun stx =>
  withAttrKindGlobal stx fun stx => do
    match stx with
    | `($[$doc?:docComment]? $[@[$attrs?,*]]? infixl:$prec $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      let prec1 := quote <| (← evalPrec prec) + 1
      `($[$doc?:docComment]? $[@[$attrs?,*]]? notation:$prec $[(name := $name)]? $[(priority := $prio)]? lhs:$prec $op:str rhs:$prec1 => $f lhs rhs)
    | `($[$doc?:docComment]? $[@[$attrs?,*]]? infix:$prec $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      let prec1 := quote <| (← evalPrec prec) + 1
      `($[$doc?:docComment]? $[@[$attrs?,*]]? notation:$prec $[(name := $name)]? $[(priority := $prio)]? lhs:$prec1 $op:str rhs:$prec1 => $f lhs rhs)
    | `($[$doc?:docComment]? $[@[$attrs?,*]]? infixr:$prec $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      let prec1 := quote <| (← evalPrec prec) + 1
      `($[$doc?:docComment]? $[@[$attrs?,*]]? notation:$prec $[(name := $name)]? $[(priority := $prio)]? lhs:$prec1 $op:str rhs:$prec => $f lhs rhs)
    | `($[$doc?:docComment]? $[@[$attrs?,*]]? prefix:$prec $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      `($[$doc?:docComment]? $[@[$attrs?,*]]? notation:$prec $[(name := $name)]? $[(priority := $prio)]? $op:str arg:$prec => $f arg)
    | `($[$doc?:docComment]? $[@[$attrs?,*]]? postfix:$prec $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      `($[$doc?:docComment]? $[@[$attrs?,*]]? notation:$prec $[(name := $name)]? $[(priority := $prio)]? arg:$prec $op:str => $f arg)
    | _ => Macro.throwUnsupported
where
  -- set "global" `attrKind`, apply `f`, and restore `attrKind` to result
  withAttrKindGlobal stx f := do
    let attrKind := stx[2]
    let stx  := stx.setArg 2 mkAttrKindGlobal
    let stx ← f stx
    return stx.raw.setArg 2 attrKind

end Lean.Elab.Command
