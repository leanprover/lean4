/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Attributes

namespace Lean.Elab.Command

@[builtinMacro Lean.Parser.Command.mixfix] def expandMixfix : Macro := fun stx =>
  withAttrKindGlobal stx fun stx => do
    match stx with
    | `(infixl:$prec $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      let prec1 := quote <| (← evalPrec prec) + 1
      `(notation:$prec $[(name := $name)]? $[(priority := $prio)]? lhs:$prec $op:strLit rhs:$prec1 => $f lhs rhs)
    | `(infix:$prec $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      let prec1 := quote <| (← evalPrec prec) + 1
      `(notation:$prec $[(name := $name)]? $[(priority := $prio)]? lhs:$prec1 $op:strLit rhs:$prec1 => $f lhs rhs)
    | `(infixr:$prec $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      let prec1 := quote <| (← evalPrec prec) + 1
      `(notation:$prec $[(name := $name)]? $[(priority := $prio)]? lhs:$prec1 $op:strLit rhs:$prec => $f lhs rhs)
    | `(prefix:$prec $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      `(notation:$prec $[(name := $name)]? $[(priority := $prio)]? $op:strLit arg:$prec => $f arg)
    | `(postfix:$prec $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      `(notation:$prec $[(name := $name)]? $[(priority := $prio)]? arg:$prec $op:strLit => $f arg)
    | _ => Macro.throwUnsupported
where
  -- set "global" `attrKind`, apply `f`, and restore `attrKind` to result
  withAttrKindGlobal stx f := do
    let attrKind := stx[0]
    let stx  := stx.setArg 0 mkAttrKindGlobal
    let stx ← f stx
    return stx.setArg 0 attrKind

end Lean.Elab.Command
