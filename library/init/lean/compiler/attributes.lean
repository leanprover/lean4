/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.attributes

namespace Lean

private def checkIsDefinition (env : Environment) (n : Name) : Except String Unit :=
match env.find n with
| (some (ConstantInfo.defnInfo _)) := Except.ok ()
| none := Except.error "unknow declaration"
| _    := Except.error "declaration is not a definition"

def mkInlineAttribute : IO TagAttribute :=
registerTagAttribute `inline "mark definition to always be inlined" checkIsDefinition
@[init mkInlineAttribute] constant inlineAttribute : TagAttribute := default _

def mkInlineIfReduceAttribute : IO TagAttribute :=
registerTagAttribute `inlineIfReduce "mark definition to be inlined when resultant term after reduction is not a `cases_on` application." checkIsDefinition
@[init mkInlineIfReduceAttribute] constant inlineIfReduceAttribute : TagAttribute := default _

def mkNoInlineAttribute : IO TagAttribute :=
registerTagAttribute `noinline "mark definition to never be inlined" checkIsDefinition
@[init mkNoInlineAttribute] constant noInlineAttribute : TagAttribute := default _

def mkMacroInlineAttribute : IO TagAttribute :=
registerTagAttribute `macroInline "mark definition to always be inlined before ANF conversion" checkIsDefinition
@[init mkMacroInlineAttribute] constant macroInlineAttribute : TagAttribute := default _

end Lean
