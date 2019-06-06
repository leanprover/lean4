/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.attributes
import init.lean.compiler.util

namespace Lean
namespace Compiler

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

private partial def hasInlineAttrAux (env : Environment) (attr : TagAttribute) : Name → Bool
| n :=
  /- We never inline auxiliary declarations created by eager lambda lifting -/
  if isEagerLambdaLiftingName n then false
  else if attr.hasTag env n then true
  else if n.isInternal then hasInlineAttrAux n.getPrefix
  else false

@[export lean.has_inline_attribute_core]
def hasInlineAttribure (env : Environment) (n : Name) : Bool :=
hasInlineAttrAux env inlineAttribute n

@[export lean.has_inline_if_reduce_attribute_core]
def hasInlineIfReduceAttribure (env : Environment) (n : Name) : Bool :=
hasInlineAttrAux env inlineIfReduceAttribute n

@[export lean.has_noinline_attribute_core]
def hasNoInlineAttribure (env : Environment) (n : Name) : Bool :=
hasInlineAttrAux env noInlineAttribute n

@[export lean.has_macro_inline_attribute_core]
def hasMacroInlineAttribure (env : Environment) (n : Name) : Bool :=
hasInlineAttrAux env macroInlineAttribute n

end Compiler
end Lean
