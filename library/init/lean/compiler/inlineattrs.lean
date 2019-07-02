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

inductive InlineAttributeKind
| inline | noinline | macroInline | inlineIfReduce

namespace InlineAttributeKind

instance : Inhabited InlineAttributeKind := ⟨InlineAttributeKind.inline⟩

protected def beq : InlineAttributeKind → InlineAttributeKind → Bool
| inline inline := true
| noinline noinline := true
| macroInline macroInline := true
| inlineIfReduce inlineIfReduce := true
| _ _ := false

instance : HasBeq InlineAttributeKind := ⟨InlineAttributeKind.beq⟩

end InlineAttributeKind

def mkInlineAttrs : IO (EnumAttributes InlineAttributeKind) :=
registerEnumAttributes `inlineAttrs
  [(`inline, "mark definition to always be inlined", InlineAttributeKind.inline),
   (`inlineIfReduce, "mark definition to be inlined when resultant term after reduction is not a `cases_on` application", InlineAttributeKind.inlineIfReduce),
   (`noinline, "mark definition to never be inlined", InlineAttributeKind.noinline),
   (`macroInline, "mark definition to always be inlined before ANF conversion", InlineAttributeKind.macroInline)]
  (fun env declName _ => checkIsDefinition env declName)

@[init mkInlineAttrs]
constant inlineAttrs : EnumAttributes InlineAttributeKind := default _

private partial def hasInlineAttrAux (env : Environment) (kind : InlineAttributeKind) : Name → Bool
| n :=
  /- We never inline auxiliary declarations created by eager lambda lifting -/
  if isEagerLambdaLiftingName n then false
  else match inlineAttrs.getValue env n with
    | some k := kind == k
    | none   := if n.isInternal then hasInlineAttrAux n.getPrefix else false

@[export lean.has_inline_attribute_core]
def hasInlineAttribute (env : Environment) (n : Name) : Bool :=
hasInlineAttrAux env InlineAttributeKind.inline n

@[export lean.has_inline_if_reduce_attribute_core]
def hasInlineIfReduceAttribute (env : Environment) (n : Name) : Bool :=
hasInlineAttrAux env InlineAttributeKind.inlineIfReduce n

@[export lean.has_noinline_attribute_core]
def hasNoInlineAttribute (env : Environment) (n : Name) : Bool :=
hasInlineAttrAux env InlineAttributeKind.noinline n

@[export lean.has_macro_inline_attribute_core]
def hasMacroInlineAttribute (env : Environment) (n : Name) : Bool :=
hasInlineAttrAux env InlineAttributeKind.macroInline n

end Compiler
end Lean
