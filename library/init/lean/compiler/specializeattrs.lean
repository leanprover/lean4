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

inductive SpecializeAttributeKind
| specialize | nospecialize

namespace SpecializeAttributeKind

instance : Inhabited SpecializeAttributeKind := ⟨SpecializeAttributeKind.specialize⟩

protected def beq : SpecializeAttributeKind → SpecializeAttributeKind → Bool
| specialize specialize := true
| nospecialize nospecialize := true
| _ _ := false

instance : HasBeq SpecializeAttributeKind := ⟨SpecializeAttributeKind.beq⟩

end SpecializeAttributeKind

def mkSpecializeAttrs : IO (EnumAttributes SpecializeAttributeKind) :=
registerEnumAttributes `specializeAttrs
  [(`specialize, "mark definition to always be inlined", SpecializeAttributeKind.specialize),
   (`nospecialize, "mark definition to never be inlined", SpecializeAttributeKind.nospecialize) ]
  (λ env declName _, checkIsDefinition env declName)

@[init mkSpecializeAttrs]
constant specializeAttrs : EnumAttributes SpecializeAttributeKind := default _

private partial def hasSpecializeAttrAux (env : Environment) (kind : SpecializeAttributeKind) : Name → Bool
| n := match specializeAttrs.getValue env n with
  | some k := kind == k
  | none   := if n.isInternal then hasSpecializeAttrAux n.getPrefix else false

@[export lean.has_specialize_attribute_core]
def hasSpecializeAttribute (env : Environment) (n : Name) : Bool :=
hasSpecializeAttrAux env SpecializeAttributeKind.specialize n

@[export lean.has_nospecialize_attribute_core]
def hasNospecializeAttribute (env : Environment) (n : Name) : Bool :=
hasSpecializeAttrAux env SpecializeAttributeKind.nospecialize n

end Compiler
end Lean
