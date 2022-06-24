/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser.Command

open Lean
namespace Lake

class DynamicType {α : Type u} (Δ : α → Type v) (a : α) (β : outParam $ Type v) : Prop where
  eq_dynamic_type : Δ a = β

export DynamicType (eq_dynamic_type)

@[inline] def toDynamic (a : α) [DynamicType Δ a β] (b : β) : Δ a :=
  cast eq_dynamic_type.symm b

@[inline] def ofDynamic (a : α) [DynamicType Δ a β] (b : Δ a) : β :=
  cast eq_dynamic_type b

/--
The syntax:

```lean
dynamic_data foo : Data 0 := Nat
```

Declares a new alternative for the dynamic `Data` type via the
production of an axiom `foo : Data 0 = Nat` and an instance of `DynamicType`
that uses this axiom for key `0`.
-/
scoped macro (name := dynamicDataDecl) doc?:optional(Parser.Command.docComment)
"dynamic_data " id:ident " : " dty:ident key:term " := " ty:term : command => do
  let tid := extractMacroScopes dty.getId |>.name
  if let (tid, _) :: _ ← Macro.resolveGlobalName tid then
    let app := Syntax.mkApp dty #[key]
    let axm := mkIdentFrom dty <| `_root_ ++ tid ++ id.getId
    `($[$doc?]? @[simp] axiom $axm : $app = $ty
    instance : DynamicType $dty $key $ty := ⟨$axm⟩)
  else
    Macro.throwErrorAt dty s!"unknown identifier '{tid}'"
