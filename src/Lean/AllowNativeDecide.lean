/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude

public import Lean.Attributes

namespace Lean

builtin_initialize allowNativeDecideAttr : TagAttribute ←
  registerTagAttribute `allow_native_decide
    "mark definition as allowed to be used in `native_decide` computations"

@[export lean_has_disallowed_native_decide]
partial def hasDisallowedNativeDecide (kenv : Kernel.Environment) (n : Name) : Option Name :=
  let env := Environment.ofKernelEnv kenv
  go env n
where go (env : Environment) (n : Name) : Option Name := Id.run do
  let some c := kenv.find? n | return some n
  match c with
  | .defnInfo d =>
    if allowNativeDecideAttr.hasTag env d.name then
      none
    else if !n.isInternalDetail then
      some n
    else
      return d.value.foldConsts (init := none) (go env · <|> ·)
  | .ctorInfo _ => none
  | .inductInfo _ => none
  | c => some c.name
