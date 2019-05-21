/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment

namespace Lean
@[extern "lean_get_init_fn_name_for"]
constant getInitFnNameFor (env : @& Environment) (fn : @& Name) : Option Name := default _

def hasInitAttr (env : Environment) (fn : Name) : Bool :=
(getInitFnNameFor env fn).isSome

end Lean
