/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment
import init.lean.attributes

namespace Lean

def mkInitAttr : IO (ParametricAttribute Name) :=
registerParametricAttribute `myInit "initialization procedure for global references" $ λ env declName stx,
  match stx with
  | Syntax.ident _ _ initFnName _ _ :=
    dbgTrace ("myInit " ++ toString initFnName) $ λ _, Except.ok initFnName
  | Syntax.missing := Except.error "invalid 'init' attribute, argument is missing"
  | _ := Except.error "invalid 'init' attribute, unexpected kind of argument"

@[init mkInitAttr]
constant initAttr : ParametricAttribute Name := default _

@[extern "lean_is_io_unit_init"]
constant isIOUnitInitFn (env : @& Environment) (fn : @& Name) : Bool := default _

@[extern "lean_get_init_fn_name_for"]
constant getInitFnNameFor (env : @& Environment) (fn : @& Name) : Option Name := default _

def hasInitAttr (env : Environment) (fn : Name) : Bool :=
(getInitFnNameFor env fn).isSome

end Lean
