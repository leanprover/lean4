/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
prelude
import Lean.Data.Options
import Lean.Log

namespace Lean.Linter

register_builtin_option linter.all : Bool := {
  defValue := false
  descr := "enable all linters"
}

def getLinterAll (o : Options) (defValue := linter.all.defValue) : Bool := o.get linter.all.name defValue

def getLinterValue (opt : Lean.Option Bool) (o : Options) : Bool := o.get opt.name (getLinterAll o opt.defValue)

def logLint [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (linterOption : Lean.Option Bool) (stx : Syntax) (msg : MessageData) : m Unit :=
  let disable := m!"note: this linter can be disabled with `set_option {linterOption.name} false`"
  logWarningAt stx (.tagged linterOption.name m!"{msg}\n{disable}")

/--
If `linterOption` is enabled, print a linter warning message at the position determined by `stx`.

Whether a linter option is enabled or not is determined by the following sequence:
1. If it is set, then the value determines whether or not it is enabled.
2. Otherwise, if `linter.all` is set, then its value determines whether or not the option is enabled.
3. Otherwise, the default value determines whether or not it is enabled.
-/
def logLintIf [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (linterOption : Lean.Option Bool) (stx : Syntax) (msg : MessageData) : m Unit := do
  if getLinterValue linterOption (← getOptions) then logLint linterOption stx msg
