/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
prelude
import Lean.Data.Options

namespace Lean.Linter

register_builtin_option linter.all : Bool := {
  defValue := false
  descr := "enable all linters"
}

def getLinterAll (o : Options) (defValue := linter.all.defValue) : Bool := o.get linter.all.name defValue

def getLinterValue (opt : Lean.Option Bool) (o : Options) : Bool := o.get opt.name (getLinterAll o opt.defValue)
