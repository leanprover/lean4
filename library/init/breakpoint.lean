/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.attribute init.meta.constructor_tactic

namespace debugger

def attr : user_attribute :=
{ name  := `breakpoint,
  descr := "breakpoint for debugger" }

end debugger

run_command attribute.register `debugger.attr
