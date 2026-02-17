/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.IR.Basic

public section

namespace Lean.IR

def ensureHasDefault (alts : Array Alt) : Array Alt :=
  if alts.any Alt.isDefault then alts
  else if alts.size < 2 then alts
  else
    let last := alts.back!
    let alts := alts.pop
    alts.push (Alt.default last.body)

end Lean.IR
