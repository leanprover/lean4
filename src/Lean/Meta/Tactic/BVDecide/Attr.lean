/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Henrik Böving
-/
module

prelude
public import Lean.Elab.Tactic.Basic
public import Lean.Meta.Tactic.Simp
public import Std.Tactic.BVDecide.Syntax
public import Lean.Meta.Sym.Simp.Theorems
import Lean.Elab.ConfigEval
import Lean.Meta.Sym.Simp.Attr

public section

/-!
Provides environment extensions around the `bv_decide` tactic frontends.
-/

namespace Lean.Meta.Tactic.BVDecide

open Simp

builtin_initialize registerTraceClass `Meta.Tactic.sat
builtin_initialize registerTraceClass `Meta.Tactic.bv

register_builtin_option sat.solver : String := {
  defValue := ""
  descr :=
    "Name of the SAT solver used by Lean.Elab.Tactic.BVDecide tactics.\n
     1. If this is set to something besides the empty string they will use that binary.\n
     2. If this is set to the empty string they will check if there is a cadical binary next to the\
        executing program. Usually that program is going to be `lean` itself and we do ship a\
        `cadical` next to it.\n
     3. If that does not succeed try to call `cadical` from PATH. The empty string default indicates\
        to use the one that ships with Lean."
}

declare_config_elab elabBVDecideConfig Lean.Elab.Tactic.BVDecide.BVDecideConfig

builtin_initialize bvNormalizeExt : Sym.Simp.SymSimpExtension ←
  Sym.Simp.registerSymSimpAttr `bv_normalize "simp theorems used by bv_normalize"

def symIntToBitVecName : Name := `int_toBitVec_sym
def metaIntToBitVecName : Name := `int_toBitVec_meta

builtin_initialize symIntToBitVecExt : Sym.Simp.SymSimpExtension ←
  Sym.Simp.registerSymSimpAttr symIntToBitVecName "sym simp theorems used to convert UIntX/IntX statements into BitVec ones"

builtin_initialize metaIntToBitVecExt : Meta.SimpExtension ←
  Meta.registerSimpAttr metaIntToBitVecName "meta simp theorems used to convert UIntX/IntX statements into BitVec ones"

builtin_initialize
  registerBuiltinAttribute {
    name := `int_toBitVec
    descr := "simp theorems used to convert UIntX/IntX statements into BitVec ones"
    add := fun declName stx attrKind => do
      let env ← getEnv
      let metaImpl ← IO.ofExcept <| getAttributeImpl env metaIntToBitVecName
      metaImpl.add declName stx attrKind
      let symImpl ← IO.ofExcept <| getAttributeImpl env symIntToBitVecName
      symImpl.add declName stx attrKind
  }

end Lean.Meta.Tactic.BVDecide
