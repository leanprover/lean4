/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Basic

namespace Lean.Compiler.LCNF

instance : Hashable Param where
  hash p := mixHash (hash p.fvarId) (hash p.type)

def hashParams (ps : Array Param) : UInt64 :=
  hash ps

mutual
partial def hashAlt (alt : Alt) : UInt64 :=
  match alt with
  | .alt ctorName ps k => mixHash (mixHash (hash ctorName) (hash ps)) (hashCode k)
  | .default k => hashCode k

partial def hashAlts (alts : Array Alt) : UInt64 :=
  alts.foldl (fun r a => mixHash r (hashAlt a)) 7

partial def hashCode (code : Code) : UInt64 :=
  match code with
  | .let decl k => mixHash (mixHash (hash decl.fvarId) (hash decl.type)) (mixHash (hash decl.value) (hashCode k))
  | .fun decl k | .jp decl k =>
    mixHash (mixHash (mixHash (hash decl.fvarId) (hash decl.type)) (mixHash (hashCode decl.value) (hashCode k))) (hash decl.params)
  | .return fvarId => hash fvarId
  | .unreach type => hash type
  | .jmp fvarId args => mixHash (hash fvarId) (hash args)
  | .cases c => mixHash (mixHash (hash c.discr) (hash c.resultType)) (hashAlts c.alts)

end

instance : Hashable Code where
  hash c := hashCode c

deriving instance Hashable for Decl

end Lean.Compiler.LCNF