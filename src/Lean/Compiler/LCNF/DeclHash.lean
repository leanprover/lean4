/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.Basic

public section

namespace Lean.Compiler.LCNF

instance : Hashable (Param pu) where
  hash p := mixHash (hash p.fvarId) (hash p.type)

def hashParams (ps : Array (Param pu)) : UInt64 :=
  hash ps

mutual
partial def hashAlt (alt : Alt pu) : UInt64 :=
  match alt with
  | .alt ctorName ps k _ => mixHash (mixHash (hash ctorName) (hash ps)) (hashCode k)
  | .default k => hashCode k
  | .ctorAlt info k _ => mixHash (hash info) (hashCode k)

partial def hashAlts (alts : Array (Alt pu)) : UInt64 :=
  alts.foldl (fun r a => mixHash r (hashAlt a)) 7

partial def hashCode (code : Code pu) : UInt64 :=
  match code with
  | .let decl k => mixHash (mixHash (hash decl.fvarId) (hash decl.type)) (mixHash (hash decl.value) (hashCode k))
  | .fun decl k _ | .jp decl k =>
    mixHash (mixHash (mixHash (hash decl.fvarId) (hash decl.type)) (mixHash (hashCode decl.value) (hashCode k))) (hash decl.params)
  | .return fvarId => hash fvarId
  | .unreach type => hash type
  | .jmp fvarId args => mixHash (hash fvarId) (hash args)
  | .cases c => mixHash (mixHash (hash c.discr) (hash c.resultType)) (hashAlts c.alts)
  | .sset fvarId i offset y ty k _ =>
    mixHash (mixHash (hash fvarId) (hash i)) (mixHash (mixHash (hash offset) (hash y)) (mixHash (hash ty) (hashCode k)))
  | .uset fvarId offset y k _ =>
    mixHash (mixHash (hash fvarId) (hash offset)) (mixHash (hash y) (hashCode k))

end

instance : Hashable (Code pu) where
  hash c := hashCode c

deriving instance Hashable for DeclValue
deriving instance Hashable for Signature
deriving instance Hashable for Decl

end Lean.Compiler.LCNF
