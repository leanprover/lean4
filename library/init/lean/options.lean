/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich and Leonardo de Moura
-/
prelude
import init.lean.kvmap init.io init.control.combinators init.data.tostring

namespace Lean

def Options := KVMap
namespace Options
def empty : Options  := {KVMap .}
instance : HasEmptyc Options := ⟨empty⟩
end Options

structure OptionDecl :=
(defValue : DataValue)
(descr    : String := "")

def OptionDecls := NameMap OptionDecl

private def initOptionDeclsRef : IO (IO.Ref OptionDecls) :=
IO.mkRef (mkNameMap OptionDecl)

@[init initOptionDeclsRef]
private constant optionDeclsRef : IO.Ref OptionDecls := default _

def registerOption (name : Name) (decl : OptionDecl) : IO Unit :=
do decls ← optionDeclsRef.get,
   when (decls.contains name) $ do {
     let msg := "invalid option declaration '" ++ toString name ++ "', option already exists",
     throw msg
   },
   optionDeclsRef.set $ decls.insert name decl

def getOptionDecls : IO OptionDecls := optionDeclsRef.get

end Lean
