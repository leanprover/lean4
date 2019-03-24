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
(group    : String := "")
(descr    : String := "")

def OptionDecls := NameMap OptionDecl

private def initOptionDeclsRef : IO (IO.Ref OptionDecls) :=
IO.mkRef (mkNameMap OptionDecl)

@[init initOptionDeclsRef]
private constant optionDeclsRef : IO.Ref OptionDecls := default _

def registerOption (name : Name) (decl : OptionDecl) : IO Unit :=
do decls ← optionDeclsRef.get,
   when (decls.contains name) $
     throw $ IO.userError ("invalid option declaration '" ++ toString name ++ "', option already exists"),
   optionDeclsRef.set $ decls.insert name decl

def getOptionDecls : IO OptionDecls := optionDeclsRef.get

def getOptionDecl (name : Name) : IO OptionDecl :=
do decls ← getOptionDecls,
   (some decl) ← pure (decls.find name) | throw $ IO.userError ("unknown option '" ++ toString name ++ "'"),
   pure decl

def getOptionDefaulValue (name : Name) : IO DataValue :=
do decl ← getOptionDecl name,
   pure decl.defValue

def getOptionDescr (name : Name) : IO String :=
do decl ← getOptionDecl name,
   pure decl.descr

def setOptionFromString (opts : Options) (entry : String) : IO Options :=
do let ps := (entry.split "=").map String.trim,
   [key, val] ← pure ps | throw "invalid configuration option entry, it must be of the form '<key> = <value>'",
   defValue ← getOptionDefaulValue key.toName,
   match defValue with
   | DataValue.ofString v := pure $ opts.setString key val
   | DataValue.ofBool v   :=
     if key == "true" then pure $ opts.setBool key true
     else if key == "false" then pure $ opts.setBool key false
     else throw $ IO.userError ("invalid Bool option value '" ++ val ++ "'")
   | DataValue.ofName v   := pure $ opts.setName key val.toName
   | DataValue.ofNat v    := do
     unless val.isNat $ throw (IO.userError ("invalid Nat option value '" ++ val ++ "'")),
     pure $ opts.setNat key val.toNat
   | DataValue.ofInt v    := do
     unless val.isInt $ throw (IO.userError ("invalid Int option value '" ++ val ++ "'")),
     pure $ opts.setInt key val.toInt

end Lean
