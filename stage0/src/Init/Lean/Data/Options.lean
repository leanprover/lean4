/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich and Leonardo de Moura
-/
prelude
import Init.System.IO
import Init.Data.Array
import Init.Data.ToString
import Init.Lean.Data.KVMap

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
private constant optionDeclsRef : IO.Ref OptionDecls := arbitrary _

@[export lean_register_option]
def registerOption (name : Name) (decl : OptionDecl) : IO Unit :=
do decls ← optionDeclsRef.get;
   when (decls.contains name) $
     throw $ IO.userError ("invalid option declaration '" ++ toString name ++ "', option already exists");
   optionDeclsRef.set $ decls.insert name decl

def getOptionDecls : IO OptionDecls := optionDeclsRef.get

@[export lean_get_option_decls_array]
def getOptionDeclsArray : IO (Array (Name × OptionDecl)) :=
do decls ← getOptionDecls;
   pure $ decls.fold
    (fun (r : Array (Name × OptionDecl)) k v => r.push (k, v))
    #[]

def getOptionDecl (name : Name) : IO OptionDecl :=
do decls ← getOptionDecls;
   (some decl) ← pure (decls.find name) | throw $ IO.userError ("unknown option '" ++ toString name ++ "'");
   pure decl

def getOptionDefaulValue (name : Name) : IO DataValue :=
do decl ← getOptionDecl name;
   pure decl.defValue

def getOptionDescr (name : Name) : IO String :=
do decl ← getOptionDecl name;
   pure decl.descr

def setOptionFromString (opts : Options) (entry : String) : IO Options :=
do let ps := (entry.splitOn "=").map String.trim;
   [key, val] ← pure ps | throw "invalid configuration option entry, it must be of the form '<key> = <value>'";
   defValue ← getOptionDefaulValue key.toName;
   match defValue with
   | DataValue.ofString v => pure $ opts.setString key val
   | DataValue.ofBool v   =>
     if key == "true" then pure $ opts.setBool key true
     else if key == "false" then pure $ opts.setBool key false
     else throw $ IO.userError ("invalid Bool option value '" ++ val ++ "'")
   | DataValue.ofName v   => pure $ opts.setName key val.toName
   | DataValue.ofNat v    => do
     unless val.isNat $ throw (IO.userError ("invalid Nat option value '" ++ val ++ "'"));
     pure $ opts.setNat key val.toNat
   | DataValue.ofInt v    => do
     unless val.isInt $ throw (IO.userError ("invalid Int option value '" ++ val ++ "'"));
     pure $ opts.setInt key val.toInt

@[init] def verboseOption : IO Unit :=
registerOption `verbose { defValue := true, group := "", descr := "disable/enable verbose messages" }

@[init] def timeoutOption : IO Unit :=
registerOption `timeout { defValue := DataValue.ofNat 0, group := "", descr := "the (deterministic) timeout is measured as the maximum of memory allocations (in thousands) per task, the default is unbounded" }

@[init] def maxMemoryOption : IO Unit :=
registerOption `maxMemory { defValue := DataValue.ofNat 2048, group := "", descr := "maximum amount of memory available for Lean in megabytes" }

end Lean
