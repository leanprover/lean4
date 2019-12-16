/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Environment

namespace Lean

/- We use aliases to implement the `export <id> (<id>+)` command. -/

abbrev AliasState := SMap Name (List Name)
abbrev AliasEntry := Name × Name

def addAliasEntry (s : AliasState) (e : AliasEntry) : AliasState :=
match s.find? e.1 with
| none    => s.insert e.1 [e.2]
| some es => if es.elem e.2 then s else s.insert e.1 (e.2 :: es)

def mkAliasExtension : IO (SimplePersistentEnvExtension AliasEntry AliasState) :=
registerSimplePersistentEnvExtension {
  name          := `aliasesExt,
  addEntryFn    := addAliasEntry,
  addImportedFn := fun es => (mkStateFromImportedEntries addAliasEntry {} es).switch
}

@[init mkAliasExtension]
constant aliasExtension : SimplePersistentEnvExtension AliasEntry AliasState := arbitrary _

/- Add alias `a` for `e` -/
def addAlias (env : Environment) (a : Name) (e : Name) : Environment :=
aliasExtension.addEntry env (a, e)

def getAliases (env : Environment) (a : Name) : List Name :=
match (aliasExtension.getState env).find? a with
| none    => []
| some es => es

end Lean
