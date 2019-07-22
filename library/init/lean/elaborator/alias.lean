/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment

namespace Lean

/- We use aliases to implement the `export <id> (<id>+)` command. -/

abbrev AliasState := SMap Name Name Name.quickLt
abbrev AliasEntry := Name × Name

def addAliasEntry (s : AliasState) (e : AliasEntry) : AliasState := s.insert e.1 e.2

def mkAliasExtension : IO (SimplePersistentEnvExtension AliasEntry AliasState) :=
registerSimplePersistentEnvExtension {
  name          := `aliasesExt,
  addEntryFn    := addAliasEntry,
  addImportedFn := fun es => (mkStateFromImportedEntries addAliasEntry {} es).switch
}

@[init mkAliasExtension]
constant aliasExtension : SimplePersistentEnvExtension AliasEntry AliasState := default _

/- Add alias `a` for `e` -/
def addAlias (env : Environment) (a : Name) (e : Name) : Environment :=
aliasExtension.addEntry env (a, e)

def isAlias (env : Environment) (a : Name) : Option Name :=
(aliasExtension.getState env).find a

end Lean
