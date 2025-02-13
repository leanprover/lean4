import Lean

open Lean Meta

-- without this, the catch below does not catch kernel errors
set_option Elab.async false

/--
info: Possible candidates for Init/Core.lean (these do not need to be added if they are irrelevant for verification):
gen_injective_theorems% MacroScopesView
gen_injective_theorems% ParserDescr
gen_injective_theorems% SourceInfo
gen_injective_theorems% TSyntax
gen_injective_theorems% Grind.Config
gen_injective_theorems% Macro.Context
gen_injective_theorems% Macro.Exception
gen_injective_theorems% Macro.Methods
gen_injective_theorems% Macro.State
gen_injective_theorems% Syntax.Preresolved
gen_injective_theorems% Syntax.SepArray
gen_injective_theorems% Syntax.TSepArray
gen_injective_theorems% Try.Config
gen_injective_theorems% Parser.Tactic.DecideConfig
-/
#guard_msgs in
run_meta
  let mut names := #[]
  for (name, ci) in (← getEnv).constants do
    let .inductInfo info := ci | continue
    if info.isUnsafe then continue
    if isClass (← getEnv) name then continue
    let bad ← do
      try
          let env0 ← getEnv
          mkInjectiveTheorems name
          let env1 ← getEnv
          if env1.constants.map₂.toArray.size > env0.constants.map₂.toArray.size then
            pure true
          else
            pure false
      catch _ =>
        pure false
    if bad then
      names := names.push name
  unless names.isEmpty do
    names := names.qsort Name.lt
    let mut msg := m!"Possible candidates for Init/Core.lean (these do not need to be added if they are irrelevant for verification):\n"
    for n in names do
      msg := msg ++ m!"gen_injective_theorems% {.ofConstName n}\n"
    logInfo msg
