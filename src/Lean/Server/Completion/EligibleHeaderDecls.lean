/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Meta.CompletionName
public import Lean.Data.Lsp.LanguageFeatures
public import Lean.AddDecl
public import Lean.ProjFns
public import Std.Sync.Mutex
import Lean.Linter.Deprecated
public section

namespace Lean.Server.Completion
open Meta

structure EligibleDecl where
  info : ConstantInfo
  kind : MetaM Lsp.CompletionItemKind
  tags : MetaM (Array Lsp.CompletionItemTag)

abbrev EligibleHeaderDecls := Std.HashMap Name EligibleDecl

/-- Cached header declarations for which `allowCompletion headerEnv decl` is true. -/
builtin_initialize eligibleHeaderDeclsMutex : Std.Mutex (Option EligibleHeaderDecls) ←
  Std.Mutex.new none

def getCompletionKindForDecl (constInfo : ConstantInfo)
    : MetaM Lsp.CompletionItemKind := do
  let env ← getEnv
  if constInfo.isCtor then
    return .constructor
  else if constInfo.isInductive then
    if isClass env constInfo.name then
      return .class
    else if (← isEnumType constInfo.name) then
      return .enum
    else
      return .struct
  else if wasOriginallyTheorem env constInfo.name then
    return .event
  else if (← isProjectionFn constInfo.name) then
    return .field
  else
    let isFunction : Bool ← withTheReader Core.Context ({ · with maxHeartbeats := 0 }) do
      return (← whnf constInfo.type).isForall
    if isFunction then
      return .function
    else
      return .constant

def getCompletionTagsForDecl (declName : Name) : MetaM (Array Lsp.CompletionItemTag) := do
  if Linter.isDeprecated (← getEnv) declName then
    return #[.deprecated]
  else
    return #[]

/--
Returns the declarations in the header for which `allowCompletion env decl` is true, caching them
if not already cached.
-/
def getEligibleHeaderDecls (env : Environment) : MetaM EligibleHeaderDecls := do
  eligibleHeaderDeclsMutex.atomically do
    match ← get with
    | some eligibleHeaderDecls =>
      return eligibleHeaderDecls
    | none =>
      let mut eligibleHeaderDecls : EligibleHeaderDecls := {}
      -- map₁ are the header decls
      for (declName, c) in env.constants.map₁ do
        if allowCompletion env declName then
          let kind ← getCompletionKindForDecl c
          let tags ← getCompletionTagsForDecl declName
          eligibleHeaderDecls := eligibleHeaderDecls.insert declName {
            info := c
            kind := pure kind
            tags := pure tags
          }
      set <| some eligibleHeaderDecls
      return eligibleHeaderDecls

/-- Iterate over all declarations that are allowed in completion results. -/
def forEligibleDeclsM [Monad m] [MonadEnv m] [MonadLiftT MetaM m]
    (f : Name → EligibleDecl → m PUnit) : m PUnit := do
  let env ← getEnv
  (← getEligibleHeaderDecls env).forM f
  -- map₂ are exactly the local decls
  env.constants.map₂.forM fun name c => do
    if allowCompletion env name then
      f name {
        info := c
        -- Lazily compute the kind and the tags when needed.
        kind := getCompletionKindForDecl c
        tags := getCompletionTagsForDecl name
      }

/-- Checks whether this declaration can appear in completion results. -/
def allowCompletion (eligibleHeaderDecls : EligibleHeaderDecls) (env : Environment)
    (declName : Name) : Bool :=
  eligibleHeaderDecls.contains declName ||
    env.constants.map₂.contains declName && Lean.Meta.allowCompletion env declName

end Lean.Server.Completion
