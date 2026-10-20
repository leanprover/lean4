/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Lean.ResolveName
public import Lean.Linter.Init

public section

namespace Lean.Linter

register_builtin_option linter.ambiguousOpen : Bool := {
  defValue := true
  descr := "if true, warn when the namespace of an `open` declaration could also refer to a \
    namespace that is silently not opened, e.g. `open B` inside `namespace A` only opens `A.B` \
    even if the namespace `B` exists as well"
}

/--
Collects all namespaces `p ++ id` where `p` is a prefix of `ns` (innermost first, ending with the
root namespace). Unlike `ResolveName.resolveNamespaceUsingScope?`, this collects every match
instead of only the innermost one, so that namespaces shadowed by the scope search are found.
-/
private def scopeCandidates (env : Environment) (id : Name) : Name → List Name
  | ns@(.str p _) =>
    let rest := scopeCandidates env id p
    if env.isNamespace (ns ++ id) then (ns ++ id) :: rest else rest
  | _ =>
    let id := id.replacePrefix rootNamespace .anonymous
    if env.isNamespace id then [id] else []

/--
Warns if the namespace identifier `nsStx` of an `open` declaration can also be interpreted as an
existing namespace that the `open` declaration silently does not open. `resolved` must be the
interpretations the `open` declaration actually uses, as returned by `resolveNamespace`.
Shadowed interpretations whose declarations are accessible anyway — because the namespace is
already opened without exceptions or encloses the current scope — are not reported.
-/
def checkAmbiguousOpen [Monad m] [MonadEnv m] [MonadOptions m] [MonadLog m]
    [AddMessageContext m] [MonadResolveName m] (nsStx : Ident) (resolved : List Name) : m Unit := do
  unless getLinterValue linter.ambiguousOpen (← getLinterOptions) do return
  let .ident info _ id preresolved := nsStx.raw | return
  -- Macro-generated `open` declarations cannot be fixed at the use site, so only lint
  -- identifiers written in the original source.
  let .original .. := info | return
  -- Identifiers with preresolved namespaces are not resolved against the environment.
  if preresolved.any fun | .namespace _ => true | _ => false then return
  -- `resolveNamespace` can return duplicates, e.g. when several `open` declarations make the
  -- same namespace visible.
  let resolved := resolved.eraseDups
  let env ← getEnv
  let currNamespace ← getCurrNamespace
  let openDecls ← getOpenDecls
  -- Interpretations via `open` declarations are always contained in `resolved`, so only the
  -- scope search can produce shadowed interpretations.
  let candidates := scopeCandidates env id currNamespace
  -- A namespace opened with `hiding` exceptions is not fully accessible, so it does not count.
  let isAccessible (n : Name) : Bool :=
    n.isPrefixOf currNamespace || openDecls.any fun
      | .simple ns [] => ns == n
      | _ => false
  let shadowed := candidates.filter fun n => !resolved.contains n && !isAccessible n
  if shadowed.isEmpty then return
  let display (n : Name) : MessageData := m!"`{rootNamespace ++ n}`"
  let displayAll (ns : List Name) : MessageData := MessageData.joinSep (ns.map display) ", "
  -- A shadowed interpretation is a non-innermost scope match, so `currNamespace` is nonempty.
  let shadowedNote :=
    if shadowed.length == 1 then m!"{displayAll shadowed} is silently not opened"
    else m!"{displayAll shadowed} are silently not opened"
  let hint :=
    m!" Specify the namespace unambiguously, e.g. `{rootNamespace ++ resolved.head!}`. The \
      warning can sometimes also be addressed by moving the `open` outside of the surrounding \
      `namespace`."
  let msg :=
    match resolved with
    | [r] =>
      m!"Ambiguous namespace `{id}`: it is interpreted as {display r} because this `open` occurs \
        inside `namespace {currNamespace}`, while {shadowedNote}." ++ hint
    | _ =>
      m!"Ambiguous namespace `{id}`: this `open` refers to all of {displayAll resolved}, while \
        {shadowedNote} because the `open` occurs inside `namespace {currNamespace}`." ++ hint
  logLint linter.ambiguousOpen nsStx.raw msg

end Lean.Linter
