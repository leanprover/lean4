/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.CoreM
import Lean.Expr

public section

namespace Lean

private def carrierIsSortUncached (declName : Name) : CoreM Bool := do
  let some info := (← getEnv).find? declName
    | throwError "unknown constant `{declName}`"
  let [u] := info.levelParams
    | throwError "`{declName}` is expected to take exactly one universe parameter"
  let .forallE _ (.sort l) _ _ := info.type
    | throwError "the first argument of `{declName}` is expected to be its carrier"
  if l == .param u then
    return true
  else if l == .succ (.param u) then
    return false
  else
    throwError "the carrier of `{declName}` is `Sort {l}`, which is neither `Sort {u}` nor `Type {u}`"

builtin_initialize leCarrierIsSortCache : IO.Ref (Option Bool) ← IO.mkRef none

/--
Reports whether the carrier of `LE` is a `Sort` rather than a `Type`.

The universe argument of `LE` means something different in each of the two forms the class can be
declared in. With `class LE (α : Type u)`, the relation on `α : Type u` is `@LE.le.{u} α`; with
`class LE (α : Sort u)`, the same relation is `@LE.le.{u+1} α`, because `Type u` is `Sort (u+1)`.
The forms are told apart by the domain of the first binder of `LE`, which is
`.sort (.succ (.param u))` for `Type u` and the bare `.sort (.param u)` for `Sort u`.

The answer is cached for the lifetime of the process: the declared form of `LE` cannot change
within one environment lineage, and the classification is only cached once it succeeds, so a
lookup before `LE` exists throws without poisoning the cache. `LT` is required to be declared in
the same form as `LE`, and this single test answers for every constant that changes forms in the
same commit as `LE`: the classes `Std.IsPreorder`, `Std.IsPartialOrder`, `Std.IsLinearOrder`,
`Std.IsLinearPreorder` and `Std.LawfulOrderLT`, their parent projections, and the
`Lean.Grind.Order` helper lemmas whose auto-bound carrier follows `LE`.
-/
def leCarrierIsSort : CoreM Bool := do
  if let some b := (← leCarrierIsSortCache.get) then
    return b
  let le ← carrierIsSortUncached ``LE
  let lt ← carrierIsSortUncached ``LT
  unless le == lt do
    throwError "`LE` and `LT` disagree on whether their carrier is a `Sort` or a `Type`"
  leCarrierIsSortCache.set (some le)
  return le

end Lean
