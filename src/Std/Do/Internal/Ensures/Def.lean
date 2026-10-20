/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Core

set_option linter.missingDocs true

universe u v

/-!
# `Internal.Ensures` and `Internal.MayReturn`

`Internal.Ensures p x` characterizes the postconditions of a monadic action `x`: it
holds iff every value returned by `x` satisfies `p`. The witness is a `Subtype`-refined
action `y : m {a // p a}` that is bind-faithful w.r.t. `x`.

`Internal.MayReturn x a` is the strongest postcondition of `x` evaluated at `a`:
`a` is in every postcondition of `x` ↔ `a` is reachable as a value of `x`.
-/

namespace Std.Do.Internal

/--
{lean}`ErasesTo x y` says the property-tagged {name}`x` is bind-faithful to {name}`y`: binding
{name}`x` and forgetting the property agrees with binding {name}`y`.
-/
public structure ErasesTo {α : Type u} {m : Type u → Type v} [Bind m] {P : α → Prop}
    (x : m {b : α // P b}) (y : m α) : Prop where
  /-- The bind-faithful equation: binding `x` and projecting agrees with binding `y`. -/
  bind_eq {β} (k : α → m β) : x >>= (fun a => k a.val) = y >>= k

/-- `Ensures p x` says every value returned by `x` satisfies `p`. The witness is a
`Subtype`-refined monadic action that is bind-faithful w.r.t. `x`. -/
public structure Ensures {m : Type u → Type v} [Bind m] {α : Type u}
    (P : α → Prop) (x : m α) : Prop where
  /-- A `P`-tagged refinement of `x` exists. -/
  exists_refinement : Exists fun y : m {a : α // P a} => ErasesTo y x

/-- `MayReturn x a` says `a` is in every postcondition of `x`, equivalently that `a`
is a value returnable from `x`. (The strongest postcondition, evaluated at `a`.) -/
public structure MayReturn {m : Type u → Type v} [Bind m] {α : Type u}
    (x : m α) (a : α) : Prop where
  /-- Apply a `MayReturn` witness to an `Ensures` proof to extract the postcondition at `a`. -/
  imp {P : α → Prop} : Ensures P x → P a

/-- `IsAttach attach` says `attach` tags each value of `x` with its `MayReturn` proof
in a bind-faithful way. -/
public structure IsAttach {m : Type u → Type v} [Bind m]
    (attach : ⦃α : Type u⦄ → (x : m α) → m {a : α // MayReturn x a}) : Prop where
  /-- For each `x`, the attached version is bind-faithful with `x`. -/
  erases {α} (x : m α) : ErasesTo (attach x) x

end Std.Do.Internal
