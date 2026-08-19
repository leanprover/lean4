/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.WP.Assertion
@[expose] public section

set_option linter.missingDocs true

/-!
# Exception Postcondition Stack Notation

A monad transformer stack carries one exception postcondition for each transformer that throws,
and `EStack⟨⟩` closes the stack. `EStack⟨Nat → σ → Prop, String → σ → Prop⟩` is the stack of
`ExceptT Nat (ExceptT String (StateM σ))`, and `estack⟨e₁, e₂⟩` is a value of it. The notation
hides the nesting and the `EStack⟨⟩` terminator of the `×` chain. A stack type prints back as
`EStack⟨…⟩`; a stack value prints as an ordinary tuple, because `()` carries no stack marker.

A base monad has one exception postcondition and no stack, so it does not use the notation:
`Except ε` carries a bare `ε → Prop`.
-/

namespace Std.WP

/-- The end of an exception postcondition stack. Reducibly `Unit`, so every `Unit` instance
applies, and a named constant, so the stack notation prints only on a stack. -/
abbrev EStackEnd := Unit

/-- Exception postcondition stack **type**: `EStack⟨ε₁ → l, ε₂ → l⟩` is `(ε₁ → l) × (ε₂ → l) × EStack⟨⟩`. -/
syntax "EStack⟨" term,* "⟩" : term
/-- Exception postcondition stack **value**: `estack⟨e₁, e₂⟩` is `(e₁, e₂, ())`. -/
syntax "estack⟨" term,* "⟩" : term

macro_rules
  | `(EStack⟨⟩) => `(EStackEnd)
  | `(EStack⟨$x⟩) => `($x × EStackEnd)
  | `(EStack⟨$x, $xs,*⟩) => `($x × EStack⟨$xs,*⟩)
  | `(estack⟨⟩) => `(())
  | `(estack⟨$x⟩) => `(($x, ()))
  | `(estack⟨$x, $xs,*⟩) => `(($x, estack⟨$xs,*⟩))

/-- Pretty-print `EStackEnd` as `EStack⟨⟩`. -/
@[app_unexpander EStackEnd] meta def unexpandEStackEnd : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(EStack⟨⟩)

/-- Pretty-print a product that ends in `EStack⟨⟩` as `EStack⟨e₁, e₂, ...⟩`. -/
@[app_unexpander Prod] meta def unexpandEStack : Lean.PrettyPrinter.Unexpander
  | `($(_) $x $xs) =>
    match xs with
    | `(EStack⟨⟩) => `(EStack⟨$x⟩)
    | `(EStack⟨$y⟩) => `(EStack⟨$x, $y⟩)
    | `(EStack⟨$y, $ys,*⟩) => `(EStack⟨$x, $y, $ys,*⟩)
    | _ => throw ()
  | _ => throw ()

end Std.WP
