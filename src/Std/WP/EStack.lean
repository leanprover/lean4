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

A monad transformer stack carries one exception postcondition for each transformer that throws.
A stack of postconditions is a right-nested `×` chain with the marker type `EStackEnd` as its
last component. `EStack⟨Nat → σ → Prop, String → σ → Prop⟩` is the stack of
`ExceptT Nat (ExceptT String (StateM σ))`, and `estack⟨e₁, e₂⟩` is a value of it. The notation
hides the nesting and the marker. A stack type prints back as `EStack⟨…⟩`. A stack value prints
as a tuple, because the value `()` carries no marker.

A base monad has one exception postcondition and no stack, so it does not use the notation:
`Except ε` carries a bare `ε → Prop`.
-/

namespace Std.WP

/-- The last component of an exception postcondition stack. It reduces to `Unit`, so every
`Unit` instance applies. It is a named constant, so only a stack prints as `EStack⟨…⟩`. -/
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

/-- Prints `EStackEnd` as `EStack⟨⟩`. -/
@[app_unexpander EStackEnd] meta def unexpandEStackEnd : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(EStack⟨⟩)

/-- Prints a product that ends in `EStack⟨⟩` as `EStack⟨e₁, e₂, …⟩`. -/
@[app_unexpander Prod] meta def unexpandEStack : Lean.PrettyPrinter.Unexpander
  | `($(_) $x $xs) =>
    match xs with
    | `(EStack⟨⟩) => `(EStack⟨$x⟩)
    | `(EStack⟨$y⟩) => `(EStack⟨$x, $y⟩)
    | `(EStack⟨$y, $ys,*⟩) => `(EStack⟨$x, $y, $ys,*⟩)
    | _ => throw ()
  | _ => throw ()

end Std.WP
