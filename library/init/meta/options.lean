/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.name
universe u
meta constant options                   : Type
meta constant options.size              : options → nat
meta constant options.mk                : options
meta constant options.contains          : options → name → bool
meta constant options.set_bool          : options → name → bool → options
meta constant options.set_nat           : options → name → nat → options
meta constant options.set_string        : options → name → string → options
meta constant options.get_bool          : options → name → bool → bool
meta constant options.get_nat           : options → name → nat → nat
meta constant options.get_string        : options → name → string → string
meta constant options.join              : options → options → options
meta constant options.fold {α : Type u} : options → α → (name → α → α) → α
meta constant options.has_decidable_eq  : decidable_eq options

attribute [instance] options.has_decidable_eq

meta instance : has_add options :=
⟨options.join⟩

meta instance : inhabited options :=
⟨options.mk⟩
