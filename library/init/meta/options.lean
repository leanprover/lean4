/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.name

meta_constant options                  : Type₁
meta_constant options.size             : options → nat
meta_constant options.mk               : options
meta_constant options.contains         : options → name → bool
meta_constant options.set_bool         : options → name → bool → options
meta_constant options.set_nat          : options → name → nat → options
meta_constant options.set_string       : options → name → string → options
meta_constant options.get_bool         : options → name → bool → bool
meta_constant options.get_nat          : options → name → nat → nat
meta_constant options.get_string       : options → name → string → string
meta_constant options.join             : options → options → options
meta_constant options.fold {A : Type}  : options → A → (name → A → A) → A
meta_constant options.has_decidable_eq : decidable_eq options

attribute [instance] options.has_decidable_eq

attribute [instance]
meta_definition options.has_add : has_add options :=
has_add.mk options.join

attribute [instance]
meta_definition options.is_inhabited : inhabited options :=
inhabited.mk options.mk
