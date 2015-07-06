/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Define countable types
-/
open function

definition countable (A : Type) : Prop := ∃ f : A → nat, injective f
