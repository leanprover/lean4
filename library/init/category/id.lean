/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.category.monad
universe u

instance : monad.{u u} id :=
{ pure := @id, bind := λ _ _ x f, f x }
