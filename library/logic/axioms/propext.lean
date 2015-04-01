/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: logic.axioms.funext
Author: Leonardo de Moura

Propositional extensionality.
-/
axiom propext {a b : Prop} : a ↔ b → a = b
