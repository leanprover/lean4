/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura

Basic datatypes
-/
prelude
notation [parsing-only] `Type'` := Type.{_+1}
notation [parsing-only] `Type₊` := Type.{_+1}
notation `Type₀` := Type.{0}
notation `Type₁` := Type.{1}
notation `Type₂` := Type.{2}
notation `Type₃` := Type.{3}

inductive unit : Type :=
star : unit

inductive empty : Type

structure prod (A B : Type) :=
mk :: (pr1 : A) (pr2 : B)
