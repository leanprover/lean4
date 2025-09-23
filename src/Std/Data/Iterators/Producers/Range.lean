/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Iterators

set_option doc.verso true

@[expose] public section

/-!
# Range iterator

This module provides iterators over ranges {name}`Std.Rcc` (and {name}`Std.Rco`, ...) via
{name (scope := "Std.Data.Iterators.Producers.Range")}`Std.Rcc.iter` (and
{name (scope := "Std.Data.Iterators.Producers.Range")}`Std.Rco.iter`, ...).
-/

open Std.PRange

/--
Returns an iterator over the given range. This iterator will emit the elements of the range
in increasing order.
-/
@[always_inline, inline]
def Std.Rcc.iter (r : Rcc α) : Iter (α := Rxc.Iterator α) α :=
  ⟨⟨some r.lower, r.upper⟩⟩

/--
Returns an iterator over the given range. This iterator will emit the elements of the range
in increasing order.
-/
@[always_inline, inline]
def Std.Rco.iter (r : Rco α) : Iter (α := Rxo.Iterator α) α :=
  ⟨⟨some r.lower, r.upper⟩⟩

/--
Returns an iterator over the given range. This iterator will emit the elements of the range
in increasing order.
-/
@[always_inline, inline]
def Std.Rci.iter (r : Rci α) : Iter (α := Rxi.Iterator α) α :=
  ⟨⟨some r.lower⟩⟩

/--
Returns an iterator over the given range. This iterator will emit the elements of the range
in increasing order.
-/
@[always_inline, inline]
def Std.Roc.iter [UpwardEnumerable α] (r : Roc α) : Iter (α := Rxc.Iterator α) α :=
  ⟨⟨UpwardEnumerable.succ? r.lower, r.upper⟩⟩

/--
Returns an iterator over the given range. This iterator will emit the elements of the range
in increasing order.
-/
@[always_inline, inline]
def Std.Roo.iter [UpwardEnumerable α] (r : Roo α) : Iter (α := Rxo.Iterator α) α :=
  ⟨⟨UpwardEnumerable.succ? r.lower, r.upper⟩⟩

/--
Returns an iterator over the given range. This iterator will emit the elements of the range
in increasing order.
-/
@[always_inline, inline]
def Std.Roi.iter [UpwardEnumerable α] (r : Roi α) : Iter (α := Rxi.Iterator α) α :=
  ⟨⟨UpwardEnumerable.succ? r.lower⟩⟩

/--
Returns an iterator over the given range. This iterator will emit the elements of the range
in increasing order.
-/
@[always_inline, inline]
def Std.Ric.iter [Least? α] (r : Ric α) : Iter (α := Rxc.Iterator α) α :=
  ⟨⟨Least?.least?, r.upper⟩⟩

/--
Returns an iterator over the given range. This iterator will emit the elements of the range
in increasing order.
-/
@[always_inline, inline]
def Std.Rio.iter [Least? α] (r : Rio α) : Iter (α := Rxo.Iterator α) α :=
  ⟨⟨Least?.least?, r.upper⟩⟩

/--
Returns an iterator over the given range. This iterator will emit the elements of the range
in increasing order.
-/
@[always_inline, inline]
def Std.Rii.iter [Least? α] (_ : Rii α) : Iter (α := Rxi.Iterator α) α :=
  ⟨⟨Least?.least?⟩⟩
