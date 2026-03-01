/-
Copyright (c) 2026 Chad Sharp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp, Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Scan
public import Init.Data.Iterators.Lemmas.Consumers.Collect
public import Init.Data.List.Scan.Basic
import Init.Data.Iterators.Lemmas.Combinators.Monadic.Scan

public section

namespace Std
open Std.Iterators

variable {α β γ : Type w} [Iterator α Id β] {it : Iter (α := α) β}
    {m : Type w → Type w'}

@[simp]
theorem Iter.toList_scanWithPostcondition [Monad m] [LawfulMonad m] [Finite α Id]
    {f : γ → β → PostconditionT m γ} {init : γ} :
    (it.scanWithPostcondition f init).toList = it.toList.scanlM (f · · |>.run) init := by
  simp [Iter.scanWithPostcondition, Iter.toList, Id.run]

@[simp]
theorem Iter.toList_scanM
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Finite α Id] {f : γ → β → m γ} {init : γ} :
    (it.scanM f init).toList = it.toList.scanlM f init := by
  simp [Iter.scanM, Iter.toList, Id.run]

@[simp]
theorem Iter.toList_scan [Finite α Id] {f : γ → β → γ} {init : γ} :
    (it.scan f init).toList = List.scanl f init it.toList := by
  simp only [scan, IterM.toList_toIter, IterM.toList_scan]
  rfl

end Std
