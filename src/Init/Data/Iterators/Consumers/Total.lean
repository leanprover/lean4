/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Basic

set_option doc.verso true
set_option linter.missingDocs true

public section

namespace Std

-- documented below by `add_decl_doc`, which can refer to `Iter.ensureTermination`
set_option linter.missingDocs false in
structure Iter.Total {α : Type w} (β : Type w) where
  /--
  The wrapped iterator, which was wrapped by `Iter.ensureTermination`.
  -/
  it : Iter (α := α) β

/--
For an iterator {name}`it`, {lean}`it.ensureTermination` provides variants of consumers that always
terminate.
-/
@[always_inline, inline]
def Iter.ensureTermination {α : Type w} {β : Type w}
    (it : Iter (α := α) β) :
  Iter.Total (α := α) β :=
  ⟨it⟩

/--
A wrapper around an iterator that provides strictly terminating consumers. See
{name}`Iter.ensureTermination`.
-/
add_decl_doc Iter.Total

end Std
