/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.basic

namespace list

/- TODO(Leo): remove meta as soon as equation compiler has support for well founded recursion.

   This is based on the minimalist Haskell "quicksort".

   Remark: this is *not* really quicksort since it doesn't partition the elements in-place -/
meta def qsort {α} (lt : α → α → bool) : list α → list α
| []     := []
| (h::t) :=
  let small := filter (λ x, lt h x = ff) t,
      large := filter (λ x, lt h x = tt) t
  in qsort small ++ h :: qsort large

end list
