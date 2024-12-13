/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"

namespace lean {
/* Insert `S.casesOn` applications for a structure `S` when
   1- There is a constructor application `S.mk ... x ...`, and
   2- `x := y.i`, and
   3- There is no `S.casesOn y ...`

   This transformation is useful because the `reset/reuse` insertion
   procedure uses `casesOn` applications as a guide.
   Moreover, Lean structure update expressions are not compiled using
   `casesOn` applicactions.

   Example: given
   ```
   fun x,
   let y_1 := x.1 in
   let y_2 := 0 in
   (y_1, y_2)
   ```
   this function returns
   ```
   fun x,
   Prod.casesOn x
    (fun fst snd,
      let y_1 := x.1 in
      let y_2 := 0 in
      (y_1, y_2))
   ```
   Note that, we rely on the simplifier (csimp.cpp) to replace `x.1` with `fst`.

   Remark: this function assumes we have already erased irrelevant information.

   Remark: we have considered compiling the `{ x with ... }` expressions using `casesOn`, but
   we loose useful definitional equalities. In the encoding we use,
   `{x with field1 := v1, field2 := v2}.field1` is definitional equal to `v1`.
   If we compile this expression using `casesOn`, we would have
   ```
   (match x with
    | {field1 := _, field2 := _, field3 := v3} := {field1 := v1, field2 := v2, field3 := v3}).field1
   ```
   as is only definitionally equal to `v1` IF `x` is definitionally equal to a constructor application.
   The missing definitional equalities is problematic. For example, the whole algebraic hierarchy
   in Lean relies on them.
*/
expr struct_cases_on(elab_environment const & env, expr const & e);
}
