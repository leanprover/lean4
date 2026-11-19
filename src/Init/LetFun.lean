/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

prelude

import Init.Notation

/--
`letFun v (fun x => b)` is a function version of `have x := v; b`.
This is equal to `(fun x => b) v`, so the value of `x` is not accessible to `b`.
This is in contrast to `let x := v; b`, where the value of `x` is accessible to `b`.

This used to be the way `have`/`let_fun` syntax was encoded,
and there used to be special support for `letFun` in WHNF and `simp`.
-/
@[deprecated "Use `have` instead." (since := "2026-07-23")]
public def letFun {α : Sort u} {β : α → Sort v} (v : α) (f : (x : α) → β x) : β v := f v
