/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Excluded middle

Remark: This axiom can be derived from propext funext and hilbert.
See examples/diaconescu
-/
axiom em (a : Prop) : a ∨ ¬a
