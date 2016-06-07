/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.expr

/- Reflect a C++ declaration object. The VM replaces it with the C++ implementation. -/
inductive declaration :=
/- definition: name, list universe parameters, type, value, is_trusted -/
| def  : name → list name → expr → expr → bool → declaration
/- theorem: name, list universe parameters, type, value (remark: theorems are always trusted) -/
| thm  : name → list name → expr → expr → declaration
/- constant assumption: name, list universe parameters, type, is_trusted -/
| cnst : name → list name → expr → bool → declaration
/- axiom : name → list universe parameters, type (remark: axioms are always trusted) -/
| ax   : name → list name → expr → declaration
