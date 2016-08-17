/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.expr init.meta.name

/- Reflect a C++ declaration object. The VM replaces it with the C++ implementation. -/
inductive declaration
/- definition: name, list universe parameters, type, value, is_trusted -/
| def  : name → list name → expr → expr → bool → declaration
/- theorem: name, list universe parameters, type, value (remark: theorems are always trusted) -/
| thm  : name → list name → expr → expr → declaration
/- constant assumption: name, list universe parameters, type, is_trusted -/
| cnst : name → list name → expr → bool → declaration
/- axiom : name → list universe parameters, type (remark: axioms are always trusted) -/
| ax   : name → list name → expr → declaration

definition declaration.to_name : declaration → name
| (declaration.def n ls t v tr) := n
| (declaration.thm n ls t v) := n
| (declaration.cnst n ls t tr) := n
| (declaration.ax n ls t) := n

definition declaration.univ_params : declaration → list name
| (declaration.def n ls t v tr) := ls
| (declaration.thm n ls t v) := ls
| (declaration.cnst n ls t tr) := ls
| (declaration.ax n ls t) := ls

definition declaration.type : declaration → expr
| (declaration.def n ls t v tr) := t
| (declaration.thm n ls t v) := t
| (declaration.cnst n ls t tr) := t
| (declaration.ax n ls t) := t

/- Instantiate a universe polymorphic declaration type with the given universes. -/
meta_constant declaration.instantiate_type_univ_params : declaration → list level → option expr

/- Instantiate a universe polymorphic declaration value with the given universes. -/
meta_constant declaration.instantiate_value_univ_params : declaration → list level → option expr
