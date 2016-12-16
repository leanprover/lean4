/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.expr init.meta.name init.meta.task

/-
Reducibility hints are used in the convertibility checker.
When trying to solve a constraint such a

           (f ...) =?= (g ...)

where f and g are definitions, the checker has to decide which one will be unfolded.
  If      f (g) is opaque,     then g (f) is unfolded if it is also not marked as opaque,
  Else if f (g) is abbrev,     then f (g) is unfolded if g (f) is also not marked as abbrev,
  Else if f and g are regular, then we unfold the one with the biggest definitional height.
  Otherwise both are unfolded.

The arguments of the `regular` constructor are: the definitional height and the flag `self_opt`.

The definitional height is by default computed by the kernel. It only takes into account
other regular definitions used in a definition. When creating declarations using meta-programming,
we can specify the definitional depth manually.

For definitions marked as regular, we also have a hint for constraints such as

          (f a) =?= (f b)

if self_opt == true, then checker will first try to solve (a =?= b), only if it fails,
it unfolds f.

Remark: the hint only affects performance. None of the hints prevent the kernel from unfolding a
declaration during type checking.

Remark: the reducibility_hints are not related to the attributes: reducible/irrelevance/semireducible.
These attributes are used by the elaborator. The reducibility_hints are used by the kernel (and elaborator).
Moreover, the reducibility_hints cannot be changed after a declaration is added to the kernel.
-/
inductive reducibility_hints
| opaque  : reducibility_hints
| abbrev  : reducibility_hints
| regular : nat → bool → reducibility_hints

/- Reflect a C++ declaration object. The VM replaces it with the C++ implementation. -/
meta inductive declaration
/- definition: name, list universe parameters, type, value, is_trusted -/
| defn : name → list name → expr → expr → reducibility_hints → bool → declaration
/- theorem: name, list universe parameters, type, value (remark: theorems are always trusted) -/
| thm  : name → list name → expr → task expr → declaration
/- constant assumption: name, list universe parameters, type, is_trusted -/
| cnst : name → list name → expr → bool → declaration
/- axiom : name → list universe parameters, type (remark: axioms are always trusted) -/
| ax   : name → list name → expr → declaration

meta def declaration.to_name : declaration → name
| (declaration.defn n ls t v h tr) := n
| (declaration.thm n ls t v) := n
| (declaration.cnst n ls t tr) := n
| (declaration.ax n ls t) := n

meta def declaration.univ_params : declaration → list name
| (declaration.defn n ls t v h tr) := ls
| (declaration.thm n ls t v) := ls
| (declaration.cnst n ls t tr) := ls
| (declaration.ax n ls t) := ls

meta def declaration.type : declaration → expr
| (declaration.defn n ls t v h tr) := t
| (declaration.thm n ls t v) := t
| (declaration.cnst n ls t tr) := t
| (declaration.ax n ls t) := t

meta def declaration.value : declaration → expr
| (declaration.defn n ls t v h tr) := v
| (declaration.thm n ls t v) := v^.get
| _ := default expr

meta def declaration.update_type : declaration → expr → declaration
| (declaration.defn n ls t v h tr) new_t := declaration.defn n ls new_t v h tr
| (declaration.thm n ls t v)       new_t := declaration.thm n ls new_t v
| (declaration.cnst n ls t tr)     new_t := declaration.cnst n ls new_t tr
| (declaration.ax n ls t)          new_t := declaration.ax n ls new_t

meta def declaration.update_name : declaration → name → declaration
| (declaration.defn n ls t v h tr) new_n := declaration.defn new_n ls t v h tr
| (declaration.thm n ls t v)       new_n := declaration.thm new_n ls t v
| (declaration.cnst n ls t tr)     new_n := declaration.cnst new_n ls t tr
| (declaration.ax n ls t)          new_n := declaration.ax new_n ls t

meta def declaration.update_value : declaration → expr → declaration
| (declaration.defn n ls t v h tr) new_v := declaration.defn n ls t new_v h tr
| (declaration.thm n ls t v)       new_v := declaration.thm n ls t (task.pure new_v)
| d                                new_v := d

meta def declaration.to_definition : declaration → declaration
| (declaration.cnst n ls t tr) := declaration.defn n ls t (default expr) reducibility_hints.abbrev tr
| (declaration.ax n ls t)      := declaration.thm n ls t (task.pure (default expr))
| d                            := d

/- Instantiate a universe polymorphic declaration type with the given universes. -/
meta constant declaration.instantiate_type_univ_params : declaration → list level → option expr

/- Instantiate a universe polymorphic declaration value with the given universes. -/
meta constant declaration.instantiate_value_univ_params : declaration → list level → option expr