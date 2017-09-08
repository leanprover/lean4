/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.expr init.meta.name init.meta.task

/--
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

/-- Reflect a C++ declaration object. The VM replaces it with the C++ implementation. -/
meta inductive declaration
/- definition: name, list universe parameters, type, value, is_trusted -/
| defn : name → list name → expr → expr → reducibility_hints → bool → declaration
/- theorem: name, list universe parameters, type, value (remark: theorems are always trusted) -/
| thm  : name → list name → expr → task expr → declaration
/- constant assumption: name, list universe parameters, type, is_trusted -/
| cnst : name → list name → expr → bool → declaration
/- axiom : name → list universe parameters, type (remark: axioms are always trusted) -/
| ax   : name → list name → expr → declaration

open declaration

meta def mk_definition (n : name) (ls : list name) (v : expr) (e : expr) : declaration :=
defn n ls v e (reducibility_hints.regular 1 tt) tt

namespace declaration

meta def to_name : declaration → name
| (defn n _ _ _ _ _) := n
| (thm n _ _ _)      := n
| (cnst n _ _ _)     := n
| (ax n _ _)         := n

meta def univ_params : declaration → list name
| (defn _ ls _ _ _ _) := ls
| (thm _ ls _ _)      := ls
| (cnst _ ls _ _)     := ls
| (ax _ ls _)         := ls

meta def type : declaration → expr
| (defn _ _ t _ _ _) := t
| (thm _ _ t _)      := t
| (cnst _ _ t _)     := t
| (ax _ _ t)         := t

meta def value : declaration → expr
| (defn _ _ _ v _ _) := v
| (thm _ _ _ v)      := v.get
| _                  := default expr

meta def value_task : declaration → task expr
| (defn _ _ _ v _ _) := task.pure v
| (thm _ _ _ v)      := v
| _                  := task.pure (default expr)

meta def is_trusted : declaration → bool
| (defn _ _ _ _ _ t) := t
| (cnst _ _ _ t)     := t
| _                  := tt

meta def update_type : declaration → expr → declaration
| (defn n ls t v h tr) new_t := defn n ls new_t v h tr
| (thm n ls t v)       new_t := thm n ls new_t v
| (cnst n ls t tr)     new_t := cnst n ls new_t tr
| (ax n ls t)          new_t := ax n ls new_t

meta def update_name : declaration → name → declaration
| (defn n ls t v h tr) new_n := defn new_n ls t v h tr
| (thm n ls t v)       new_n := thm new_n ls t v
| (cnst n ls t tr)     new_n := cnst new_n ls t tr
| (ax n ls t)          new_n := ax new_n ls t

meta def update_value : declaration → expr → declaration
| (defn n ls t v h tr) new_v := defn n ls t new_v h tr
| (thm n ls t v)       new_v := thm n ls t (task.pure new_v)
| d                    new_v := d

meta def update_value_task : declaration → task expr → declaration
| (defn n ls t v h tr) new_v := defn n ls t new_v.get h tr
| (thm n ls t v)       new_v := thm n ls t new_v
| d                    new_v := d

meta def map_value : declaration → (expr → expr) → declaration
| (defn n ls t v h tr) f := defn n ls t (f v) h tr
| (thm n ls t v)       f := thm n ls t (task.map f v)
| d                    f := d

meta def to_definition : declaration → declaration
| (cnst n ls t tr) := defn n ls t (default expr) reducibility_hints.abbrev tr
| (ax n ls t)      := thm n ls t (task.pure (default expr))
| d                := d

meta def is_definition : declaration → bool
| (defn _ _ _ _ _ _) := tt
| _                  := ff

/-- Instantiate a universe polymorphic declaration type with the given universes. -/
meta constant instantiate_type_univ_params : declaration → list level → option expr

/-- Instantiate a universe polymorphic declaration value with the given universes. -/
meta constant instantiate_value_univ_params : declaration → list level → option expr

end declaration
