/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.monad init.meta.format
/-
Remark: we use a function that produces a format object as the exception information.
Motivation: the formatting object may be big, and we may create it on demand.
-/
inductive exceptional (A : Type)
| success   : A → exceptional
| exception : (options → format) → exceptional

section
open exceptional
variables {A : Type}
variables [has_to_string A]

protected meta definition exceptional.to_string : exceptional A → string
| (success a)       := to_string a
| (exception .A e) := "Exception: " ++ to_string (e options.mk)

attribute [instance]
protected meta definition exceptional.has_to_string : has_to_string (exceptional A) :=
has_to_string.mk exceptional.to_string
end

namespace exceptional
variables {A B : Type}

attribute [inline]
protected meta definition fmap (f : A → B) (e : exceptional A) : exceptional B :=
exceptional.cases_on e
  (λ a, success (f a))
  (λ f, exception B f)

attribute [inline]
protected meta definition bind (e₁ : exceptional A) (e₂ : A → exceptional B) : exceptional B :=
exceptional.cases_on e₁
  (λ a, e₂ a)
  (λ f, exception B f)

attribute [inline]
protected meta definition return (a : A) : exceptional A :=
success a

attribute [inline]
meta definition fail (f : format) : exceptional A :=
exception A (λ u, f)
end exceptional

attribute [instance]
meta definition exceptional.is_monad : monad exceptional :=
⟨@exceptional.fmap, @exceptional.return, @exceptional.bind⟩
