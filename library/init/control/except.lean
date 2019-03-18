/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch, Sebastian Ullrich

The except monad transformer.
-/
prelude
import init.control.alternative init.control.lift init.data.to_string
import init.control.monad_fail
universes u v w

inductive except (ε : Type u) (α : Type v)
| error {} : ε → except
| ok {} : α → except

instance {ε α : Type} [inhabited ε] : inhabited (except ε α) :=
⟨except.error (default ε)⟩

section
variables {ε : Type u} {α : Type v}

protected def except.to_string [has_to_string ε] [has_to_string α] : except ε α → string
| (except.error e) := "(error " ++ to_string e ++ ")"
| (except.ok a)    := "(ok " ++ to_string a ++ ")"

protected def except.repr [has_repr ε] [has_repr α] : except ε α → string
| (except.error e) := "(error " ++ repr e ++ ")"
| (except.ok a)    := "(ok " ++ repr a ++ ")"

instance [has_to_string ε] [has_to_string α] : has_to_string (except ε α) :=
⟨except.to_string⟩

instance [has_repr ε] [has_repr α] : has_repr (except ε α) :=
⟨except.repr⟩
end

namespace except
variables {ε : Type u}

@[inline] protected def return {α : Type v} (a : α) : except ε α :=
except.ok a

@[inline] protected def map {α β : Type v} (f : α → β) : except ε α → except ε β
| (except.error err) := except.error err
| (except.ok v) := except.ok $ f v

@[inline] protected def map_error {ε' : Type u} {α : Type v} (f : ε → ε') : except ε α → except ε' α
| (except.error err) := except.error $ f err
| (except.ok v) := except.ok v

@[inline] protected def bind {α β : Type v} (ma : except ε α) (f : α → except ε β) : except ε β :=
match ma with
| (except.error err) := except.error err
| (except.ok v) := f v

@[inline] protected def to_bool {α : Type v} : except ε α → bool
| (except.ok _)    := tt
| (except.error _) := ff

@[inline] protected def to_option {α : Type v} : except ε α → option α
| (except.ok a)    := some a
| (except.error _) := none

@[inline] protected def catch {α : Type u} (ma : except ε α) (handle : ε → except ε α) : except ε α :=
match ma with
| except.ok a    := except.ok a
| except.error e := handle e

instance : monad (except ε) :=
{ pure := @except.return _, bind := @except.bind _ }
end except

def except_t (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
m (except ε α)

@[inline] def except_t.mk {ε : Type u} {m : Type u → Type v} {α : Type u} (x : m (except ε α)) : except_t ε m α :=
x

@[inline] def except_t.run {ε : Type u} {m : Type u → Type v} {α : Type u} (x : except_t ε m α) : m (except ε α) :=
x

namespace except_t
variables {ε : Type u} {m : Type u → Type v} [monad m]

@[inline] protected def return {α : Type u} (a : α) : except_t ε m α :=
except_t.mk $ pure (except.ok a)

@[inline] protected def bind_cont {α β : Type u} (f : α → except_t ε m β) : except ε α → m (except ε β)
| (except.ok a)    := f a
| (except.error e) := pure (except.error e)

@[inline] protected def bind {α β : Type u} (ma : except_t ε m α) (f : α → except_t ε m β) : except_t ε m β :=
except_t.mk $ ma >>= except_t.bind_cont f

@[inline] protected def lift {α : Type u} (t : m α) : except_t ε m α :=
except_t.mk $ except.ok <$> t

instance except_t_of_except : has_monad_lift (except ε) (except_t ε m) :=
⟨λ α e, except_t.mk $ pure e⟩

instance : has_monad_lift m (except_t ε m) :=
⟨@except_t.lift _ _ _⟩

@[inline] protected def catch {α : Type u} (ma : except_t ε m α) (handle : ε → except_t ε m α) : except_t ε m α :=
except_t.mk $ ma >>= λ res, match res with
 | except.ok a    := pure (except.ok a)
 | except.error e := (handle e)

instance (m') [monad m'] : monad_functor m m' (except_t ε m) (except_t ε m') :=
⟨λ _ f x, f x⟩

instance : monad (except_t ε m) :=
{ pure := @except_t.return _ _ _, bind := @except_t.bind _ _ _ }

@[inline] protected def adapt {ε' α : Type u} (f : ε → ε') : except_t ε m α → except_t ε' m α :=
λ x, except_t.mk $ except.map_error f <$> x
end except_t

/-- An implementation of [MonadError](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Except.html#t:MonadError) -/
class monad_except (ε : out_param (Type u)) (m : Type v → Type w) :=
(throw {} {α : Type v} : ε → m α)
(catch {} {α : Type v} : m α → (ε → m α) → m α)

namespace monad_except
variables {ε : Type u} {m : Type v → Type w}

@[inline] protected def orelse [monad_except ε m] {α : Type v} (t₁ t₂ : m α) : m α :=
catch t₁ $ λ _, t₂

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
@[inline] def orelse' [monad_except ε m] {α : Type v} (t₁ t₂ : m α) (use_first_ex := tt) : m α :=
catch t₁ $ λ e₁, catch t₂ $ λ e₂, throw (if use_first_ex then e₁ else e₂)

@[inline] def lift_except {ε' : Type u} [monad_except ε m] [has_lift_t ε' ε] [monad m] {α : Type v} : except ε' α → m α
| (except.error e) := throw ↑e
| (except.ok a)    := pure a
end monad_except

export monad_except (throw catch)

instance (m : Type u → Type v) (ε : Type u) [monad m] : monad_except ε (except_t ε m) :=
{ throw := λ α e, except_t.mk $ pure (except.error e),
  catch := @except_t.catch ε _ _ }

instance (ε) : monad_except ε (except ε) :=
{ throw := λ α, except.error, catch := @except.catch _ }

/-- Adapt a monad stack, changing its top-most error type.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_except_functor (ε ε' : out_param (Type u)) (n n' : Type u → Type u) :=
    (map {} {α : Type u} : (∀ {m : Type u → Type u} [monad m], except_t ε m α → except_t ε' m α) → n α → n' α)
    ```
-/
class monad_except_adapter (ε ε' : out_param (Type u)) (m m' : Type u → Type v) :=
(adapt_except {} {α : Type u} : (ε → ε') → m α → m' α)
export monad_except_adapter (adapt_except)

section
variables {ε ε' : Type u} {m m' : Type u → Type v}

instance monad_except_adapter_trans {n n' : Type u → Type v} [monad_functor m m' n n'] [monad_except_adapter ε ε' m m'] : monad_except_adapter ε ε' n n' :=
⟨λ α f, monad_map (λ α, (adapt_except f : m α → m' α))⟩

instance [monad m] : monad_except_adapter ε ε' (except_t ε m) (except_t ε' m) :=
⟨λ α, except_t.adapt⟩
end

instance (ε m out) [monad_run out m] : monad_run (λ α, out (except ε α)) (except_t ε m) :=
⟨λ α, run⟩

-- useful for implicit failures in do-notation
instance (m : Type → Type) [monad m] : monad_fail (except_t string m) :=
⟨λ _, throw⟩
