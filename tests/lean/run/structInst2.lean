import Init.Control.Option


universe u v

def OptionT2 (m : Type u → Type v) (α : Type u) : Type v :=
m (Option α)

namespace OptionT2
variable {m : Type u → Type v} [Monad m] {α β : Type u}

@[inline] protected def bind (ma : OptionT2 m α) (f : α → OptionT2 m β) : OptionT2 m β :=
(do {
    let a? ← ma;
    (match a? with
    | some a => f a
    | none   => pure none)
} : m (Option β))

@[inline] protected def pure (a : α) : OptionT2 m α :=
(Pure.pure (some a) : m (Option α))

@[inline] protected def orelse (ma : OptionT2 m α) (mb : Unit → OptionT2 m α) : OptionT2 m α :=
(do { let a? ← ma;
        (match a? with
        | some a => pure (some a)
        | _      => mb ()) } : m (Option α))

@[inline] protected def fail : OptionT2 m α :=
(pure none : m (Option α))

end OptionT2

instance optMonad1 {m} [Monad m] : Monad (OptionT2 m) :=
{ pure := OptionT2.pure, bind := OptionT2.bind }

def optMonad2 {m} [Monad m] : Monad (OptionT m) :=
{ pure := OptionT.pure, bind := OptionT.bind }

def optAlt1 {m} [Monad m] : Alternative (OptionT m) :=
{ failure       := OptionT.fail,
  orElse        := OptionT.orElse,
  toApplicative := Monad.toApplicative }

def optAlt2 {m} [Monad m] : Alternative (OptionT m) :=
⟨OptionT.fail, OptionT.orElse⟩ -- it works because it treats `toApplicative` as an instance implicit argument

def optAlt3 {m} [Monad m] : Alternative (OptionT2 m) :=
{ failure       := OptionT2.fail,
  orElse        := OptionT2.orelse,
  toApplicative := Monad.toApplicative }
