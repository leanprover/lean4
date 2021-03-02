universes u v w

namespace Nondet

def AltsCore := PNonScalar.{u}

inductive Alts (m : Type u → Type u) (α : Type u)
| nil                                  : Alts m α
| cons  (head : α) (tail : m AltsCore) : Alts m α
| delayed (t : Thunk (m AltsCore))     : Alts m α

namespace Alts

@[inline]
unsafe def ofAltsCore {m : Type u → Type u} {α : Type u} (x : m AltsCore.{u}) : m (Alts m α) :=
  unsafeCast x

@[inline]
unsafe def toAltsCore {m : Type u → Type u} {α : Type u} (x : m (Alts m α)) : m AltsCore.{u} :=
  unsafeCast x

mutual
unsafe def run' {m : Type u → Type u} {α : Type u} [Monad m] : Alts m α → m (Option (α × m (Alts m α)))
  | nil        => pure none
  | cons x xs  => pure $ some (x, ofAltsCore xs)
  | delayed xs => runUnsafe (ofAltsCore xs.get)

unsafe def runUnsafe {m : Type u → Type u} {α : Type u} [Monad m] (x : m (Alts m α)) : m (Option (α × m (Alts m α))) := do
  run' (← x)
end

unsafe def ofList [Monad m] : List α → m (Alts m α)
  | []    => pure Alts.nil
  | a::as => pure $ Alts.cons a (toAltsCore (ofList as))

mutual
unsafe def append' [Monad m] : Alts m α → m (Alts m α) → m (Alts m α)
  | nil,          bs => bs
  | cons a as,    bs => pure $ delayed $ Thunk.mk fun _ => toAltsCore $ pure $ cons a $ toAltsCore $ append (ofAltsCore as) bs
  | delayed as,   bs => pure $ delayed $ Thunk.mk fun _ => toAltsCore $ append (ofAltsCore as.get) bs

unsafe def append [Monad m] (xs ys : m (Alts m α)) : m (Alts m α) := do
  append' (← xs) ys
end

mutual
unsafe def join' [Monad m] : Alts m (m (Alts m α)) → m (Alts m α)
  | nil        => pure nil
  | cons x xs  => pure $ delayed $ Thunk.mk fun _ => toAltsCore $ append x $ join $ ofAltsCore xs
  | delayed xs => pure $ delayed $ Thunk.mk fun _ => toAltsCore (α := α) $ join (ofAltsCore xs.get)

unsafe def join [Monad m] (xs : m (Alts m (m (Alts m α)))) : m (Alts m α) := do
  join' (← xs)
end

mutual
unsafe def map' [Monad m] (f : α → β) : Alts m α → m (Alts m β)
  | nil          => pure nil
  | cons x xs    => pure $ delayed $ Thunk.mk fun _ => toAltsCore $ pure $ cons (f x) $ toAltsCore $ map f (ofAltsCore xs)
  | delayed xs   => pure $ delayed $ Thunk.mk fun _ => toAltsCore $ map f (ofAltsCore xs.get)

unsafe def map [Monad m] (f : α → β) (xs : m (Alts m α)) : m (Alts m β) := do
  map' f (← xs)
end

@[inline]
protected unsafe def pure [Monad m] (a : α) : m (Alts m α) := do
  pure $ Alts.cons a $ toAltsCore (α := α) Alts.nil

end Alts

def NondetT (m : Type u → Type u) (α : Type u) := m (Alts m α)

instance [Pure m] : Inhabited (NondetT m α) where
  default := (pure Alts.nil : m (Alts m α))

@[inline]
unsafe def appendUnsafe [Monad m] (x y : NondetT m α) : NondetT m α :=
  Alts.append x y

@[implementedBy appendUnsafe]
protected constant append [Monad m] (x y : NondetT m α) : NondetT m α

@[inline]
unsafe def joinUnsafe [Monad m] (x : NondetT m (NondetT m α)) : NondetT m α :=
  Alts.join x

@[implementedBy joinUnsafe]
protected constant join [Monad m] (x : NondetT m (NondetT m α)) : NondetT m α

@[inline]
unsafe def mapUnsafe [Monad m] (f : α → β) (x : NondetT m α) : NondetT m β :=
  Alts.map f x

@[implementedBy mapUnsafe]
protected constant map [Monad m] (f : α → β) (x : NondetT m α) : NondetT m β

@[inline]
unsafe def pureUnsafe [Monad m] (a : α) : NondetT m α :=
  Alts.pure a

@[implementedBy pureUnsafe]
protected constant pure [Monad m] (a : α) : NondetT m α

@[inline]
protected def failure [Monad m] : NondetT m α := id (α := m (Alts m α)) $
  pure Alts.nil

instance [Monad m] : Monad (NondetT m) where
  bind x f := Nondet.join (Nondet.map f x)
  pure     := Nondet.pure
  map      := Nondet.map

instance [Monad m] : Alternative (NondetT m) where
  failure := Nondet.failure
  orElse  := Nondet.append

@[inline]
unsafe def runUnsafe [Monad m] (x : NondetT m α) : m (Option (α × NondetT m α)) :=
  Alts.runUnsafe x

@[implementedBy runUnsafe]
protected constant NondetT.run [Monad m] (x : NondetT m α) : m (Option (α × NondetT m α))

protected def NondetT.run' [Monad m] (x : NondetT m α) : m (Option α) := do
  match (← x.run) with
  | some (a, _) => pure (some a)
  | none        => pure none

@[inline]
unsafe def chooseUnsafe [Monad m] (as : List α) : NondetT m α :=
  Alts.ofList as

@[implementedBy chooseUnsafe]
constant chooseImp [Monad m] (as : List α) : NondetT m α

class Choose (m : Type u → Type u) :=
  (choose : List α → m α)

export Choose (choose)

instance [MonadLift m n] [Choose m] : Choose n where
  choose := fun as => liftM (m := m) $ choose as

instance [Monad m] : Choose (NondetT m) where
  choose := chooseImp

@[inline]
unsafe def liftUnsafe [Monad m] (x : m α) : NondetT m α := id (α := m (Alts m α)) do
  let a ← x
  Alts.pure a

@[implementedBy liftUnsafe]
protected constant lift [Monad m] (x : m α) : NondetT m α

instance [Monad m] : MonadLift m (NondetT m) where
  monadLift := Nondet.lift

end Nondet

export Nondet (NondetT)

namespace ex1
-- The state is not backtrackable
abbrev M := NondetT $ StateT Nat $ IO

def checkVal (x : Nat) : M Nat := do
  IO.println s!"x: {x}"
  guard (x % 2 == 0)
  pure x

def f : M Nat := do
  let x ← Nondet.choose [1, 2, 3, 4, 5, 6, 7, 8]
  checkVal x

def h : M Nat := do
  let a ← f
  modify (· + 1)
  guard (a % 3 == 0)
  pure (a+1)

def g : IO Unit :=  do
  let (some (x, _), s) ← h.run.run 0 | throw $ IO.userError "failed"
  IO.println s!"x: {x}, s: {s}"

#eval g
end ex1

namespace ex2
-- The state is backtrackable
abbrev M := StateT Nat $ NondetT $ IO

def checkVal (x : Nat) : M Nat := do
  IO.println s!"x: {x}"
  guard (x % 2 == 0)
  pure x

def f : M Nat := do
  let x ← Nondet.choose [1, 2, 3, 4, 5, 6, 7, 8]
  checkVal x

def h : M Nat := do
  let a ← f
  modify (· + 1)
  guard (a % 3 == 0)
  pure (a+1)

def g : IO Unit :=  do
  let some ((x, s), _) ← (h.run 0).run | throw $ IO.userError "failed"
  IO.println s!"x: {x}, s: {s}"

#eval g
end ex2

namespace ex3
abbrev M := NondetT IO

def a : M Unit := IO.println "a"
def b : M Unit := IO.println "b"
def c : M Unit := IO.println "c"

def t1 : M Unit :=
  ((a <|> a) *> b) *> c

def t2 : M Unit :=
  (a <|> a) *> (b *> c)

#eval t1.run'
#eval t2.run'

end ex3
