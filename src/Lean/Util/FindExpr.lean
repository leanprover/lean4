/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr
import Lean.Util.PtrSet

namespace Lean
namespace Expr
namespace FindImpl

unsafe abbrev FindM (m) := StateT (PtrSet Expr) m

@[inline] unsafe def checkVisited [Monad m] (e : Expr) : OptionT (FindM m) Unit := do
  if (← get).contains e then
    failure
  modify fun s => s.insert e

unsafe def findM? [Monad m] (p : Expr → m Bool) (e : Expr) : OptionT (FindM m) Expr :=
  let rec visit (e : Expr) := do
    checkVisited e
    if ← p e then
      pure e
    else match e with
      | .forallE _ d b _ => visit d <|> visit b
      | .lam _ d b _     => visit d <|> visit b
      | .mdata _ b       => visit b
      | .letE _ t v b _  => visit t <|> visit v <|> visit b
      | .app f a         => visit f <|> visit a
      | .proj _ _ b      => visit b
      | _                => failure
  visit e

unsafe def findUnsafeM? {m} [Monad m] (p : Expr → m Bool) (e : Expr) : m (Option Expr) :=
  findM? p e |>.run' mkPtrSet

@[inline] unsafe def findUnsafe? (p : Expr → Bool) (e : Expr) : Option Expr := findUnsafeM? (m := Id) p e

end FindImpl

/--
Find a subexpression on which the (monadic) predicate `p` returns true.

In compiled code, this is replaced by a fast implementation which uses a cache.

Note that if `p` is not pure (e.g. it uses a cache), then this reference implementation may not
match the compiled behavior! In particular, the compiled implementation will not re-evaluate `p`
on repeated subterms.

Please use this function cautiously; if it becomes a source of bugs, we may remove it.

(See `find?` below for a pure version.)
-/

@[implemented_by FindImpl.findUnsafeM?]
def findM? [Monad m] (p : Expr → m Bool) (e : Expr) : m (Option Expr) := do
  if ← p e then
    return some e
  else match e with
    | .forallE _ d b _ => findM? p d <||> findM? p b
    | .lam _ d b _     => findM? p d <||> findM? p b
    | .mdata _ b       => findM? p b
    | .letE _ t v b _  => findM? p t <||> findM? p v <||> findM? p b
    | .app f a         => findM? p f <||> findM? p a
    | .proj _ _ b      => findM? p b
    | _                => pure none

@[implemented_by FindImpl.findUnsafe?]
def find? (p : Expr → Bool) (e : Expr) : Option Expr := findM? (m := Id) p e

/-- Return true if `e` occurs in `t` -/
def occurs (e : Expr) (t : Expr) : Bool :=
  (t.find? fun s => s == e).isSome


/--
  Return type for `findExt?` function argument.
-/
inductive FindStep where
  /-- Found desired subterm -/ | found
  /-- Search subterms -/ | visit
  /-- Do not search subterms -/ | done

namespace FindExtImpl

unsafe def findM? (p : Expr → FindStep) (e : Expr) : OptionT (FindImpl.FindM Id) Expr :=
  visit e
where
  visitApp (e : Expr) :=
    match e with
    | .app f a .. => visitApp f <|> visit a
    | e => visit e

  visit (e : Expr) := do
    FindImpl.checkVisited e
    match p e with
      | .done  => failure
      | .found => pure e
      | .visit =>
        match e with
        | .forallE _ d b _ => visit d <|> visit b
        | .lam _ d b _     => visit d <|> visit b
        | .mdata _ b       => visit b
        | .letE _ t v b _  => visit t <|> visit v <|> visit b
        | .app ..          => visitApp e
        | .proj _ _ b      => visit b
        | _                => failure

unsafe def findUnsafe? (p : Expr → FindStep) (e : Expr) : Option Expr :=
  Id.run <| findM? p e |>.run' mkPtrSet

end FindExtImpl

/--
  Similar to `find?`, but `p` can return `FindStep.done` to interrupt the search on subterms.
  Remark: Differently from `find?`, we do not invoke `p` for partial applications of an application. -/
@[implemented_by FindExtImpl.findUnsafe?]
opaque findExt? (p : Expr → FindStep) (e : Expr) : Option Expr

end Expr
end Lean
