/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
import Lean.Util.PtrSet

namespace Lean
namespace Expr
namespace FindImpl

unsafe abbrev FindM := StateT (PtrSet Expr) Id

@[inline] unsafe def checkVisited (e : Expr) : OptionT FindM Unit := do
  if (← get).contains e then
    failure
  modify fun s => s.insert e

unsafe def findM? (p : Expr → Bool) (e : Expr) : OptionT FindM Expr :=
  let rec visit (e : Expr) := do
    checkVisited e
    if p e then
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

unsafe def findUnsafe? (p : Expr → Bool) (e : Expr) : Option Expr :=
  Id.run <| findM? p e |>.run' mkPtrSet

end FindImpl

@[implemented_by FindImpl.findUnsafe?]
def find? (p : Expr → Bool) (e : Expr) : Option Expr :=
  /- This is a reference implementation for the unsafe one above -/
  if p e then
    some e
  else match e with
    | .forallE _ d b _ => find? p d <|> find? p b
    | .lam _ d b _     => find? p d <|> find? p b
    | .mdata _ b       => find? p b
    | .letE _ t v b _  => find? p t <|> find? p v <|> find? p b
    | .app f a         => find? p f <|> find? p a
    | .proj _ _ b      => find? p b
    | _                => none

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

unsafe def findM? (p : Expr → FindStep) (e : Expr) : OptionT FindImpl.FindM Expr :=
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
