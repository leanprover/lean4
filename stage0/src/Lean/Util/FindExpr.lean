/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean
namespace Expr

namespace FindImpl

abbrev cacheSize : USize := 8192

structure State where
  keys : Array Expr -- Remark: our "unsafe" implementation relies on the fact that `()` is not a valid Expr

abbrev FindM := StateT State Id

unsafe def visited (e : Expr) (size : USize) : FindM Bool := do
  let s ← get
  let h := ptrAddrUnsafe e
  let i := h % size
  let k := s.keys.uget i lcProof
  if ptrAddrUnsafe k == h then
    pure true
  else
    modify fun s => { keys := s.keys.uset i e lcProof }
    pure false

@[specialize] unsafe def findM? (p : Expr → Bool) (size : USize) (e : Expr) : OptionT FindM Expr :=
  let rec visit (e : Expr) := do
    if (← visited e size)  then
      failure
    else if p e then
      pure e
    else match e with
      | Expr.forallE _ d b _   => visit d <|> visit b
      | Expr.lam _ d b _       => visit d <|> visit b
      | Expr.mdata _ b _       => visit b
      | Expr.letE _ t v b _    => visit t <|> visit v <|> visit b
      | Expr.app f a _         => visit f <|> visit a
      | Expr.proj _ _ b _      => visit b
      | e                      => failure
  visit e


unsafe def initCache : State :=
  { keys    := mkArray cacheSize.toNat (cast lcProof ()) }

@[inline] unsafe def findUnsafe? (p : Expr → Bool) (e : Expr) : Option Expr :=
  Id.run <| findM? p cacheSize e |>.run' initCache

end FindImpl

@[implementedBy FindImpl.findUnsafe?]
partial def find? (p : Expr → Bool) (e : Expr) : Option Expr :=
  /- This is a reference implementation for the unsafe one above -/
  if p e then
    some e
  else match e with
    | Expr.forallE _ d b _   => find? p d <|> find? p b
    | Expr.lam _ d b _       => find? p d <|> find? p b
    | Expr.mdata _ b _       => find? p b
    | Expr.letE _ t v b _    => find? p t <|> find? p v <|> find? p b
    | Expr.app f a _         => find? p f <|> find? p a
    | Expr.proj _ _ b _      => find? p b
    | e                      => none

/-- Return true if `e` occurs in `t` -/
def occurs (e : Expr) (t : Expr) : Bool :=
  (t.find? fun s => s == e).isSome

end Expr
end Lean
