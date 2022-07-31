/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Expr

namespace Lean

/--
Datastructure for representing the "head symbol" of an expression.
It is the key of `KExprMap`.
Examples:
- The head of `f a` is `.const f`
- The head of `let x := 1; f x` is `.const f`
- The head of `fun x => fun` is `.lam`

`HeadIndex` is a very simple index, and is used in situations where
we want to find definitionally equal terms, but we want to minimize
the search by checking only pairs of terms that have the same
`HeadIndex`.
-/
inductive HeadIndex where
  | fvar (fvarId : FVarId)
  | mvar (mvarId : MVarId)
  | const (constName : Name)
  | proj (structName : Name) (idx : Nat)
  | lit (litVal : Literal)
  | sort
  | lam
  | forallE
  deriving Inhabited, BEq, Repr

namespace HeadIndex

/-- Hash code for a `HeadIndex` value. -/
protected def HeadIndex.hash : HeadIndex → UInt64
  | fvar fvarId         => mixHash 11 <| hash fvarId
  | mvar mvarId         => mixHash 13 <| hash mvarId
  | const constName     => mixHash 17 <| hash constName
  | proj structName idx => mixHash 19 <| mixHash (hash structName) (hash idx)
  | lit litVal          => mixHash 23 <| hash litVal
  | sort                => 29
  | lam                 => 31
  | forallE             => 37

instance : Hashable HeadIndex := ⟨HeadIndex.hash⟩

end HeadIndex

namespace Expr

/-- Return the number of arguments in the given expression with respect to its `HeadIndex` -/
def headNumArgs (e : Expr) : Nat :=
  go e 0
where
  go : Expr → Nat → Nat
  | app f _, n        => go f (n + 1)
  | letE _ _ _ b _, n => go b n
  | mdata _ e, n      => go e n
  | _, n              => n

/--
  Quick version that may fail if it "hits" a loose bound variable.
  This can happen, for example, if the input expression is of the form.
  ```
  let f := fun x => x + 1;
  f 0
  ```
-/
private def toHeadIndexQuick? : Expr → Option HeadIndex
  | mvar mvarId             => HeadIndex.mvar mvarId
  | fvar fvarId             => HeadIndex.fvar fvarId
  | const constName _       => HeadIndex.const constName
  | proj structName idx _   => HeadIndex.proj structName idx
  | sort _                  => HeadIndex.sort
  | lam ..                  => HeadIndex.lam
  | forallE ..              => HeadIndex.forallE
  | lit v                   => HeadIndex.lit v
  | app f _                 => toHeadIndexQuick? f
  | letE _ _ _ b _          => toHeadIndexQuick? b
  | mdata _ e               => toHeadIndexQuick? e
  | _                       => none

/--
  Slower version of `toHeadIndexQuick?` that "expands" let-declarations to make
  sure we never hit a loose bound variable.
  The performance of the `letE` alternative can be improved, but this function should not be in the hotpath
  since `toHeadIndexQuick?` succeeds most of the time.
-/
private partial def toHeadIndexSlow : Expr → HeadIndex
  | mvar mvarId             => HeadIndex.mvar mvarId
  | fvar fvarId             => HeadIndex.fvar fvarId
  | const constName _       => HeadIndex.const constName
  | proj structName idx _   => HeadIndex.proj structName idx
  | sort _                  => HeadIndex.sort
  | lam ..                  => HeadIndex.lam
  | forallE ..              => HeadIndex.forallE
  | lit v                   => HeadIndex.lit v
  | app f _                 => toHeadIndexSlow f
  | letE _ _ v b _          => toHeadIndexSlow (b.instantiate1 v)
  | mdata _ e               => toHeadIndexSlow e
  | _                       => panic! "unexpected expression kind"

/--
Convert the given expression into a `HeadIndex`.
-/
def toHeadIndex (e : Expr) : HeadIndex :=
  match toHeadIndexQuick? e with
  | some i => i
  | none => toHeadIndexSlow e

end Expr
end Lean
