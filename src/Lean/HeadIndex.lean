/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Expr

namespace Lean

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

def head : Expr → Expr
  | app f _ _      => head f
  | letE _ _ _ b _ => head b
  | mdata _ e _    => head e
  | e              => e

private def headNumArgsAux : Expr → Nat → Nat
  | app f _ _, n      => headNumArgsAux f (n + 1)
  | letE _ _ _ b _, n => headNumArgsAux b n
  | mdata _ e _, n    => headNumArgsAux e n
  | _, n              => n

def headNumArgs (e : Expr) : Nat :=
  headNumArgsAux e 0

/-
  Quick version that may fail if it "hits" a loose bound variable.
  This can happen, for example, if the input expression is of the form.
  ```
  let f := fun x => x + 1;
  f 0
  ```
-/
private def toHeadIndexQuick? : Expr → Option HeadIndex
  | mvar mvarId _           => HeadIndex.mvar mvarId
  | fvar fvarId _           => HeadIndex.fvar fvarId
  | const constName _ _     => HeadIndex.const constName
  | proj structName idx _ _ => HeadIndex.proj structName idx
  | sort _ _                => HeadIndex.sort
  | lam _ _ _ _             => HeadIndex.lam
  | forallE _ _ _ _         => HeadIndex.forallE
  | lit v _                 => HeadIndex.lit v
  | app f _ _               => toHeadIndexQuick? f
  | letE _ _ _ b _          => toHeadIndexQuick? b
  | mdata _ e _             => toHeadIndexQuick? e
  | _                       => none

/-
  Slower version of `toHeadIndexQuick?` that "expands" let-declarations to make
  sure we never hit a loose bound variable.
  The performance of the `letE` alternative can be improved, but this function should not be in the hotpath
  since `toHeadIndexQuick?` succeeds most of the time.
-/
private partial def toHeadIndexSlow : Expr → HeadIndex
  | mvar mvarId _           => HeadIndex.mvar mvarId
  | fvar fvarId _           => HeadIndex.fvar fvarId
  | const constName _ _     => HeadIndex.const constName
  | proj structName idx _ _ => HeadIndex.proj structName idx
  | sort _ _                => HeadIndex.sort
  | lam _ _ _ _             => HeadIndex.lam
  | forallE _ _ _ _         => HeadIndex.forallE
  | lit v _                 => HeadIndex.lit v
  | app f _ _               => toHeadIndexSlow f
  | letE _ _ v b _          => toHeadIndexSlow (b.instantiate1 v)
  | mdata _ e _             => toHeadIndexSlow e
  | _                       => panic! "unexpected expression kind"

def toHeadIndex (e : Expr) : HeadIndex :=
  match toHeadIndexQuick? e with
  | some i => i
  | none => toHeadIndexSlow e

end Expr
end Lean
