/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.array
universes u v w

inductive PersistentArrayNode (α : Type u)
| node (cs : Array PersistentArrayNode) : PersistentArrayNode
| leaf (vs : Array α)                   : PersistentArrayNode

instance PersistentArrayNode.inhabited {α : Type u} : Inhabited (PersistentArrayNode α) :=
⟨PersistentArrayNode.leaf Array.empty⟩

abbrev PersistentArray.initShift : USize := 5
abbrev PersistentArray.branching : USize := USize.ofNat (2 ^ PersistentArray.initShift.toNat)

structure PersistentArray (α : Type u) :=
/- Recall that we run out of memory if we have more than `usizeSz/8` elements.
   So, we can stop adding elements at `root` after `size > usizeSz`, and
   keep growing the `tail`. This modification allow us to use `USize` instead
   of `Nat` when traversing `root`. -/
(root    : PersistentArrayNode α := PersistentArrayNode.node (Array.mkEmpty PersistentArray.branching.toNat))
(tail    : Array α               := Array.mkEmpty PersistentArray.branching.toNat)
(size    : Nat                   := 0)
(shift   : USize                 := PersistentArray.initShift)
(tailOff : Nat                   := 0)

abbrev PArray (α : Type u) := PersistentArray α

namespace PersistentArray
/- TODO: use proofs for showing that array accesses are not out of bounds.
   We can do it after we reimplement the tactic framework. -/
variables {α : Type u} {β : Type v}
open PersistentArrayNode

instance : Inhabited (PersistentArray α) := ⟨{}⟩

def mkEmptyArray : Array α := Array.mkEmpty branching.toNat

abbrev mul2Shift (i : USize) (shift : USize) : USize := USize.shift_left i shift
abbrev div2Shift (i : USize) (shift : USize) : USize := USize.shift_right i shift
abbrev mod2Shift (i : USize) (shift : USize) : USize := USize.land i ((USize.shift_left 1 shift) - 1)

partial def getAux [Inhabited α] : PersistentArrayNode α → USize → USize → α
| (node cs) i shift := getAux (cs.get (div2Shift i shift).toNat) (mod2Shift i shift) (shift - initShift)
| (leaf cs) i _     := cs.get i.toNat

def get [Inhabited α] (t : PersistentArray α) (i : Nat) : α :=
if i >= t.tailOff then
  t.tail.get (i - t.tailOff)
else
  getAux t.root (USize.ofNat i) t.shift

partial def setAux : PersistentArrayNode α → USize → USize → α → PersistentArrayNode α
| (node cs) i shift a :=
  let j     := div2Shift i shift in
  let i     := mod2Shift i shift in
  let shift := shift - initShift in
  node $ cs.modify j.toNat $ λ c, setAux c i shift a
| (leaf cs) i _     a := leaf (cs.set i.toNat a)

def set (t : PersistentArray α) (i : Nat) (a : α) : PersistentArray α :=
if i >= t.tailOff then
  { tail := t.tail.set (i - t.tailOff) a, .. t }
else
  { root := setAux t.root (USize.ofNat i) t.shift a, .. t }

@[specialize] partial def modifyAux [Inhabited α] (f : α → α) : PersistentArrayNode α → USize → USize → PersistentArrayNode α
| (node cs) i shift :=
  let j     := div2Shift i shift in
  let i     := mod2Shift i shift in
  let shift := shift - initShift in
  node $ cs.modify j.toNat $ λ c, modifyAux c i shift
| (leaf cs) i _     := leaf (cs.modify i.toNat f)

@[specialize] def modify [Inhabited α] (t : PersistentArray α) (i : Nat) (f : α → α) : PersistentArray α :=
if i >= t.tailOff then
  { tail := t.tail.modify (i - t.tailOff) f, .. t }
else
  { root := modifyAux f t.root (USize.ofNat i) t.shift, .. t }

partial def mkNewPath : USize → Array α → PersistentArrayNode α
| shift a :=
  if shift == 0 then
    leaf a
  else
    node (mkEmptyArray.push (mkNewPath (shift - initShift) a))

partial def insertNewLeaf : PersistentArrayNode α → USize → USize → Array α → PersistentArrayNode α
| (node cs) i shift a :=
  if i < branching then
    node (cs.push (leaf a))
  else
    let j     := div2Shift i shift in
    let i     := mod2Shift i shift in
    let shift := shift - initShift in
    if j.toNat < cs.size then
       node $ cs.modify j.toNat $ λ c, insertNewLeaf c i shift a
    else
       node $ cs.push $ mkNewPath shift a
| n _ _ _ := n -- unreachable

def mkNewTail (t : PersistentArray α) : PersistentArray α :=
if t.size <= (mul2Shift 1 (t.shift + initShift)).toNat then
  { tail    := mkEmptyArray, root := insertNewLeaf t.root (USize.ofNat (t.size - 1)) t.shift t.tail,
    tailOff := t.size,
    .. t }
else
  { tail := Array.empty,
    root := let n := mkEmptyArray.push t.root in
            node (n.push (mkNewPath t.shift t.tail)),
    shift   := t.shift + initShift,
    tailOff := t.size,
    .. t }

def tooBig : Nat := usizeSz / 8

def push (t : PersistentArray α) (a : α) : PersistentArray α :=
let r := { tail := t.tail.push a, size := t.size + 1, .. t } in
if r.tail.size < branching.toNat || t.size >= tooBig then
  r
else
  mkNewTail r

section
variables {m : Type v → Type v} [Monad m]

@[specialize] partial def mfoldlAux (f : β → α → m β) : PersistentArrayNode α → β → m β
| (node cs) b := cs.mfoldl (λ b c, mfoldlAux c b) b
| (leaf vs) b := vs.mfoldl f b

@[specialize] def mfoldl (f : β → α → m β) (b : β) (t : PersistentArray α) : m β :=
do b ← mfoldlAux f t.root b, t.tail.mfoldl f b

end

@[inline] def foldl (f : β → α → β) (b : β) (t : PersistentArray α) : β :=
Id.run (t.mfoldl f b)

def toList (t : PersistentArray α) : List α :=
(t.foldl (λ xs x, x :: xs) []).reverse

section
variables {m : Type v → Type v} [Monad m]

@[specialize] partial def mmapAux (f : α → m β) : PersistentArrayNode α → m (PersistentArrayNode β)
| (node cs) := node <$> cs.mmap (λ c, mmapAux c)
| (leaf vs) := leaf <$> vs.mmap f

@[specialize] def mmap (f : α → m β) (t : PersistentArray α) : m (PersistentArray β) :=
do
  root ← mmapAux f t.root,
  tail ← t.tail.mmap f,
  pure { tail := tail, root := root, .. t }

end

@[inline] def map (f : α → β) (t : PersistentArray α) : PersistentArray β :=
Id.run (t.mmap f)

structure Stats :=
(numNodes : Nat) (depth : Nat) (tailSize : Nat)

partial def collectStats : PersistentArrayNode α → Stats → Nat → Stats
| (node cs) s d :=
  cs.foldl (λ s c, collectStats c s (d+1))
    { numNodes := s.numNodes + 1,
      depth    := Nat.max d s.depth, .. s }
| (leaf vs) s d := { numNodes := s.numNodes + 1, depth := Nat.max d s.depth, .. s }

def stats (r : PersistentArray α) : Stats :=
collectStats r.root { numNodes := 0, depth := 0, tailSize := r.tail.size } 0

def Stats.toString (s : Stats) : String :=
toString [s.numNodes, s.depth, s.tailSize]

instance : HasToString Stats := ⟨Stats.toString⟩

end PersistentArray

def List.toPersistentArrayAux {α : Type u} : List α → PersistentArray α → PersistentArray α
| []      t := t
| (x::xs) t := List.toPersistentArrayAux xs (t.push x)

def List.toPersistentArray {α : Type u} (xs : List α) : PersistentArray α :=
xs.toPersistentArrayAux {}
