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
variables {α : Type u}
open PersistentArrayNode

def empty : PersistentArray α :=
{}

def isEmpty (a : PersistentArray α) : Bool :=
a.size == 0

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
  let j     := div2Shift i shift;
  let i     := mod2Shift i shift;
  let shift := shift - initShift;
  node $ cs.modify j.toNat $ fun c => setAux c i shift a
| (leaf cs) i _     a := leaf (cs.set i.toNat a)

def set (t : PersistentArray α) (i : Nat) (a : α) : PersistentArray α :=
if i >= t.tailOff then
  { tail := t.tail.set (i - t.tailOff) a, .. t }
else
  { root := setAux t.root (USize.ofNat i) t.shift a, .. t }

@[specialize] partial def modifyAux [Inhabited α] (f : α → α) : PersistentArrayNode α → USize → USize → PersistentArrayNode α
| (node cs) i shift :=
  let j     := div2Shift i shift;
  let i     := mod2Shift i shift;
  let shift := shift - initShift;
  node $ cs.modify j.toNat $ fun c => modifyAux c i shift
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
    let j     := div2Shift i shift;
    let i     := mod2Shift i shift;
    let shift := shift - initShift;
    if j.toNat < cs.size then
       node $ cs.modify j.toNat $ fun c => insertNewLeaf c i shift a
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
    root := let n := mkEmptyArray.push t.root;
            node (n.push (mkNewPath t.shift t.tail)),
    shift   := t.shift + initShift,
    tailOff := t.size,
    .. t }

def tooBig : Nat := usizeSz / 8

def push (t : PersistentArray α) (a : α) : PersistentArray α :=
let r := { tail := t.tail.push a, size := t.size + 1, .. t };
if r.tail.size < branching.toNat || t.size >= tooBig then
  r
else
  mkNewTail r

private def emptyArray {α : Type u} : Array (PersistentArrayNode α) :=
Array.mkEmpty PersistentArray.branching.toNat

partial def popLeaf : PersistentArrayNode α → Option (Array α) × Array (PersistentArrayNode α)
| n@(node cs) :=
  if h : cs.size ≠ 0 then
    let idx : Fin cs.size := ⟨cs.size - 1, Nat.predLt h⟩;
    let last := cs.fget idx;
    match popLeaf last with
    | (none,   _)       => (none, emptyArray)
    | (some l, newLast) =>
      if newLast.size == 0 then
        let cs := cs.pop;
        if cs.isEmpty then (some l, emptyArray) else (some l, cs)
      else
        (some l, cs.fset idx (node newLast))
  else
    (none, emptyArray)
| (leaf vs) := (some vs, emptyArray)

def pop (t : PersistentArray α) : PersistentArray α :=
if t.tail.size > 0 then
  { tail := t.tail.pop, size := t.size - 1, .. t }
else
  match popLeaf t.root with
  | (none, _) => t
  | (some last, newRoots) =>
    let last       := last.pop;
    let newSize    := t.size - 1;
    let newTailOff := newSize - last.size;
    if newRoots.size == 1 then
      { root    := newRoots.get 0,
        shift   := t.shift - initShift,
        size    := newSize,
        tail    := last,
        tailOff := newTailOff }
    else
      { root    := node newRoots,
        size    := newSize,
        tail    := last,
        tailOff := newTailOff,
        .. t }

section
variables {m : Type v → Type w} [Monad m]
variable {β : Type v}

@[specialize] partial def mfoldlAux (f : β → α → m β) : PersistentArrayNode α → β → m β
| (node cs) b := cs.mfoldl (fun b c => mfoldlAux c b) b
| (leaf vs) b := vs.mfoldl f b

@[specialize] def mfoldl (t : PersistentArray α) (f : β → α → m β) (b : β) : m β :=
do b ← mfoldlAux f t.root b; t.tail.mfoldl f b

@[specialize] partial def mfindAux (f : α → m (Option β)) : PersistentArrayNode α → m (Option β)
| (node cs) := cs.mfind (fun c => mfindAux c)
| (leaf vs) := vs.mfind f

@[specialize] def mfind (t : PersistentArray α) (f : α → m (Option β)) : m (Option β) :=
do b ← mfindAux f t.root;
   match b with
   | none   => t.tail.mfind f
   | some b => pure (some b)

@[specialize] partial def mfindRevAux (f : α → m (Option β)) : PersistentArrayNode α → m (Option β)
| (node cs) := cs.mfindRev (fun c => mfindRevAux c)
| (leaf vs) := vs.mfindRev f

@[specialize] def mfindRev (t : PersistentArray α) (f : α → m (Option β)) : m (Option β) :=
do b ← t.tail.mfindRev f;
   match b with
   | none   => mfindRevAux f t.root
   | some b => pure (some b)

partial def mfoldlFromAux (f : β → α → m β) : PersistentArrayNode α → USize → USize → β → m β
| (node cs) i shift b := do
  let j    := (div2Shift i shift).toNat;
  b ← mfoldlFromAux (cs.get j) (mod2Shift i shift) (shift - initShift) b;
  cs.mfoldlFrom (fun b c => mfoldlAux f c b) b (j+1)
| (leaf vs) i _ b := vs.mfoldlFrom f b i.toNat

def mfoldlFrom (t : PersistentArray α) (f : β → α → m β) (b : β) (ini : Nat) : m β :=
if ini >= t.tailOff then
  t.tail.mfoldlFrom f b (ini - t.tailOff)
else do
  b ← mfoldlFromAux f t.root (USize.ofNat ini) t.shift b;
  t.tail.mfoldl f b

@[specialize] partial def mforAux (f : α → m β) : PersistentArrayNode α → m PUnit
| (node cs) := cs.mfor (fun c => mforAux c)
| (leaf vs) := vs.mfor f

@[specialize] def mfor (t : PersistentArray α) (f : α → m β) : m PUnit :=
mforAux f t.root *> t.tail.mfor f

end

@[inline] def foldl {β} (t : PersistentArray α) (f : β → α → β) (b : β) : β :=
Id.run (t.mfoldl f b)

@[inline] def find {β} (t : PersistentArray α) (f : α → (Option β)) : Option β :=
Id.run (t.mfind f)

@[inline] def findRev {β} (t : PersistentArray α) (f : α → (Option β)) : Option β :=
Id.run (t.mfindRev f)

@[inline] def foldlFrom {β} (t : PersistentArray α) (f : β → α → β) (b : β) (ini : Nat) : β :=
Id.run (t.mfoldlFrom f b ini)

def toList (t : PersistentArray α) : List α :=
(t.foldl (fun xs x => x :: xs) []).reverse

section
variables {m : Type u → Type v} [Monad m]
variable {β : Type u}

@[specialize] partial def mmapAux (f : α → m β) : PersistentArrayNode α → m (PersistentArrayNode β)
| (node cs) := node <$> cs.mmap (fun c => mmapAux c)
| (leaf vs) := leaf <$> vs.mmap f

@[specialize] def mmap (f : α → m β) (t : PersistentArray α) : m (PersistentArray β) :=
do
  root ← mmapAux f t.root;
  tail ← t.tail.mmap f;
  pure { tail := tail, root := root, .. t }

end

@[inline] def map {β} (f : α → β) (t : PersistentArray α) : PersistentArray β :=
Id.run (t.mmap f)

structure Stats :=
(numNodes : Nat) (depth : Nat) (tailSize : Nat)

partial def collectStats : PersistentArrayNode α → Stats → Nat → Stats
| (node cs) s d :=
  cs.foldl (fun s c => collectStats c s (d+1))
    { numNodes := s.numNodes + 1,
      depth    := Nat.max d s.depth, .. s }
| (leaf vs) s d := { numNodes := s.numNodes + 1, depth := Nat.max d s.depth, .. s }

def stats (r : PersistentArray α) : Stats :=
collectStats r.root { numNodes := 0, depth := 0, tailSize := r.tail.size } 0

def Stats.toString (s : Stats) : String :=
"{nodes := " ++ toString s.numNodes ++ ", depth := " ++ toString s.depth  ++ ", tail size := " ++ toString s.tailSize ++ "}"

instance : HasToString Stats := ⟨Stats.toString⟩

end PersistentArray

def List.toPersistentArrayAux {α : Type u} : List α → PersistentArray α → PersistentArray α
| []      t := t
| (x::xs) t := List.toPersistentArrayAux xs (t.push x)

def List.toPersistentArray {α : Type u} (xs : List α) : PersistentArray α :=
xs.toPersistentArrayAux {}
