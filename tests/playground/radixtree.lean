import init.lean.format
open Lean
universes u v w

inductive RadixNode (α : Type u)
| node (cs : Array RadixNode) : RadixNode
| leaf (vs : Array α) : RadixNode

instance RadixNode.inhabited {α : Type u} : Inhabited (RadixNode α) :=
⟨RadixNode.leaf Array.empty⟩

abbrev RadixTree.branching : USize := USize.ofNat 32

structure RadixTree (α : Type u) :=
/- Recall that we run out of memory if we have more than `usizeSz/8` elements.
   So, we can stop adding elements at `root` after `size > usizeSz`, and
   keep growing the `tail`. This modification allow us to use `USize` instead
   of `Nat` when traversing `root`. -/
(root    : RadixNode α := RadixNode.node (Array.mkEmpty RadixTree.branching.toNat))
(tail    : Array α     := Array.mkEmpty RadixTree.branching.toNat)
(size    : Nat         := 0)
(mh      : USize       := RadixTree.branching)
(tailOff : Nat         := 0)

namespace RadixTree
/- TODO:
   - Use proofs for showing that array accesses are not out of bounds.
   - Use bit shifting and masking operations instead of `/` and `%`.
-/
variables {α : Type u} {β : Type v}
open RadixNode

instance : Inhabited (RadixTree α) := ⟨{}⟩

def mkEmptyArray : Array α := Array.mkEmpty branching.toNat

partial def getAux [Inhabited α] : RadixNode α → USize → USize → α
| (node cs) i mh := getAux (cs.get (i / mh).toNat) (i % mh) (mh / branching)
| (leaf cs) i _  := cs.get i.toNat

def get [Inhabited α] (t : RadixTree α) (i : Nat) : α :=
if i >= t.tailOff then
  t.tail.get (i - t.tailOff)
else
  getAux t.root (USize.ofNat i) t.mh

partial def setAux : RadixNode α → USize → USize → α → RadixNode α
| (node cs) i mh a := node (cs.modify (i / mh).toNat $ λ c, setAux c (i % mh) (mh / branching) a)
| (leaf cs) i _  a := leaf (cs.set i.toNat a)

def set (t : RadixTree α) (i : Nat) (a : α) : RadixTree α :=
if i >= t.tailOff then
  { tail := t.tail.set (i - t.tailOff) a, .. t }
else
  { root := setAux t.root (USize.ofNat i) t.mh a, .. t }

partial def mkNewPath : USize → Array α → RadixNode α
| mh a :=
  if mh <= 1 then
    leaf a
  else
    node (mkEmptyArray.push (mkNewPath (mh / branching) a))

partial def insertNewLeaf : RadixNode α → USize → USize → Array α → RadixNode α
| (node cs) i mh a :=
  if i < branching then
    node (cs.push (leaf a))
  else
    let j := i / mh in
    if j.toNat < cs.size then
       node (cs.modify j.toNat $ λ c, insertNewLeaf c (i % mh) (mh / branching) a)
    else
       node (cs.push (mkNewPath (mh / branching) a))
| n         _ _  _ := n -- unreachable

def mkNewTail (t : RadixTree α) : RadixTree α :=
if t.size <= (t.mh * branching).toNat then
  { tail    := mkEmptyArray, root := insertNewLeaf t.root (USize.ofNat (t.size - 1)) t.mh t.tail,
    tailOff := t.size,
    .. t }
else
  { tail := Array.empty,
    root := let n := mkEmptyArray.push t.root in
            node (n.push (mkNewPath t.mh t.tail)),
    mh   := t.mh * branching,
    tailOff := t.size,
    .. t }

def tooBig : Nat := usizeSz / 8

def push (t : RadixTree α) (a : α) : RadixTree α :=
let r := { tail := t.tail.push a, size := t.size + 1, .. t } in
if r.tail.size < branching.toNat || t.size >= tooBig then
  r
else
  mkNewTail r

section
variables {m : Type v → Type v} [Monad m]
local attribute [instance] monadInhabited'

@[specialize] partial def mfoldlAux (f : β → α → m β) : RadixNode α → β → m β
| (node cs) b := cs.mfoldl (λ b c, mfoldlAux c b) b
| (leaf vs) b := vs.mfoldl f b

@[specialize] def mfoldl (f : β → α → m β) (b : β) (t : RadixTree α) : m β :=
do b ← mfoldlAux f t.root b, t.tail.mfoldl f b

end

@[inline] def foldl (f : β → α → β) (b : β) (t : RadixTree α) : β :=
Id.run (t.mfoldl f b)

def toList (t : RadixTree α) : List α :=
(t.foldl (λ xs x, x :: xs) []).reverse

section
variables {m : Type v → Type v} [Monad m]

@[specialize] partial def mmapAux (f : α → m β) : RadixNode α → m (RadixNode β)
| (node cs) := node <$> cs.mmap (λ c, mmapAux c)
| (leaf vs) := leaf <$> vs.mmap f

@[specialize] def mmap (f : α → m β) (t : RadixTree α) : m (RadixTree β) :=
do
  root ← mmapAux f t.root,
  tail ← t.tail.mmap f,
  pure { tail := tail, root := root, .. t }

end

@[inline] def map (f : α → β) (t : RadixTree α) : RadixTree β :=
Id.run (t.mmap f)

structure Stats :=
(numNodes : Nat) (depth : Nat) (tailSize : Nat)

partial def collectStats : RadixNode α → Stats → Nat → Stats
| (node cs) s d :=
  cs.foldl (λ s c, collectStats c s (d+1))
    { numNodes := s.numNodes + 1,
      depth    := Nat.max d s.depth, .. s }
| (leaf vs) s d := { numNodes := s.numNodes + 1, depth := Nat.max d s.depth, .. s }

def stats (r : RadixTree α) : Stats :=
collectStats r.root { numNodes := 0, depth := 0, tailSize := r.tail.size } 0

def Stats.toString (s : Stats) : String :=
toString [s.numNodes, s.depth, s.tailSize]

instance : HasToString Stats := ⟨Stats.toString⟩

partial def formatRawAux [HasFormat α] : RadixNode α → Format
| (node cs) := "Node" ++ Format.sbracket (cs.foldl (λ f c, f ++ Format.line ++ formatRawAux c) Format.nil)
| (leaf cs) := format cs.toList

partial def formatRaw [HasFormat α] (t : RadixTree α) : Format :=
Format.bracket "{" ("root :=" ++ Format.line ++ formatRawAux t.root ++ "," ++ Format.line ++
                    "tail :=" ++ Format.line ++ format t.tail.toList) "}"
end RadixTree

def List.toRadixTreeAux {α : Type u} : List α → RadixTree α → RadixTree α
| []      t := t
| (x::xs) t := List.toRadixTreeAux xs (t.push x)

def List.toRadixTree {α : Type u} (xs : List α) : RadixTree α :=
xs.toRadixTreeAux {}

abbrev PArray := RadixTree Nat
-- abbrev PArray := Array Nat

def mkRadixTree (n : Nat) : PArray :=
n.fold (λ i s, s.push i) { RadixTree . }
-- n.fold (λ i s, s.push i) Array.empty

def check (n : Nat) (p : Nat → Nat → Bool) (s : PArray) : IO Unit :=
n.mfor $ λ i, unless (p i (s.get i)) (throw (IO.userError ("failed at " ++ toString i ++ " " ++ toString (s.get i))))

def inc1 (n : Nat) (s : PArray) : PArray :=
n.fold (λ i s, s.set i (s.get i + 1)) s

def checkId (n : Nat) (s : PArray) : IO Unit :=
check n (==) s

def main (xs : List String) : IO Unit :=
do
let n := xs.head.toNat,
let t := mkRadixTree n,
-- IO.println t.formatRaw *>
checkId n t,
let t := inc1 n t,
check n (λ i v, v == i + 1) t,
IO.println t.size,
IO.println t.stats,
pure ()
