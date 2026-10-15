import Lean.ConstTrie

/-!
Lookups in constant prefix trees whose nodes have at least `2^16 - 1` children, which need wide
child-index offsets: a single module's trie and the lazily merged view of several modules, where
the root collects the top-level names of all of them.
-/

open Lean

def names (pre : String) (n : Nat) : Array Name :=
  (Array.range n).map fun i => Name.mkSimple s!"{pre}{i}"

def wide := names "a" 70000

/-- A single node with 70000 children. -/
def wideTrie := ConstTrie.ofNames wide

#guard wide.all fun n => (wideTrie.find? n).isSome
#guard (wideTrie.find? `missing).isNone
#guard (wideTrie.find? (.str `a0 "x")).isNone

def part₁ := names "b" 40000
def part₂ := names "c" 40000

/-- Neither module's root is wide, but the merged root has 80000 children. -/
def merged : ImportedConsts Unit :=
  ImportedConsts.mergeModuleTreesLazy #[(0, ConstTrie.ofNames part₁),
    (1, ConstTrie.ofNames (part₂.push `b0))]

#guard part₁.all fun n => merged.findModIdx? n == some 0
#guard part₂.all fun n => merged.findModIdx? n == some 1
#guard (merged.find? `missing).isNone

/-- Narrow nodes keep working alongside wide ones. -/
def narrow := ConstTrie.ofNames #[`x, `x.y, `x.z, `w]

#guard [`x, `x.y, `x.z, `w].all fun n => (narrow.find? n).isSome
#guard (narrow.find? `x.q).isNone
