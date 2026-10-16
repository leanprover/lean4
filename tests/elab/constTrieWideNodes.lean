import Lean.ConstTrie

/-!
Lookups via constant locators (`ConstTrie`) with very wide nodes: a single module whose root has
70000 children, and the lazily merged view of several modules, whose root collects the top-level
names of all of them. Also covers names below a module's own names, which the locator covers by
their root instead of storing them.
-/

open Lean

def names (pre : String) (n : Nat) : Array Name :=
  (Array.range n).map fun i => Name.mkSimple s!"{pre}{i}"

def units (ns : Array Name) : Array Unit := ns.map fun _ => ()

def wide := names "a" 70000

/-- A single module with 70000 top-level names. -/
def wideMod := ModuleConsts.ofArrays wide (units wide)

#guard wide.all fun n => (wideMod.find? n).isSome
#guard (wideMod.find? `missing).isNone
#guard (wideMod.find? (.str `a0 "x")).isNone

def part₁ := names "b" 40000
def part₂ := names "c" 40000

/-- Neither module's root is wide, but the merged root has 80000 children. -/
def merged : ImportedConsts Unit :=
  ImportedConsts.mergeModules 2 #[(0, ModuleConsts.ofArrays part₁ (units part₁)),
    (1, ModuleConsts.ofArrays (part₂.push `b0) (units (part₂.push `b0)))]

#guard part₁.all fun n => merged.findModIdx? n == some 0
#guard part₂.all fun n => merged.findModIdx? n == some 1
#guard (merged.find? `missing).isNone

/-- Names below other names of the module are found via the covering root. -/
def nested := #[`x, `x.y, `x.z, `x.y.w, `w, `v.u, `v.u.t]
def nestedMod := ModuleConsts.ofArrays nested (units nested)

#guard nested.all fun n => (nestedMod.find? n).isSome
#guard [`x.q, `x.y.q, `v, `v.q, `q].all fun n => (nestedMod.find? n).isNone

/--
Modules declaring names below another module's name: lookups consult every module whose root
covers the name.
-/
def owner := #[`Foo, `Foo.mk, `Foo.x]
def other := #[`Foo.bar, `Foo.bar.baz, `Qux]
def mixed : ImportedConsts Unit :=
  ImportedConsts.mergeModules 2 #[(0, ModuleConsts.ofArrays owner (units owner)),
    (1, ModuleConsts.ofArrays other (units other))]

#guard owner.all fun n => mixed.findModIdx? n == some 0
#guard other.all fun n => mixed.findModIdx? n == some 1
#guard [`Foo.y, `Foo.bar.q, `Qux.q].all fun n => (mixed.find? n).isNone

/-- `collectDuplicates` finds names declared by two modules, also below another module's root. -/
def dupA := #[`Foo, `Foo.x, `Bar.y]
def dupB := #[`Foo.x, `Bar, `Bar.y, `Baz]

/-- info: [`Bar.y, `Foo.x] -/
#guard_msgs in
#eval (ImportedConsts.collectDuplicates 2 #[(0, ModuleConsts.ofArrays dupA (units dupA)),
  (1, ModuleConsts.ofArrays dupB (units dupB))]).map (·.name) |>.qsort (·.toString < ·.toString)
  |>.toList
