/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski

Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Linter.Basic

public section

namespace Lean.Linter.Clippy
open Elab Command

/--
Enables the 'unnecessary `<;>`' linter. This will warn whenever the `<;>` tactic combinator
is used when `;` would work.

```
example : True := by apply id <;> trivial
```
The `<;>` is unnecessary here because `apply id` only makes one subgoal.
Prefer `apply id; trivial` instead.

In some cases, the `<;>` is syntactically necessary because a single tactic is expected:
```
example : True := by
  cases () with apply id <;> apply id
  | unit => trivial
```
In this case, you should use parentheses, as in `(apply id; apply id)`:
```
example : True := by
  cases () with (apply id; apply id)
  | unit => trivial
```
-/
register_builtin_option linter.clippy.unnecessarySeqFocus : Bool := {
  defValue := false
  descr := "enable the 'unnecessary <;>' linter"
}

namespace UnnecessarySeqFocus

/--
The set of tactic syntax kinds that act on multiple goals — meaning `tac` differs from
`focus tac`. Used to suppress false positives where `tac1 <;> tac2` cannot be replaced by
`(tac1; tac2)` because that would expose `tac2` to a different set of goals.

Other modules can extend this set in their own `builtin_initialize` block by calling
`addBuiltinMultigoalKinds`.
-/
builtin_initialize multigoalKindsRef : IO.Ref Lean.NameSet ← IO.mkRef {}

/-- Register `k` as a multigoal tactic syntax kind. -/
def addBuiltinMultigoalKind (k : SyntaxNodeKind) : IO Unit :=
  multigoalKindsRef.modify (·.insert k)

/-- Register `ks` as multigoal tactic syntax kinds. -/
def addBuiltinMultigoalKinds (ks : Array SyntaxNodeKind) : IO Unit :=
  multigoalKindsRef.modify fun s => ks.foldl (·.insert ·) s

builtin_initialize
  addBuiltinMultigoalKinds #[
    ``Parser.Tactic.«tacticNext_=>_»,
    ``Parser.Tactic.allGoals,
    ``Parser.Tactic.anyGoals,
    ``Parser.Tactic.case,
    ``Parser.Tactic.case',
    ``Parser.Tactic.Conv.«convNext__=>_»,
    ``Parser.Tactic.Conv.allGoals,
    ``Parser.Tactic.Conv.anyGoals,
    ``Parser.Tactic.Conv.case,
    ``Parser.Tactic.Conv.case',
    ``Parser.Tactic.rotateLeft,
    ``Parser.Tactic.rotateRight,
    ``Parser.Tactic.show,
    ``Parser.Tactic.tacticStop_
  ]

/-- Whether `k` is a multigoal tactic kind, per `multigoalKindsRef`. -/
def isMultigoalKind (k : SyntaxNodeKind) : BaseIO Bool :=
  return (← multigoalKindsRef.get).contains k

/-- The information we record for each `<;>` node appearing in the syntax. -/
structure Entry where
  /-- The `<;>` node itself. -/
  stx : Syntax
  /--
  * `true`: this `<;>` has been used unnecessarily at least once
  * `false`: it has never been executed
  * If it has been used properly at least once, the entry is removed from the table.
  -/
  used : Bool

/-- The monad for collecting used tactic syntaxes. -/
abbrev M (ω) := StateRefT (Std.HashMap Lean.Syntax.Range Entry) (ST ω)

/-- True if this is a `<;>` node in either `tactic` or `conv` classes. -/
@[inline] def isSeqFocus (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Tactic.«tactic_<;>_» || k == ``Parser.Tactic.Conv.«conv_<;>_»

/-- Accumulates the set of tactic syntaxes that should be evaluated at least once. -/
@[specialize] partial def getTactics {ω} (stx : Syntax) : M ω Unit := do
  if let .node _ k args := stx then
    if isSeqFocus k then
      if let some r := stx.getRange? true then
        modify fun m => m.insert r { stx, used := false }
    args.forM getTactics

/--
Traverse the info tree down a given path.
Each `(n, i)` means that the array must have length `n` and we will descend into the `i`'th child.
-/
def getPath : Info → PersistentArray InfoTree → List ((n : Nat) × Fin n) → Option Info
  | i, _, [] => some i
  | _, c, ⟨n, i, h⟩::ns =>
    if e : c.size = n then
      if let .node i c' := c[i]'(e ▸ h) then getPath i c' ns else none
    else none

mutual
variable (multigoals : Lean.NameSet)
/-- Search for tactic executions in the info tree and remove executed tactic syntaxes. -/
partial def markUsedTacticsList {ω} (trees : PersistentArray InfoTree) : M ω Unit :=
  trees.forM markUsedTactics

/-- Search for tactic executions in the info tree and remove executed tactic syntaxes. -/
partial def markUsedTactics {ω} : InfoTree → M ω Unit
  | .node i c => do
    if let .ofTacticInfo i := i then
      if let some r := i.stx.getRange? true then
      if let some entry := (← get)[r]? then
      if i.stx.getKind == ``Parser.Tactic.«tactic_<;>_» then
        let isBad := do
          unless i.goalsBefore.length == 1 || !multigoals.contains i.stx[0].getKind do
            none
          -- Note: this uses the exact sequence of tactic applications
          -- in the macro expansion of `<;> : tactic`
          let .ofTacticInfo i ← getPath (.ofTacticInfo i) c
            [⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨5, 0⟩] | none
          guard <| i.goalsAfter.length == 1
        modify fun s => if isBad.isSome then s.insert r { entry with used := true } else s.erase r
      else if i.stx.getKind == ``Parser.Tactic.Conv.«conv_<;>_» then
        let isBad := do
          unless i.goalsBefore.length == 1 || !multigoals.contains i.stx[0].getKind do
            none
          -- Note: this uses the exact sequence of tactic applications
          -- in the macro expansion of `<;> : conv`
          let .ofTacticInfo i ← getPath (.ofTacticInfo i) c
            [⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨5, 0⟩] | none
          guard <| i.goalsAfter.length == 1
        modify fun s => if isBad.isSome then s.insert r { entry with used := true } else s.erase r
    markUsedTacticsList c
  | .context _ t => markUsedTactics t
  | .hole _ => pure ()

end

@[inherit_doc Lean.Linter.Clippy.linter.clippy.unnecessarySeqFocus]
def unnecessarySeqFocusLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValueClippy linter.clippy.unnecessarySeqFocus (← getLinterOptions)
      && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  let multigoals ← multigoalKindsRef.get
  let go {ω} : M ω Unit := do
    getTactics stx
    markUsedTacticsList multigoals trees
  let (_, map) := runST fun _ => go.run {}
  let unused := map.fold (init := #[]) fun acc r { stx, used } =>
    if used then acc.push (stx[1].getRange?.getD r, stx[1]) else acc
  let key (r : Lean.Syntax.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : Lean.Syntax.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unused.qsort (key ·.1 < key ·.1) do
    if last.start ≤ r.start && r.stop ≤ last.stop then continue
    Linter.logLint linter.clippy.unnecessarySeqFocus stx
      "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"
    last := r

end UnnecessarySeqFocus

builtin_initialize addLinter UnnecessarySeqFocus.unnecessarySeqFocusLinter

end Lean.Linter.Clippy
