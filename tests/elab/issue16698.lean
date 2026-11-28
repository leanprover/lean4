import Lean

/-!
Regression test for #16698 (and #16688): `Kernel.Environment.replay` must reject an inductive
entry whose `all` or `ctors` field names something other than a stored inductive type or
constructor, or whose `all` field does not contain the entry itself, with an error rather than a
panic, and must reject a stored `InductiveVal` that differs from the one the kernel generates.
-/

open Lean

inductive T where
  | mk

inductive Z : Prop

inductive E : Nat → Prop where
  | mk : E 0

def replayWith (extra : List ConstantInfo) : MetaM Unit := do
  let env ← getEnv
  let mut consts : Std.HashMap Name ConstantInfo :=
    env.constants.map₂.foldl (init := ∅) fun consts n info => consts.insert n info
  for ci in extra do
    consts := consts.insert ci.name ci
  let some importEnv := env.importEnv?
    | unreachable!
  discard <| importEnv.toKernelEnv.replay consts

def modifyInduct (n : Name) (f : InductiveVal → InductiveVal) : MetaM ConstantInfo := do
  let .inductInfo iv ← getConstInfo n | unreachable!
  return .inductInfo (f iv)

-- The unmodified environment replays fine.
run_meta replayWith []

/--
error: while replaying declaration 'T':
inductive type 'T' is not listed in its own `all` field
-/
#guard_msgs in
run_meta do replayWith [← modifyInduct ``T fun iv => { iv with all := [``T.mk] }]

/--
error: while replaying declaration 'T':
'T.mk', listed in the `all` field of 'T', is not a stored inductive type
-/
#guard_msgs in
run_meta do replayWith [← modifyInduct ``T fun iv => { iv with all := [``T, ``T.mk] }]

/--
error: while replaying declaration 'T':
'J', listed in the `all` field of 'T', is not a stored inductive type
-/
#guard_msgs in
run_meta do replayWith [← modifyInduct ``T fun iv => { iv with all := [``T, `J] }]

/--
error: while replaying declaration 'T':
'T.nope', listed as a constructor of 'T', is not a stored constructor
-/
#guard_msgs in
run_meta do replayWith [← modifyInduct ``T fun iv => { iv with ctors := [``T.mk, `T.nope] }]

/--
error: while replaying declaration 'T':
'Z', listed as a constructor of 'T', is not a stored constructor
-/
#guard_msgs in
run_meta do replayWith [← modifyInduct ``T fun iv => { iv with ctors := [``Z] }]

-- A forged inductive `bad : False` that lists only the honest `Z` in its `all` field (#16688).
/--
error: while replaying declaration 'bad':
inductive type 'bad' is not listed in its own `all` field
-/
#guard_msgs in
run_meta replayWith [.inductInfo {
    name := `bad, levelParams := [], type := mkConst ``False, numParams := 0, numIndices := 0
    all := [``Z], ctors := [], numNested := 0, isRec := false, isUnsafe := false
    isImpredicative := false, isK := false, hasProjections := false, hasEta := false
    hasLargeElim := false }]

-- A forged inductive that lists an ill-typed definition `D : Type := Type` in its `all` field.
/--
error: while replaying declaration 'bad':
'D', listed in the `all` field of 'bad', is not a stored inductive type
-/
#guard_msgs in
run_meta replayWith [
  .inductInfo {
    name := `bad, levelParams := [], type := mkSort 1, numParams := 0, numIndices := 0
    all := [`bad, `D], ctors := [], numNested := 0, isRec := false, isUnsafe := false
    isImpredicative := false, isK := false, hasProjections := false, hasEta := false
    hasLargeElim := false },
  .defnInfo {
    name := `D, levelParams := [], type := mkSort 1, value := mkSort 1, hints := .abbrev
    safety := .safe, all := [`D] }]

-- Stored metadata that disagrees with what the kernel generates.
/--
error: while replaying declaration 'E':
Invalid inductive type E
-/
#guard_msgs in
run_meta do replayWith [← modifyInduct ``E fun iv => { iv with numIndices := 0 }]

/--
error: while replaying declaration 'T':
Invalid inductive type T
-/
#guard_msgs in
run_meta do replayWith [← modifyInduct ``T fun iv => { iv with isRec := true }]
