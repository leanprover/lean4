import Lean.Elab.Command

inductive T1 where | mk : T1 → T1

/-- info: 0 -/
#guard_msgs in
run_meta
  let indInfo ← Lean.getConstInfoInduct ``T1
  Lean.logInfo m!"{indInfo.numNested}"


inductive T2 where | mk : List T2 → T2

/-- info: 1 -/
#guard_msgs in
run_meta
  let indInfo ← Lean.getConstInfoInduct ``T2
  Lean.logInfo m!"{indInfo.numNested}"


inductive T3 where | mk : List T3 → List T3 → T3

/-- info: 1 -/
#guard_msgs in
run_meta
  let indInfo ← Lean.getConstInfoInduct ``T3
  Lean.logInfo m!"{indInfo.numNested}"


inductive T4 where | mk : List T4 → List (List T4) → T4

/-- info: 2 -/
#guard_msgs in
run_meta
  let indInfo ← Lean.getConstInfoInduct ``T4
  Lean.logInfo m!"{indInfo.numNested}"


mutual
inductive T5 where | mk : List T5b → List (List T5b) → T5
inductive T5b where | mk : List T5 → List (List T5) → T5b
end

/-- info: 4 -/
#guard_msgs in
run_meta
  let indInfo ← Lean.getConstInfoInduct ``T5b
  Lean.logInfo m!"{indInfo.numNested}"
