import Lean

open Lean Lean.Meta

inductive Nested where
  | c : List Nested → Nested

run_meta show MetaM Unit from do
  let env ← getEnv
  let consts := env.constants.map₂.foldl (init := ∅) fun consts n info =>
    consts.insert n info
  let some importEnv := env.importEnv?
    | unreachable!
  let _ ← importEnv.replay consts
