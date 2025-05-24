import Lean.Meta.Basic
import Lean.Util.ErrorExplanation
-- TODO: delete
import Lean.Elab.Import

namespace Lean

open Meta

inductive CodeBlockIndex where
  | broken
  | fixed (idx : Nat)
  deriving Repr

structure CodeBlockId where
  explanationName : Name
  setIndex : Nat
  blockIndex : CodeBlockIndex
  deriving Repr

structure IdentifiedExample where
  id : CodeBlockId
  code : String
  outputs: Array String
  deriving Repr

def ErrorExplanation.CodeBlockSet.toIdentifiedExamples (explanationName : Name) (setIndex : Nat) : ErrorExplanation.CodeBlockSet → Array IdentifiedExample
  | { broken, brokenOutputs, fixedWithOutputs } =>
    let brokenEx := { id := { explanationName, setIndex, blockIndex := .broken }
                      code := broken
                      outputs := brokenOutputs }
    let fixedExs := fixedWithOutputs.mapIdx fun i (code, outputs) => {
        id := { explanationName, setIndex, blockIndex := .fixed i }
        code
        outputs
      }
    fixedExs.push brokenEx

deriving instance BEq for Import
deriving instance Hashable for Import

def makeCommonImportSets : MetaM (Std.HashMap (Array Import) (Array IdentifiedExample)) := do
  let mut importSets := {}
  for (explanationName, explanation) in getErrorExplanationsRaw (← getEnv) do
    for h : i in [:explanation.codeBlocks.size] do
      let examples := explanation.codeBlocks[i].toIdentifiedExamples explanationName i
      for ex in examples do
        let inputCtx := Parser.mkInputContext ex.code "<input>"
        let (header, ps, msgs) ← Parser.parseHeader inputCtx
        let imports := Elab.HeaderSyntax.imports header
        importSets := importSets.alter imports (fun val? => val?.getD #[] |>.push ex)
  return importSets
      -- try
      -- catch e =>
      --   throwError m!"Explanation `{explanationName}` contains an invalid code sample:\n{e.toMessageData}"

-- TODO: caching -- only reprocess an explanation if it's changed (this is just a Verso thing, though...)
def processExplanations : MetaM Unit := do
  let importSets ← makeCommonImportSets

  -- TODO: for each import set, call out to a process that does highlighting/message stuff/etc. for
  -- all snippets with common imports
  sorry




-- deriving instance Repr for MessageSeverity
-- deriving instance Repr for ErrorExplanation.Metadata
-- deriving instance Repr for ErrorExplanation

-- run_meta do
--   logInfo m!"{repr <| ← getErrorExplanationsSorted}"
--   let sets ← makeCommonImportSets
--   logInfo m!"{repr sets.toArray}"

def main : IO UInt32 := do
  sorry
