import Lean
set_option maxHeartbeats 100000
-- attribute [simp] Array.findIdx?.loop -- Still broken
attribute [simp] Lean.expandExplicitBindersAux.loop
attribute [simp] Lean.Elab.Term.resolveLocalName.loop


-- Mathlib
-- attribute [simp] BinaryHeap.heapifyDown
-- attribute [simp] ByteSlice.forIn.loop
-- attribute [simp] Lean.Export.exportName
-- attribute [simp] Lean.Export.exportLevel
-- attribute [simp] Array.heapSort.loop
