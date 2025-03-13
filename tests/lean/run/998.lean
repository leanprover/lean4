import Lean
set_option maxHeartbeats 100000
attribute [simp] Array.findIdx?.loop
attribute [simp] Lean.expandExplicitBindersAux.loop
attribute [simp] Lean.resolveLocalName.loop


-- Mathlib
-- attribute [simp] BinaryHeap.heapifyDown
-- attribute [simp] ByteSlice.forIn.loop
-- attribute [simp] Lean.Export.exportName   -- Fixed see 998Export.lean
-- attribute [simp] Lean.Export.exportLevel  -- Fixed see 998Export.lean
-- attribute [simp] Array.heapSort.loop
