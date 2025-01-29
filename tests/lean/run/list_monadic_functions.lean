-- This files tracks the implementation of monadic functions for lists, arrays, and vectors.
-- This is just about the definitions, not the theorems.

#check List.mapM
#check Array.mapM
#check Vector.mapM

#check List.flatMapM
#check Array.flatMapM
#check Vector.flatMapM

#check List.mapFinIdxM
#check Array.mapFinIdxM
#check Vector.mapFinIdxM

#check List.mapIdxM
#check Array.mapIdxM
#check Vector.mapIdxM

#check List.firstM
#check Array.firstM
#check Vector.firstM

#check List.forM
#check Array.forM
#check Vector.forM

#check List.filterM
#check Array.filterM

#check List.filterRevM
#check Array.filterRevM

#check List.filterMapM
#check Array.filterMapM

#check List.foldlM
#check Array.foldlM
#check Vector.foldlM

#check List.foldrM
#check Array.foldrM
#check Vector.foldrM

#check List.findM?
#check Array.findM?
#check Vector.findM?

#check List.findSomeM?
#check Array.findSomeM?
#check Vector.findSomeM?

#check List.anyM
#check Array.anyM
#check Vector.anyM

#check List.allM
#check Array.allM
#check Vector.allM

variable {m : Type v → Type w} [Monad m] {α : Type} {n : Nat}
#synth ForIn' m (List α) α inferInstance
#synth ForIn' m (Array α) α inferInstance
#synth ForIn' m (Vector α n) α inferInstance

#check List.forM
#check Array.forM
#check Vector.forM

#synth ForM m (List α) α
#synth ForM m (Array α) α
#synth ForM m (Vector α n) α

#synth Functor List
#synth Functor Array

-- These operations still have discrepancies.

-- #check List.modifyM
#check Array.modifyM
-- #check Vector.modifyM

-- #check List.forRevM
#check Array.forRevM
-- #check Vector.forRevM

-- #check List.findRevM?
#check Array.findRevM?
-- #check Vector.findRevM?

-- #check List.findSomeRevM?
#check Array.findSomeRevM?
-- #check Vector.findSomeRevM?

-- #check List.findIdxM?
#check Array.findIdxM?
-- #check Vector.findIdxM?

-- The following have not been implemented for any of the containers.

-- #check List.foldlIdxM
-- #check Array.foldlIdxM
-- #check Vector.foldlIdxM

-- #check List.foldrIdxM
-- #check Array.foldrIdxM
-- #check Vector.foldrIdxM

-- #check List.ofFnM
-- #check Array.ofFnM
-- #check Vector.ofFnM
