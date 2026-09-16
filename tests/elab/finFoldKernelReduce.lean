module

-- `Fin.foldl` and `Fin.foldr` reduce in the kernel.
example : Fin.foldl 8 (fun a i => a + i.val) 0 = 28 := by decide
example : Fin.foldr 8 (fun i a => a + i.val) 0 = 28 := by decide
