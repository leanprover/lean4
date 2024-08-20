open List MergeSort Internal

unseal mergeSort merge in
example : mergeSort (· ≤ ·) [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] :=
  rfl

unseal mergeSort merge in
example : mergeSort (fun x y => x/10 ≤ y/10) [3, 100 + 1, 4, 100 + 1, 5, 100 + 9, 2, 10 + 6, 5, 10 + 3, 5] = [3, 4, 5, 2, 5, 5, 16, 13, 101, 101, 109] :=
  rfl

unseal mergeSortTR.run mergeTR.go in
example : mergeSortTR (· ≤ ·) [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] :=
  rfl

unseal mergeSortTR.run mergeTR.go in
example : mergeSortTR (fun x y => x/10 ≤ y/10) [3, 100 + 1, 4, 100 + 1, 5, 100 + 9, 2, 10 + 6, 5, 10 + 3, 5] = [3, 4, 5, 2, 5, 5, 16, 13, 101, 101, 109] :=
  rfl

unseal mergeSortTR₂.run mergeTR.go in
example : mergeSortTR₂ (· ≤ ·) [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] :=
  rfl

unseal mergeSortTR₂.run mergeTR.go in
example : mergeSortTR₂ (fun x y => x/10 ≤ y/10) [3, 100 + 1, 4, 100 + 1, 5, 100 + 9, 2, 10 + 6, 5, 10 + 3, 5] = [3, 4, 5, 2, 5, 5, 16, 13, 101, 101, 109] :=
  rfl
