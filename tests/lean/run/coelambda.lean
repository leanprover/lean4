

#guard #[2, 3, 1, 0].qsort (fun a b => a < b) == #[0, 1, 2, 3]
#guard #[2, 3, 1, 0].qsort (fun a b => let x := a; x < b) == #[0, 1, 2, 3]
#guard #[2, 3, 1, 0].qsort (· < ·) == #[0, 1, 2, 3]
#guard #[2, 3, 1, 0].filter (· > 1) == #[2, 3]
#guard #[2, 3, 1, 0].filter (2 > ·) == #[1, 0]
