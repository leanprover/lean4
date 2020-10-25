

#eval #[2, 3, 1, 0].qsort fun a b => a < b
#eval #[2, 3, 1, 0].qsort fun a b => let x := a; x < b
#eval #[2, 3, 1, 0].qsort (· < ·)
#eval #[2, 3, 1, 0].filter (· > 1)
#eval #[2, 3, 1, 0].filter (2 > ·)
