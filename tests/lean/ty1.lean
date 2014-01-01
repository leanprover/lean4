Import Int.
Variable i : Int.
Check fun x, x + i
Check fun x, x + 1
Check fun x, x
Check fun x y, y + i + 1 + x
Check (fun x, x) i
Check (fun x, x i) (fun x y, x + 1 + y)
Check (fun x, x) (fun x y, x + 1 + y)
