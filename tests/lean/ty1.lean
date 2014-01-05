import Int.
variable i : Int.
check fun x, x + i
check fun x, x + 1
check fun x, x
check fun x y, y + i + 1 + x
check (fun x, x) i
check (fun x, x i) (fun x y, x + 1 + y)
check (fun x, x) (fun x y, x + 1 + y)
