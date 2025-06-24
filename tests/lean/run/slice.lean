#eval (1..<2).toList

#eval (Std.Slice.mk #[1, 2, 3] *..<2) |>.iter.toList

#eval (Std.Slice.mk #[1, 2, 3] 1..<10) |>.size
