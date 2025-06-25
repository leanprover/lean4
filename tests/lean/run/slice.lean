import Std.Data.Iterators

#eval #[1, 2, 3][*...*].iter.toList

#eval #[1, 2, 3][1...*].iter.toList

#eval #[1, 2, 3][*...<2].iter.toList

#eval #[1, 2, 3][1...<10].size

#eval #[1, 2, 3][1...*].take 2 |>.toList
