import data.int
open int

constant abs : int → int
notation `|`:40 A:40 `|` := abs A
constants a b c : int
check |a + |b| + c|
