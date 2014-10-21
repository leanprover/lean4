import data.int
open int

constant abs : int → int
notation `|` A `|` := abs A
constants a b c : int
check |a + |b| + c|
