import data.int
open int

variable abs : int → int
notation `|`:40 A:40 `|` := abs A
variables a b c : int
check |a + |b| + c|
