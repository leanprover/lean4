import data.int
open int
namespace foo
constant abs : int → int
notation `|` A `|` := abs A
constants a b c : int
check |a + |b| + c|
end foo
