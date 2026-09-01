inductive Bar
| foobar : Foo → Bar
| somelist : List Bar → Bar

inductive Bar2
| foobar : (x : Foo) → Bar2
| somelist : List Bar2 → Bar2
