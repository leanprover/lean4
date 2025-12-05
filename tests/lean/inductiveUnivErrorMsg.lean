inductive Bar
| foobar : Foo → Bar
| somelist : List Bar → Bar

inductive Bar2
| foobar : (x : Foo) → Bar2
| somelist : List Bar2 → Bar2

inductive Bar3
| foobar {Foo : Prop} : Foo → Bar3
| somelist : List Bar3 → Bar3

inductive Bar4
| foobar {Foo : Type} : Foo → Bar4
| somelist : List Bar4 → Bar4

inductive Bar5 : Prop where
| foobar {Foo : Prop} : Foo → Bar5
| somelist : List Bar5 → Bar5

inductive Bar6 : Type where
| foobar {Foo : Type} : Foo → Bar6
| somelist : List Bar6 → Bar6

inductive Bar7 : Type where
| foobar {Foo : Prop} : Foo → Bar7
| somelist : List Bar7 → Bar7

-- Potentially undesirable for `Foo` to get classified as a `Prop` automatically here
inductive Bar8 : Type where
| foobar : (x : Foo) → Bar8
| somelist : List Bar8 → Bar8

-- This error case could be improved:
inductive Bar9 : Type (u + 1) where
| foobar : (x : Foo) → Bar9
| somelist : List Bar9 → Bar9
