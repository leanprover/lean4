inductive Foo : Type
| u  : Foo
| mk : Bool → Foo

instance : HasRepr Foo := ⟨λ foo =>
match foo with
| Foo.u => "u"
| Foo.mk b => "mk"⟩

#eval #[false, true].map Foo.mk -- 10:0: error: incomplete case

/-
Additional information:

tag: 981544044
>> Foo.u
>> Foo.mk
function: _main
function: _main._closed_6
function: _main._closed_5
function: List.repr._at._main._spec_2
function: List.reprAux._main._at._main._spec_3
function: List.reprAux._main._at._main._spec_3
-/
