example : (`foo.bla).eraseSuffix? `bla == some `foo := rfl
example : (`foo.bla).eraseSuffix? `boo == none := rfl
example : (`foo.bla).eraseSuffix? `foo.bla == some .anonymous := rfl
example : (`foo.bla.boo).eraseSuffix? `bla == none := rfl
example : (`foo.bla.boo).eraseSuffix? `boo == `foo.bla := rfl
example : (`foo.bla.boo).eraseSuffix? `bla.boo == `foo := rfl
