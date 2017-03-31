namespace foo
constant bar : ℕ → ℕ
end foo

noncomputable def foo : ℕ → ℕ
| x := @foo.bar x -- should not use field notation with '@'
