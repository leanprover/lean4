inductive Syntax
| atom : String → Syntax
| node : String → Array Syntax → Syntax

instance coe1 : HasCoe String Syntax := ⟨Syntax.atom⟩
instance coe2 {α} : HasCoe (List α) (Array α) := ⟨List.toArray⟩

def ex10 (s : Syntax) : Syntax :=
Syntax.node "foo" (List.toArray ["boo", s]) -- Works

def ex11 (s : Syntax) :=
[s, "foo"] -- Works

def ex12 (s : Syntax) :=
/-
We don't know the expected type. Before elaborating the `List.cons` applications we know
that the resulting type is `List ?A`. Then, we elaborate `"foo"`, and set `?A := String`.
Then, we fail when we try to elaborate `s` since there is not coercion from `Syntax` to `String`.
Potential solution: add special support for polymorphic nested applications such as `List.cons`, `Add.add`, etc.
Disclaimer: not sure whether we will create even more problems since all nested arguments would have to
be elaborated without an expected type. Perhaps, combined with the "suspension" mechanism it will work great.
-/
["foo", s]
