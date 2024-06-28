A new linter flags situations where a local variable's name is one of
the argumentless constructors of its type. This can arise when a user either
doesn't open a namespace or doesn't add a dot or leading qualifier, as
in the following:

````
inductive Tree (α : Type) where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)

def depth : Tree α → Nat
  | leaf => 0
````

With this linter, the `leaf` pattern is highlighted as a local
variable whose name overlaps with the constructor `Tree.leaf`.

The linter can be disabled with `set_option linter.constructorNameAsVariable false`.

Additionally, the error message that occurs when a name in a pattern that takes arguments isn't valid now suggests similar names that would be valid. This means that the following definition:

```
def length (list : List α) : Nat :=
  match list with
  | nil => 0
  | cons x xs => length xs + 1
```

now results in the following warning:

```
warning: Local variable 'nil' resembles constructor 'List.nil' - write '.nil' (with a dot) or 'List.nil' to use the constructor.
note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
```

and error:

```
invalid pattern, constructor or constant marked with '[match_pattern]' expected

Suggestion: 'List.cons' is similar
```


#4301
