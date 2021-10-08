# Option

The `Option` type allows the representation of an optional value. For any type `α`, elements of `Option α` are either `none` or `some a` where `a` is of type `α`.
`Option` is an inductive type and defined as:
```lean
inductive Option (α : Type u) where
  | none : Option α
  | some (val : α) : Option α
```
Examples of use are:
```lean
#check @none                  -- none : {α : Type u_1} → Option α
#check some 42                -- some 42 : Option Nat
#check some ("Le"++"an", 3+1) -- some ("Le" ++ "an", 3 + 1) : Option (String × Nat)

#eval (none: Option Nat)     -- none
#eval some 42                -- some 42
#eval some ("Le"++"an", 3+1) -- some ("Lean", 4)
```
Note in the first `#eval` example `none` is annotated with a type. `none` is of type `Option` something, but in isolation Lean doesn't know what that something is.

A key use of the `Option` type is to handle partial functions in Lean's framework of total functions. A partial function is not defined for all elements of its domain. For example, division is undefined when the denominator is 0.
```lean
def divide (num den : Nat) : Option Nat :=
  if den = 0 then none else some (num/den)

#eval divide 7 2 -- some 3
#eval divide 5 0 -- none
```
Rather than return `Nat`, `divide` returns `Option Nat` and the result is `none` in the case the denominator is 0.

Another example of a partial function that can be handled by `Option` is a `head` function on lists.
```lean
def head : List α → Option α
  | []   => none
  | a::_ => some a

#check @head               -- head : {α : Type u_1} → List α → Option α
#eval head ([] : List Nat) -- none
#eval head [1,2,3]         -- some 1
```
Again the empty list has a type annotation because in isolation Lean only knows `[]` is a list of something, but not what that something is.

In some situations where an `Option α` is required, but an `α` only is provided, Lean coerces the value to `Option α`. For example, the `head` function could be defined as:
```lean
def head : List α → Option α
  | []   => none
  | a::_ => a

#check @head               -- head : {α : Type u_1} → List α → Option α
#eval head ([] : List Nat) -- none
#eval head [1,2,3]         -- some 1
```
In this case `some` has been omitted from the `::` clause. Lean recognises that `a : α` must be coerced to `Option α` to be consistent with the return type of the function.

A more complex example is a function that composes two partial functions, taking account of the `Option` return types.
```lean
# def divide (num den : Nat) : Option Nat :=
#   if den = 0 then none else some (num/den)
# def head : List α → Option α
#   | []   => none
#   | a::_ => some a
variable {α β γ : Type}

def compose (g : β → Option γ) (f : α → Option β) (a : α) : Option γ :=
  match f a with
  | none   => none
  | some b => g b

#check @compose -- compose : {α β γ : Type} → (β → Option γ) → (α → Option β) → α → Option γ

def divhead := compose (divide 100) head

#check divhead         -- divhead : List Nat → Option Nat
#eval divhead [12,2,3] -- some 8
#eval divhead []       -- none (from head)
#eval divhead [0,2,3]  -- none (from divide)
```
The definition of `compose` demonstrates pattern matching on the `Option` type.
