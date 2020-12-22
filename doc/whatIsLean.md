# What is Lean

Lean is a functional programming language that makes it easy to
write correct and maintainable code.
You can also use Lean as an interactive theorem prover.

Lean programming primarily involves defining types and functions.
This allows your focus to remain on the problem domain and manipulating its data,
rather than the details of programming.

```lean
-- Defines a function that takes a name and produces a greeting.
def getGreeting (name : String) := s!"Hello, {name}! Isn't Lean great?"

-- The `main` function is the entry point of your program.
-- Its type is `IO Unit` because it can perform `IO` operations (side effects).
def main : IO Unit :=
  -- Define a list of names
  let names := ["Sebastian", "Leo", "Daniel"]

  -- Map each name to a greeting
  let greetings := names.map getGreeting

  -- Print the list of greetings
  for greeting in greetings do
    IO.println greeting
```

Lean has numerous features, including:

- Type inference
- First-class functions
- Powerful data types
- Pattern matching
- Type classes
- Extensible syntax
- Hygienic macros
- Dependent types
- Metaprogramming framework
- Multithreading
- Verification: you can prove properties of your functions using Lean itself
