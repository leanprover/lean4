# Tour of Lean

The best way to learn about Lean is to read and write Lean code.
This article will act as a tour through some of the key features of the Lean
language and give you some code snippets that you can execute on your machine.
To learn about setting up a development environment, check out [Getting Started](./gettingStarted.md).

There are two primary concepts in Lean: functions and types.
This tour will emphasize features of the language which fall into
these two concepts.

# Functions and Namespaces

The most fundamental pieces of any Lean program are functions organized into namespaces.
[Functions](./functions.md) perform work on inputs to produce outputs,
and they are organized under [namespaces](./namespaces.md),
which are the primary way you group things in Lean.
They are defined using the [`def`](./definitions.md) command,
which give the function a name and define its arguments.

```lean
namespace BasicFunctions

-- The `#eval` command is used to evaluate expressions
#eval 2+2

-- You use 'def' to define a function. This one accepts a natural number and returns a natural number.
-- Parentheses are optional for function arguments, except for when you use an explicit type annotation.
-- Lean can often infer the type of the functions arguments
def sampleFunction1 x := x*x + 3

-- Apply the function, naming the function return result using 'def'.
-- The variable type is inferred from the function return type.
def result1 := sampleFunction1 4573

-- This line uses an interpolated string to print the result. Expressions inside
-- braces `{}` are converted into string using the polymorphic method `toString`
#eval println! "The result of squaring the integer 4573 and adding 3 is {result1}"

-- When needed, annotate the type of a parameter name using '(argument:type)'.  Parentheses are required.
def sampleFunction2 (x : Nat) := 2*x*x - x + 3

def result2 := sampleFunction2 (7 + 4)

#eval println! "The result of applying the 2nd sample function to (7 + 4) is {result2}"

-- Conditionals use if/then/else
def sampleFunction3 (x : Int) :=
  if x > 100 then
    2*x*x - x + 3
  else
    2*x*x + x - 37

#eval println! "The result of applying the 3rd sample function to 2 is {sampleFunction3 2}"

end BasicFunctions
```
