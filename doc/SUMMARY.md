# Summary

- [What is Lean](./whatIsLean.md)
- [Tour of Lean](./tour.md)
- [Setting Up Lean](./quickstart.md)
  - [Extended Setup Notes](./setup.md)
- [Theorem Proving in Lean](./tpil.md)
- [Functional Programming in Lean](fplean.md)
- [Examples](./examples.md)
  - [Palindromes](examples/palindromes.lean.md)
  - [Binary Search Trees](examples/bintree.lean.md)
  - [A Certified Type Checker](examples/tc.lean.md)
  - [The Well-Typed Interpreter](examples/interp.lean.md)
  - [Dependent de Bruijn Indices](examples/deBruijn.lean.md)
  - [Parametric Higher-Order Abstract Syntax](examples/phoas.lean.md)

# Language Manual
<!-- - [Using Lean](./using_lean.md) -->
<!-- - [Lexical Structure](./lexical_structure.md) -->
<!-- - [Expressions](./expressions.md) -->
<!-- - [Declarations](./declarations.md) -->
- [Organizational features](./organization.md)
  - [Sections](./sections.md)
  - [Namespaces](./namespaces.md)
  - [Implicit Arguments](./implicit.md)
  - [Auto Bound Implicit Arguments](./autobound.md)
<!-- - [Dependent Types](./deptypes.md) -->
<!--   - [Simple Type Theory](./simptypes.md) -->
<!--   - [Types as objects](./typeobjs.md) -->
<!--   - [Function Abstraction and Evaluation](./funabst.md) -->
<!--   - [Introducing Definitions](./introdef.md) -->
<!--   - [What makes dependent type theory dependent?](./dep.md) -->
<!-- - [Tactics](./tactics.md) -->
- [Syntax Extensions](./syntax.md)
  - [The `do` Notation](./do.md)
  - [String Interpolation](./stringinterp.md)
  - [User-Defined Notation](./notation.md)
  - [Macro Overview](./macro_overview.md)
  - [Elaborators](./elaborators.md)
  - [Examples](./syntax_examples.md)
    - [Balanced Parentheses](./syntax_example.md)
    - [Arithmetic DSL](./metaprogramming-arith.md)
- [Declaring New Types](./decltypes.md)
  - [Enumerated Types](./enum.md)
  - [Inductive Types](./inductive.md)
  - [Structures](./struct.md)
  - [Type classes](./typeclass.md)
  - [Unification Hints](./unifhint.md)
- [Builtin Types](./builtintypes.md)
  - [Natural number](./nat.md)
  - [Integer](./int.md)
  - [Fixed precision unsigned integer](./uint.md)
  - [Float](./float.md)
  - [Array](./array.md)
  - [List](./list.md)
  - [Character](./char.md)
  - [String](./string.md)
  - [Option](./option.md)
  - [Thunk](./thunk.md)
  - [Task and Thread](./task.md)
- [Functions](./functions.md)
- [Monads](./monads/intro.md)
  - [Functor](./monads/functors.lean.md)
  - [Applicative](./monads/applicatives.lean.md)
  - [Monad](./monads/monads.lean.md)
  - [Reader](./monads/readers.lean.md)
  - [State](./monads/states.lean.md)
  - [Except](./monads/except.lean.md)
  - [Transformers](./monads/transformers.lean.md)
  - [Laws](./monads/laws.lean.md)

# Other

- [Frequently Asked Questions](./faq.md)
- [Significant Changes from Lean 3](./lean3changes.md)
- [Syntax Highlighting Lean in LaTeX](./syntax_highlight_in_latex.md)
- [User Widgets](examples/widgets.lean.md)
- [Semantic Highlighting](./semantic_highlighting.md)

# Development

- [Development Guide](./dev/index.md)
- [Building Lean](./make/index.md)
  - [Ubuntu Setup](./make/ubuntu.md)
  - [macOS Setup](./make/osx-10.9.md)
  - [Windows MSYS2 Setup](./make/msys2.md)
  - [Windows with WSL](./make/wsl.md)
- [Bootstrapping](./dev/bootstrap.md)
- [Testing](./dev/testing.md)
- [Debugging](./dev/debugging.md)
- [Commit Convention](./dev/commit_convention.md)
- [Building This Manual](./dev/mdbook.md)
- [Foreign Function Interface](./dev/ffi.md)
