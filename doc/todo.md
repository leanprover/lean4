To Do List
----------

- ~~Add `cast : Pi (A B : Type) (H : A = B) (a : A) : B`, and implement "casting propagation" in the type checker.~~
- ~~Modify the `let` construct to store the type of the value. The idea is to allow `let name : type := value in expr`. The type does not need to be provided by the user. However, the user may want to provide it as a hint for the Lean elaborator.~~
- Refactor the elaborator code. The elaborator will be one of the main data-structures in Lean. The elaborator manager should be shared between different frontends.
- ~~Reconsider whether meta-variables should be in `expr` or not. Metavariables (aka holes) are fundamental in our [design](design.md).~~
- ~~Improve Lean pretty printer for Pi's. For example, it produces `Var a : Pi (A : Type) (_ : A), A` instead of `Var a : Pi (A : Type), A -> A`.~~
- Decide what will be the main technique for customizing Lean's behavior. The elaborator manager will have many building blocks that can be put together in many different ways. Possible solutions:
   - We design our own configuration language.
   - We use an off-the-shelf embedded language such as [Lua](http://www.lua.org).
   - We use Lean itself.
- Module for reading [OpenTheory](http://www.gilith.com/research/opentheory/) proofs.
- ~~Higher-Order unification and matching~~.
- Rewriter (and Rewriter Combinators).
- [MCSat](http://leodemoura.github.io/files/fmcad2013.pdf) framework.
- Implement independent type checker using a different programming language (e.g., OCaml).
- Add `match` construct in `expr`.
- Add inductive datatype (families) in the environment. It will be a new kind of object.
- Add recursive function definition objects (low priority). It is another new kind of object.
