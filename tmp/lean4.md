Design notes for Lean4
----------------------

* Goals

- Move more code from C++ to Lean.
- New compiler and C++ code generator.
- New runtime (support for unboxed values and FFI).
- New parser and macro expander (in Lean).
- New monad for accessing primitives that are only available in C++ (e.g., `type_context`).
- Fix critical issues (e.g., issue #1601).
- Fix language design issues.
- Reduce clutter in the core lib and code base.

* Plan

- Create Lean4 branch
- Disable most tests (they will be incrementally added back as we make progress on Lean4).
- Dramatically reduce the size of core lib. We should only keep the basics that
are needed to execute Lean programs. Remove most theorems and lemmas,
algebraic hierarchy, all non basic tactics, etc. Motivations: reduce clutter,
and increase agility. We will copy `library` into `old_library` and incrementally
rebuild core lib.
- Remove dead C++ code, and disable all but the most basic tactics.
- Add abstraction layers to isolate modules. Example: module manager should not depend on the parser;
  equation compiler should not depend on the elaborator.
- Make Lean object thread safe (see Memory management section for performance issues),
and remove related clutter. Example: we will not need ts_vm_obj anymore.
Remove unnecessary closure objects that were added for the previous C++ code generator
that was discontinued.
- Split tactic state into backtrackable and non-backtrackable parts using the
new monad transformers. The plan is to have the following monads for meta programming:
  a) `meta_core`: it has non-backtrackable state, stores the name generator and
      cache data structures. It allows users to invoke `io` actions.
  b) `elab`: it has a non-backtrackable state, and is defined on top of `meta_core`.
      It provides access to the environment, and metavariable context.
      It also allows us to create `type_context` objects. There is no goal management.
  c) `tactic`: it has a backtrackable state, and has goal management support.
      It is also defined on top of `meta_core`, and it can execute `elab` actions.
  Both `meta_core` and `elab` use their state linearly. We will implement the (most of the) C++ primitive tactics
  in the `elab` monad.
- Implement support objects in Lean: options, format, structure trace messages, syntax object, etc.
- Add parser infrastructure in Lean.
- Compiler and C++ code generator. The C++ code generator will avoid many bootstrapping
problems we have. The idea is to write several Lean modules in Lean, emit C++ code, save
the generated C++ code in our repo.
- New IR with support for non uniform memory layout for Lean objects (see details on the #backend
Slack channel).
- Develop a tool in Lean that given a Lean inductive datatype (or structure) generates C++
code for retrieving fields and creating Lean objects. The goal is to isolate primitives implemented
in C++ from the way we represent Lean objects in memory. For example, most Lean functions implemented
in C++ use the C++ function `cfield` which assumes objects have a uniform memory layout.
- Develop a tool for generating glue code for interfacing Lean and C++ code. Again, the goal
is to isolate the primitives from the way we handle boxed/unboxed values.
For example, suppose we have a builtin function `foo` that takes two Lean `bool` values.
Right now, this function takes boxed values `c_foo(vm_obj const & a, vm_obj const & b)`.
It feels weird to have to box a Lean value to be able to invoke the builtin implementation for `foo`.
After we have the tool, we would write `c_foo(bool a, bool b)` and describe its signature in a Lean file.
The tool then generates the wrappers for invoking `c_foo` from the interpreter and generated C++ code.

* Language and library issues

- `private` declarations are not reliable. Users can easily subvert them
using meta programming. This is problematic for several optimizations
we want to use. For example, suppose we define a state-like monad
where every primitive uses the state linearly. The code
generator cannot rely on that since users can currently access
the internal implementation, and use the state in a non linear way.
This is just an example. We have many more.

- `parameter`s are currently simulated in Lean. For example,
when we declare `foo` in a section with a parameter `A`,
`foo` is automatically abstracted and an alias `foo => @foo A` is created.
This creates many problems, most of them are documented in the issue tracker.
This approach has one advantage: users can use the abstracted (`_root_.foo`)
and non-abstracted (`foo`) version simultaneously. Another advantage is that
we don't have to type check `foo` more than once in the kernel.
That being said, the disadvantages far outweigh the advantages.
We plan to go back to the approach used in Lean1 and Coq.

- Coercion resolution (see issue #1402).

- Name resolution for `[ ... ] tactic blocks.
The `[ ... ] notation allows us to use interactive tactic notation
when writing reusable tactics. This is very convenient, but the current
implementation uses dynamic name resolution, and is a source of many
bugs.

- `if-then-else` using `bool` instead of `Prop`.
As soon as we started programming with Lean (version 3), it became clear
that `if-then-else` with `Prop` creates more problems that it solves.
The elaborator already has support for a coercion from `Prop` to `bool`
(for decidable propositions). The dependent `if H : p then t else e`
may look cute, but it is unnecessary now that we have `match`.

- `decidable` type class. A recurrent problem in Lean occurs when
users perform dependent elimination on `decidable` instances.
The problem occurs when we have `[h : decidable p]` in the context
and a goal `G[@f p h]`, that is, a goal containing the term `@f p h`.
Then, we perform `cases h`, and obtain `G[@f p (dedicable.is_true h')]` in
one branch and `G[@f p (decidable.is_false h)]` in another. Then, we apply a
lemma that gives us `G[@f p h]` where `h` is the synthesized instance,
but we cannot use it to close the goal because we get a type error.
We have discussed this problem with Tahina and he pointed out that
we should never perform dependent elimination on type class instances in proofs,
and that this is an anti-idiom. He told us that every type class is a
structure in Coq. That is, everything is wrapped in a structure.
In Coq, they would use a custom eliminator for performing case analysis
on decidable instances. They don't face this problem because the custom eliminator
is more convenient to use them manually destructing the wrapper structure,
and then the actual data. He also strongly suggested that we
should decouple the program that computes whether a proposition is true or false
from the proof the result is correct. The Lean type class combines both in one single definition.
He said this will be a problem in the future for users that want to compute in the kernel.
 The kernel computations will have to deal with these proof terms. In Coq, `decidable` is now defined as:
```
Class Decidable (P : Prop) := {
  Decidable_witness : bool;
  Decidable_spec : Decidable_witness = true <-> P
}.
```
He strongly recommended we define `decidable` using this approach.
He said this is not the original definition used in Coq. The first one was a structure wrapping a
sum type (which is closer to our definition), and the Coq developers had to change it
because of performance problems in proofs by reflection.

- Interactive tactics. In Lean4 we will have a much more extensible and flexible
parser, and it will be written in Lean. We will be able to write a custom parser for the tactic
interactive mode. So, the current argument-type driven parser we use will not
be needed anymore.

- Quotations. Do we need all of them? I find the one with three backticks very inconvenient to use.
Moreover, as soon as we implement the new parser, we will want quotations for building
the new syntactic object and Lean expressions.

* Compiler

- The first compilation step applies compiler specific simplification rules provided by users.
For example, we will be able to mark `map g (map f l) = map (g o f) l` as an optimization
rule for the compiler.

- The new compiler will use a System-F like intermediate representation.
It will be similar to Haskell core language. Inductive datatypes will be represented
using a constant for each constructor and a `cases` eliminator. If `cases` is encoded
using a expr-macro, we can easily support `default/other` case.

- Basic types (scalars, bool, char, uint32, uint64, int64, int32, ...) and C++ types
can be stored in unboxed form. The unboxed version are prefixed with `#` as they do
in Haskell.

- When we convert a Lean function to System-F, we will generate two versions: boxed and unboxed.
The boxed version is needed when passing this function to polymorphic higher-order functions.
As in Haskell, polymorphic functions always take boxed values.
Both versions are stored in the Lean environment as `meta` functions.
Example: the function `def inc (a : int32) := a + 1` is converted into two versions
`meta def _SystemF.boxed.inc (a : int32) := a + 1`, and `meta def _SystemF.unboxed.inc (a : #int32) := a #+ #1`.
Now, suppose we want to compile `twice inc a` where `def twice {A : Type} (f : A -> A) (a : A) := f (f a)`.
Then, since `twice` is polymorphic, we need to pass `inc` boxed version, and we generate
`@_SystemF.boxed.twice int32 _SystemF.boxed.inc a`.

- We want to implement monomorphisation as an additional optimization step. The idea is specialize functions like `twice`.
In the previous example, monomorphisation would generate `@_SystemF.unboxed.twice_int32 (f : #int32 -> #int32) (a : #int32)`.
We are considering caching monomorphised functions into the .olean files. If we do this, we have to consider the situation
where more than one .olean contains the same monomorphised function. We see two options: we have a canonical way to generate
names for monomorphised functions; we generate unique names, and accept the fact the environment will contain duplicates.
It is just a space issue.

- Code inlining will occur at the System-F level after we have applied
simplifications.  This is relevant for the performance issues we have
observed when a long chain of functions need to be unfolded (e.g., new
monad transformer library).

* IR

- Register based.
- Explicit reference counting instructions. We use reference counting for: composite objects, closures and
  C++ unboxed data (e.g., `expr`). Remark: for each C++ primitive the VM needs to know how to increase/decrease the reference counter.
- Support for unboxed values.
- Instructions for accessing unboxed values in non-uniform structures.
  We will have instructions for operations such as `get_scalar_<sz>(obj, offset)`,
  where `obj` is a (potentially non-uniform) Lean object, `offset` is the offset
  inside of this object, and `sz` is the number of bytes needed to store the object.
  In practice, we would have `get_scalar_1`, `get_scalar_2`, `get_scalar_4` and `get_scalar_8`.
  These scalars are unboxed. We would have registers for storing the different kinds of scalars,
  and basic operations on them (e.g., comparison, arithmetic, etc). So, we will
  have instructions such as `GETS_<sz> r_o r_i offset` where `r_o` and `r_i` are registers, and
  it corresponds to `r_o := get_scalar_<sz>(r_i, offset)`. Moreover, `r_o` must be a scalar
  register of size `sz` and `r_i` is a register for storing Lean objects.

Remark: for each constructor datatype, we will have a table that maps fields to the
operation needed to retrieve them. We will use this table when converting the SystemF
representation into the IR.

Open issue: should we use SSA or SIL?

* VM

- We need a new VM for the new IR.

- The VM should be able to invoke primitives hand written in C++ and
C++ code emitted by the Lean compiler.

- A few hand written C++ primitives and C++ code emitted by the Lean compiler
need to invoke Lean functions. We should be careful to avoid a mismatch here where
a C++ function F for Lean version `X` is trying to invoke bytecode for
a Lean function G for version `X+1`. If we allow this to happen the system
may crash because the data representation for version `X+1` may be
different from version `X`.

We can try to address this issue by breaking core lib into two parts.
The first part (bootstrapping) contains all the infrastructure needed by the parser, compiler,
tactic framework, and Lean runtime. If we make a change here, we should
compile it again using the previously emitted C++ code, and then generate
a new version of the C++ code, compile it, and check whether it works or not.
In principle, it is not safe to invoke bytecode generated during the current compilation
from previously emitted C++ code since they may be using different representations.
Of course, the changes may be harmless, but to avoid problems we should minimize
the number of tactics used in this part of the core lib. Ideally, tactics should
not be used in the bootstrapping part.

We may also emit C++ code for non essential functionality that is implemented in Lean,
and then link it with the Lean executable. Example: a decision procedure, a parser extension.
The idea is to provide a more efficient version to users. Here we can use a more
relaxed approach since this functionality is not part of the compiler. We can store a hash code
for each of these functions. When we import the .olean file that generated the function
we compare whether the hash code there matches the one in the emitted C++ code.
If it does, we use the C++ version, otherwise we use the bytecode.

* Memory management

Lean3 VM objects are not thread safe: they do not use atomic
operations for updating the reference counter, and we use a small
object memory allocator. The main motivation was performance.
We evaluated these design decisions again, and did not observe any
performance impact when we used atomic operations for updating
the reference counter and removed the small object allocator.
The experiments were conducted using OSX and Linux.
We considered two benchmarks: core lib compilation, and a small Lean
program attached in the end of this section.
In both platforms and benchmarks no significant difference was observed.
Then, we disable the `memory_pool` object, and again no difference
in performance was observed.
We believe the memory allocators in the C++ runtime have been improved.
This is consistent with our observation that building Lean with `tcmalloc`
does not improve the performance significantly anymore.
However, it is not clear why using std::atomic does not impact performance
anymore.

```
def foo (n : nat) : nat :=
(((list.iota n).map (+10)).map (+30)).length

#eval nat.repeat (λ i _, foo i) 4000 0
```
