# The Lean 4 standard library

Maintainer team (in alphabetical order): Henrik Böving, Markus Himmel
(community contact & external contribution coordinator), Kim Morrison, Paul
Reichert, Sofia Rodrigues.

The Lean 4 standard library is a core part of the Lean distribution, providing
essential building blocks for functional programming, verified software
development, and software verification. Unlike the standard libraries of most
other languages, many of its components are formally verified and can be used
as part of verified applications.

The standard library is a public API that contains the components listed in the
standard library outline below. Not all public APIs in the Lean distribution
are part of the standard library, and the standard library does not correspond
to a certain directory within the Lean source repository (like `Std`). For
example, the metaprogramming framework is not part of the standard library, but
basic types like `True` and `Nat` are.

The standard library is under active development. Our guiding principles are:

* Provide comprehensive, verified building blocks for real-world software.
* Build a public API of the highest quality with excellent internal consistency.
* Carefully optimize components that may be used in performance-critical software.
* Ensure smooth adoption and maintenance for users.
* Offer excellent documentation, example projects, and guides.
* Provide a reliable and extensible basis that libraries for software
  development, software verification and mathematics can build on.

The standard library is principally developed by the Lean FRO. Community
contributions are welcome. If you would like to contribute, please refer to the
call for contributions below.

### Standard library outline

1. Core types and operations
   1. Basic types
   2. Numeric types, including floating point numbers
   3. Containers
   4. Strings and formatting
2. Language constructs
   1. Ranges and iterators
   2. Comparison, ordering, hashing and related type classes
   3. Basic monad infrastructure
3. Libraries
   1. Random numbers
   2. Dates and times
4. Operating system abstractions
   1. Concurrency and parallelism primitives
   2. Asynchronous I/O
   3. FFI helpers
   4. Environment, file system, processes
   5. Locales

The material covered in the first three sections (core types and operations,
language constructs and libraries) will be verified, with the exception of
floating point numbers and the parts of the libraries that interface with the
operating system (e.g., sources of operating system randomness or time zone
database access).

### Call for contributions

Thank you for taking interest in contributing to the Lean standard library\!
There are two main ways for community members to contribute to the Lean
standard library: by contributing experience reports or by contributing code
and lemmas.

**If you are using Lean for software verification or verified software
development:** hearing about your experiences using Lean and its standard
library for software verification is extremely valuable to us. We are committed
to building a standard library suitable for real-world applications and your
input will directly influence the continued evolution of the Lean standard
library. Please reach out to the standard library maintainer team via Zulip
(either in a public thread in the \#lean4 channel or via direct message). Even
just a link to your code helps. Thanks\!

**If you have code that you believe could enhance the Lean 4 standard
library:** we encourage you to initiate a discussion in the \#lean4 channel on
Zulip. This is the most effective way to receive preliminary feedback on your
contribution. The Lean standard library has a very precise scope and it has
very high quality standards, so at the moment we are mostly interested in
contributions that expand upon existing material rather than introducing novel
concepts.

**If you would like to contribute code to the standard library but don’t know
what to work on:** we are always excited to meet motivated community members
who would like to contribute, and there is always impactful work that is
suitable for new contributors. Please reach out to Markus Himmel on Zulip to
discuss possible contributions.

As laid out in the [project-wide External Contribution
Guidelines](../../CONTRIBUTING.md),
PRs are much more likely to be merged if they are preceded by an RFC or if you
discussed your planned contribution with a member of the standard library
maintainer team. When in doubt, introducing yourself is always a good idea.

All code in the standard library is expected to strictly adhere to the
[standard library coding conventions](./style.md).
