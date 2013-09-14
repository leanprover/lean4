Coding Style
============

[C++11](http://en.wikipedia.org/wiki/C%2B%2B11) features
--------------------------------------------------------

We make extensive use of new features in the C++ 11 standard.
Developers must be familiar with the standard to be able to understand
the code.
Here are some of the features that are extensively used.

- Type inference (aka `auto` keyword).
- Initializer lists.
- Lambda functions and expressions.
- `nullptr` constant.
- Strongly typed enumerations.
- Right angle bracket.
- Thread local storage.
- Threading facilities.
- Tuple types.

Comments
--------

The comments in the Lean codebase contain
[Doxygen](http://www.stack.nl/~dimitri/doxygen/) commands.
Doxygen is the de facto standard tool for generating documentation from
annotated C++ sources.

Namespaces
----------

All code is in the `lean` namespace. Each frontend is stored in a
separate nested namespace. For example, the SMT 2.0 frontend is stored
in the `lean::smt` namespace.

Exception: some debugging functions are stored outside of the `lean`
namespace. These functions are called `print` and are meant to be used
when debugging Lean using `gdb`.

Smart pointers
--------------

We only use `std::shared_ptr` template for class `C` only if we expect
to create only a few objects (< 1000) of class `C`. Otherwise, we
implement our own intrusive smart pointer. For example, the class
`expr` is an intrusive smart pointer to `expr_cell`. We may have
millions of `expr` objects. We say it is intrusive because the
reference counter is stored in `expr_cell`.

We use `std::unique_ptr` to make sure unique resources will be freed
correctly.

Idioms
------

We use some popular C++ idioms:

- [Pimpl](http://c2.com/cgi/wiki?PimplIdiom)
- [RAII](http://en.wikipedia.org/wiki/Resource_Acquisition_Is_Initialization) Resource Acquisition Is Initialization

Formatting
----------

* We use 4 spaces for indentation.

* Class, method, and function names are lower case
We use `_` for composite names. Example: `type_checker`.

* Class/struct fields should start with the prefix `m_`.

Example:

     class point {
         int m_x;
         int m_y;
     public:
         ...
     };

* We do **not** use the `#ifndef-#define-#endif` idiom for header files.
Instead we use `#pragma once`.

* We write `type const & v` instead of `const type & v`.

* We use `const` extensively.

* `if-then-else`

The following forms are acceptable:

     if (cond) {
         ...
     } else {
         ...
     }

and

     if (cond)
        statement1;
     else
        statement2;

In *exceptional cases*, we also use

     if (cond) statement;

and

     if (cond) statement1; else stament2;

* `if-then-else-if-else`

The following forms are acceptable:

     if (cond) {
         ...
     } else if (cond) {
         ...
     } else {
         ...
     }

and

     if (cond)
         statement1;
     else if (cond)
         statement2;
     else
         statement3;

* We frequently format code using extra spaces

For example, we write

    environment const & m_env;
    cache               m_cache;
    normalizer          m_normalizer;
    volatile bool       m_interrupted;

instead of

    environment const & m_env;
    cache m_cache;
    normalizer m_normalizer;
    volatile bool m_interrupted;

* We use the macro `lean_assert` for assertions.
The macro `lean_assert` is extensively used when writing unit tests.

* Spaces in expressions
We write `a == b` instead of `a==b`.
Similarly, we write `x < y + 1` instead of `x<y+1`.

Google's C++ Style Guide
------------------------

We are using a modified version of
[Google's C++ Style Guide][google-style]. Here is a list of checks
that we *disabled*:

 - Namespace should be terminated with "namespace"  [readability/namespace]
 - At least two spaces is best between code and comments
 - Do not use ``dynamic_cast<>``.  If you need to cast within a class
   hierarchy, use ``static_cast<>`` to upcast.  Google doesn't support
   RTTI.
 - "public:" should be preceded by a blank line  [whitespace/blank_line]
 - Missing space before ``{``  [whitespace/braces]
 - Found C system header after C++ system header. Should be:
   environment.h, c system, c++ system, other.  [build/include_order]
   [4]
 - Labels should always be indented at least one space.  If this is
   a member-initializer list in a constructor or the base class list in
   a class definition, the colon should be on the following line.
   [whitespace/labels]
 - You don't need a ``;`` after a ``}``  [readability/braces]
 - No ``#ifndef`` header guard found
 - Streams are highly discouraged.
 - Extra space before ``(`` in function call  [whitespace/parens]
 - Else clause should never be on same line as else [whitespace/newline]
 - Extra space before ``)``  [whitespace/parens]
 - Is this a non-const reference? If so, make const or use a pointer. [runtime/references]

[google-style]: http://google-styleguide.googlecode.com/svn/trunk/cppguide.xml
