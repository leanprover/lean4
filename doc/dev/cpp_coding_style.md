[google-style]: https://google.github.io/styleguide/cppguide.html
[cpplint]: /src/cmake/Modules/cpplint.py

# Coding Style

The Lean project is moving away from using any C++ as more and more of
the compiler is being bootstrapped in Lean itself. But the remaining
C++ codebase is using modified version of [Google's C++ Style
Guide][google-style].

## [C++11](http://en.wikipedia.org/wiki/C%2B%2B11) features

Lean makes extensive use of new features in the C++ 11 standard.
Developers must be familiar with the standard to be able to understand
the code. Here are some of the features that are extensively used.

- Type inference (aka `auto` keyword).
- Initializer lists.
- Lambda functions and expressions.
- `nullptr` constant.
- Strongly typed enumerations.
- Right angle brackets with no space is now allowed in C++ 11.
- Thread local storage.
- Threading facilities.
- Tuple types.
- Smart pointers.
- When using ``std::list`` make sure to include the `std::`
  qualifier so you do not accidentally use the ``lean::list`` type.
- When using ``std::copy`` make sure to include the `std::`
  qualifier so you do not accidentally use the ``lean::copy`` type.
- Small and focused functions are preferred: foo().  Try not to
  exceed 500 lines in a function, except in tests.
- Do **not** use the `#ifndef-#define-#endif` idiom for header files.
  Instead use `#pragma once`.
- Write `type const & v` instead of `const type & v`.
- Use `const` extensively.
- Use the macro `lean_assert` for assertions. The macro `lean_assert`
  is extensively used when writing unit tests.

## Naming

- Class, method, and function names are lower case
Use `_` for composite names. Example: `type_checker`.
- Class/struct fields should start with the prefix `m_`.

  Example:
  ```c++
  class point {
      int m_x;
      int m_y;
  public:
      ...
  };
  ```

## Namespaces

All code is in the `lean` namespace. Each frontend is stored in a
separate nested namespace. For example, the SMT 2.0 frontend is stored
in the `lean::smt` namespace.

Exception: some debugging functions are stored outside of the `lean`
namespace. These functions are called `print` and are meant to be used
when debugging Lean using `gdb`.

Do not use `using namespace` in a header file.

## Templates

Organize template source code using the approach described at http://www.codeproject.com/Articles/3515/How-To-Organize-Template-Source-Code

## Idioms

Use some popular C++ idioms:

- [Pimpl](http://c2.com/cgi/wiki?PimplIdiom)
- [RAII](http://en.wikipedia.org/wiki/Resource_Acquisition_Is_Initialization) Resource Acquisition Is Initialization

## Formatting

* Use 4 spaces for indentation.

* `if-then-else` curly brackets not always required.  The following
  forms are acceptable:

  ```c++
  if (cond) {
      ...
  } else {
      ...
  }
  ```
  and

  ```c++
  if (cond)
    statement1;
  else
    statement2;
  ```

  In *exceptional cases*, we also use

  ```c++
  if (cond) statement;
  ```

  and

  ```c++
  if (cond) statement1; else stament2;
  ```
  * `if-then-else-if-else`

  The following forms are acceptable:

  ```c++
  if (cond) {
      ...
  } else if (cond) {
      ...
  } else {
      ...
  }
  ```c++
  and

  ```c++
  if (cond)
      statement1;
  else if (cond)
      statement2;
  else
      statement3;
  ```

* Format code using extra spaces to make code more readable.  For example:

  ```c++
  environment const & m_env;
  cache               m_cache;
  normalizer          m_normalizer;
  volatile bool       m_interrupted;
  ```
  instead of:

  ```c++
  environment const & m_env;
  cache m_cache;
  normalizer m_normalizer;
  volatile bool m_interrupted;
  ```

* Spaces in expressions.  Write `a == b` instead of `a==b`. Similarly,
  we write `x < y + 1` instead of `x<y+1`.
