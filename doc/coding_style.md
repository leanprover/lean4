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

Template
--------
We organize template source code using the approach described at http://www.codeproject.com/Articles/3515/How-To-Organize-Template-Source-Code

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

We are using a modified version of [Google's C++ Style Guide][google-style]. 
We also have our version of Google's style checker [cpplint.py][cpplint].
You can run the checker over the codebase by typing:

    make style
    
If you use Ninja, you can check by ``ninja style``. It is also a part of testcases and can be run by 

    ctest -R style_check

*Disabled* Features:

 - Namespace should be terminated with "namespace"
 - At least two spaces is best between code and comments
 - Do not use ``dynamic_cast<>``.  If you need to cast within a class
   hierarchy, use ``static_cast<>`` to upcast.  Google doesn't support
   RTTI.
 - "public:" should be preceded by a blank line
 - Missing space before ``{``
 - Found C system header after C++ system header. Should be:
   environment.h, c system, c++ system, other.
 - Labels should always be indented at least one space.  If this is
   a member-initializer list in a constructor or the base class list in
   a class definition, the colon should be on the following line.
 - You don't need a ``;`` after a ``}``
 - No ``#ifndef`` header guard found
 - Streams are highly discouraged.
 - Extra space before ``(`` in function call
 - Else clause should never be on same line as else
 - Extra space before ``)``
 - Is this a non-const reference? If so, make const or use a pointer.
 - All parameters should be named in a function

Modified Features:

  - Add ``#include <list>`` for ``list<>``

    => *Check* ``std::list`` instead of ``list`` because we do have our own ``lean::list`` type.

  - Add ``#include <algorithm>`` for copy

    => *Check* ``std::copy`` instead of ``copy`` because we do have our own ``lean::copy`` method.

  - Do not use namespace using-directives. Use using-declarations instead.

    => *Allow* this if filename contains "tests/"

  - Small and focused functions are preferred: foo()
    has xxx non-comment lines (error triggered by exceeding 500 lines).

    => *Allow* this if filename contains "tests/"

  - Include the directory when naming .h files
  
    => *Allow* this if the included filename is "version.h" which is generated by cmake.

[google-style]: http://google-styleguide.googlecode.com/svn/trunk/cppguide.xml
[cpplint]: /src/cmake/Modules/cpplint.py

Git pre-push hook
-----------------

Since [git 1.8.2][git-pre-push-hook], git introduced *pre-push* hook
which is executed *before* actual push operation is performed. Using this,
we can *automatically* run the style checker over the changed files *before*
we push commits to repositories. This is useful because it prevents us
from accidentally pushing the commits which contain style problems.

[git-pre-push-hook]: https://github.com/git/git/blob/master/Documentation/RelNotes/1.8.2.txt

 - Create ``<PROJECT_ROOT>/.git/hooks/pre-push`` file with the following contents:

~~~~~~~~~~~~~~~~
#!/usr/bin/env bash
IFS=' '
DIR="$( cd "$( dirname "$0" )" && pwd )"
CHECKER=$DIR/../../src/cmake/Modules/cpplint.py
while read local_ref local_sha remote_ref remote_sha;
do
    CHANGED_FILES=`git diff --name-only $local_sha $remote_sha | grep '\(cpp\|h\)$'`
    if [ ! -z "$CHANGED_FILES" -a "$CHANGED_FILES" != " " ]; then
        echo $CHANGED_FILES | xargs $CHECKER
        RET=$?
        if [ $RET -ne 0 ]; then
            echo "There is error(s) from style-check. Please fix them before push to the repo."
            exit $RET
        fi
    fi
done
exit 0
~~~~~~~~~~~~~~~~

 - Give "exec" permission to the file

~~~~~~~~~~~~~~~~
chmod +x <PROJECT_ROOT>/.git/hooks/pre-push
~~~~~~~~~~~~~~~~

Note that you need to change ``CHECKER`` variable if you want to use other
checkers.
