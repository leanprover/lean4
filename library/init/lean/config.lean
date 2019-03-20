/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.core

namespace lean
/--
For functions `f` with more than `closureMaxArgs`, we need to generate a curried version
```
obj* fCurried(obj** args) {
  return f(args[0], args[1], ..., args[n-1]);
}
```
The curried version is used when a closure for `f` is created.

Remark: whenever the value of this constant is modified, we have to regenerate
`src/util/apply.cpp` and `src/util/apply.h` using the meta program `gen/apply.lean`.
-/
def closureMaxArgs := 16
end lean
