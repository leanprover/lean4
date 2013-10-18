/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/debug.h"

namespace lean {
template<class T>
T remainder(T a, T b) {
    lean_assert(b != 0);
    if (a > 0)
        return a % b;
    else if (b > 0)
        return a % b + b;
    else
        return a % b - b;
}
}
