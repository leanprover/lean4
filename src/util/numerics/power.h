/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/

namespace lean {
/**
   \brief Template for computing <tt>a^k</tt>.
*/
template<typename T>
T power(T const & a, unsigned k) {
    unsigned mask = 1;
    T power(a);
    T b(a);
    b = 1;
    while (mask <= k) {
        if (mask & k)
            b *= power;
        power *= power;
        mask = mask << 1;
    }
    return b;
}
}
