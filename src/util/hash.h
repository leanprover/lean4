/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {

unsigned hash(char const * str, unsigned length, unsigned init_value);

inline unsigned hash(unsigned h1, unsigned h2) {
    h2 -= h1; h2 ^= (h1 << 8);
    h1 -= h2; h2 ^= (h1 << 16);
    h2 -= h1; h2 ^= (h1 << 10);
    return h2;
}

}
