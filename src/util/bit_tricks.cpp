/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/debug.h"

namespace lean {
unsigned log2(unsigned v) {
    unsigned r = 0;
    if (v & 0xFFFF0000) {
        v >>= 16;
        r |=  16;
    }
    if (v & 0xFF00) {
        v >>= 8;
        r |=  8;
    }
    if (v & 0xF0) {
        v >>= 4;
        r |=  4;
    }
    if (v & 0xC) {
        v >>= 2;
        r |=  2;
    }
    if (v & 0x2) {
        v >>= 1;
        r |=  1;
    }
    return r;
}

// make sure no one calls the math.h log2 accidentally
double log2(int v) {
  (void)v;
  lean_unreachable();
}
}
