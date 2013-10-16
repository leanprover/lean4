/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/uint64.h"

namespace lean {
/**
   \brief Prime number iterator. It can be used to enumerate the first LEAN_PRIME_LIST_MAX_SIZE primes.
*/
class prime_iterator {
    unsigned m_idx;
public:
    prime_iterator();
    uint64 next();
};
}
