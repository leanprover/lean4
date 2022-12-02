/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/hash.h"

namespace lean {

//-----------------------------------------------------------------------------
// MurmurHash2, 64-bit versions, by Austin Appleby
// https://sites.google.com/site/murmurhash/
static uint64 MurmurHash64A(void const * key, size_t len, uint64 seed) {
    const uint64 m = 0xc6a4a7935bd1e995;
    const int r = 47;

    uint64 h = seed ^ (len * m);

    const uint64 * data = (const uint64 *)key;
    const uint64 * end = data + (len/8);

    while (data != end) {
        uint64 k = *data++;

        k *= m;
        k ^= k >> r;
        k *= m;

        h ^= k;
        h *= m;
    }

    const unsigned char * data2 = (const unsigned char *) data;

    switch (len & 7) {
    case 7: h ^= uint64(data2[6]) << 48;
    case 6: h ^= uint64(data2[5]) << 40;
    case 5: h ^= uint64(data2[4]) << 32;
    case 4: h ^= uint64(data2[3]) << 24;
    case 3: h ^= uint64(data2[2]) << 16;
    case 2: h ^= uint64(data2[1]) << 8;
    case 1: h ^= uint64(data2[0]);
            h *= m;
    };

    h ^= h >> r;
    h *= m;
    h ^= h >> r;

    return h;
}

uint64 hash_str(size_t len, unsigned char const * str, uint64 init_value) {
    return MurmurHash64A(str, len, init_value);
}

}
