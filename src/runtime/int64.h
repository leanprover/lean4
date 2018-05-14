/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
namespace lean {
typedef long long int64;
typedef unsigned long long uint64;
static_assert(sizeof(int64 ) == 8,  "unexpected int64 size");
static_assert(sizeof(uint64 ) == 8, "unexpected uint64 size");
}
