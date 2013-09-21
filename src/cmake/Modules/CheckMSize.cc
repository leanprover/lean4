/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <malloc.h>

#define MAX_SZ 1024

int main() {
    for (unsigned i = 1; i < MAX_SZ; i++) {
        void * p = malloc(i);
        size_t r = _msize(p);
        if (r < i || ((i > 128) && (r > 2 * i))) {
            fprintf(stderr, "Unexpected _msize behavior: i = %d, r = %d\n", i, int(r));
            return 1;
        }
        free(p);
    }
    return 0;
}
