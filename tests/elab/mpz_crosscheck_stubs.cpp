// Allocator and panic stubs so `mpz_crosscheck.cpp` can link `src/runtime/mpz.cpp`
// without the rest of the runtime.
#include <cstdlib>
#include <cstdio>
#include <cstddef>
extern "C" {
void * mi_malloc(size_t sz) { return malloc(sz); }
void mi_free_size(void * p, size_t) { free(p); }
void lean_internal_panic_out_of_memory() { fprintf(stderr, "oom\n"); abort(); }
void lean_internal_panic_overflow() { fprintf(stderr, "overflow\n"); abort(); }
}
