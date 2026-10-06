/* Time deletion separately from allocation; compare identical binaries linked to each runtime. */
#include <lean/lean.h>
#include <stdio.h>

void lean_initialize_runtime_module(void);
lean_object * lean_io_mono_nanos_now(void);

static uint64_t now(void) { return lean_uint64_of_nat_mk(lean_io_mono_nanos_now()); }
static lean_object * leaf(void) { return lean_alloc_ctor(0, 0, 0); }

static lean_object * graph(unsigned shape, unsigned n) {
    if (shape == 0) {
        lean_object * o = leaf();
        for (unsigned i = 1; i < n; ++i) {
            lean_object * p = lean_alloc_ctor(0, 1, 0);
            lean_ctor_set(p, 0, o);
            o = p;
        }
        return o;
    }
    lean_object * a = lean_alloc_array(n, n);
    for (unsigned i = 0; i < n; ++i) {
        lean_object * o = shape == 1 ? leaf() : lean_box(i);
        if (shape == 3) {
            o = leaf();
            lean_internal_set_rc(o, -1);
        }
        lean_array_cptr(a)[i] = o;
    }
    return a;
}

int main(void) {
    lean_initialize_runtime_module();
    char const * names[] = {"ctor-chain", "array-leaves", "array-scalars", "array-shared"};
    unsigned n = 250000, repeats = 25;
    for (unsigned shape = 0; shape < 4; ++shape) {
        uint64_t elapsed = 0;
        for (unsigned r = 0; r < repeats + 3; ++r) {
            lean_object * o = graph(shape, n);
            uint64_t start = now();
            lean_dec(o);
            uint64_t stop = now();
            if (r >= 3) elapsed += stop - start;
        }
        printf("%s %.3f ns/element\n", names[shape], (double)elapsed / (n * repeats));
    }
    return 0;
}
