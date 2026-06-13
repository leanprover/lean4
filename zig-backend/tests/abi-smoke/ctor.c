#include <lean/lean.h>

#include <stdint.h>
#include <stdio.h>
#include <string.h>

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);

#define CHECK(cond)                                                                 \
    do {                                                                            \
        if (!(cond)) {                                                              \
            fprintf(stderr, "FAIL:%s:%d: %s\n", __FILE__, __LINE__, #cond);         \
            return 1;                                                               \
        }                                                                           \
    } while (0)

static lean_object *make_ctor(unsigned tag, unsigned num_objs, unsigned scalar_bytes) {
    size_t total = sizeof(lean_ctor_object) + ((size_t)num_objs * sizeof(void *)) + scalar_bytes;
    lean_ctor_object *ctor = (lean_ctor_object *)lean_alloc_object(total);
    if (ctor == NULL) {
        fprintf(stderr, "FAIL:%s:%d: lean_alloc_object returned NULL\n", __FILE__, __LINE__);
        return NULL;
    }

    ctor->m_header.m_rc = 1;
    ctor->m_header.m_cs_sz = scalar_bytes;
    ctor->m_header.m_other = num_objs;
    ctor->m_header.m_tag = (uint8_t)tag;
    for (unsigned i = 0; i < num_objs; ++i) {
        ctor->m_objs[i] = lean_box(0);
    }
    return (lean_object *)ctor;
}

int main(void) {
    const unsigned num_objs = 3;
    const unsigned scalar_base = num_objs * (unsigned)sizeof(void *);
    const unsigned scalar_bytes = (unsigned)(sizeof(size_t) + sizeof(uint8_t) + sizeof(uint16_t) +
                                             sizeof(uint32_t) + sizeof(uint64_t) + sizeof(double) +
                                             sizeof(float));

    lean_initialize_runtime_module();
    lean_initialize_thread();

    lean_object *ctor = make_ctor(7, num_objs, scalar_bytes);
    CHECK(ctor != NULL);
    CHECK(lean_obj_tag(ctor) == 7);

    lean_ctor_set(ctor, 0, lean_box(11));
    lean_ctor_set(ctor, 1, lean_box(22));
    lean_ctor_set(ctor, 2, lean_box(33));

    CHECK(lean_ctor_get(ctor, 0) == lean_box(11));
    CHECK(lean_ctor_get(ctor, 1) == lean_box(22));
    CHECK(lean_ctor_get(ctor, 2) == lean_box(33));

    lean_ctor_set_usize(ctor, num_objs, 0xfeedbeefUL);
    CHECK(lean_ctor_get_usize(ctor, num_objs) == 0xfeedbeefUL);

    lean_ctor_set_uint8(ctor, scalar_base + 0, 0xab);
    lean_ctor_set_uint16(ctor, scalar_base + 2, 0xcdef);
    lean_ctor_set_uint32(ctor, scalar_base + 4, 0x89abcdefU);
    lean_ctor_set_uint64(ctor, scalar_base + 8, 0x0123456789abcdefULL);

    double fp64 = 3.141592653589793;
    float fp32 = 3.1415927f;
    lean_ctor_set_float(ctor, scalar_base + 16, fp64);
    lean_ctor_set_float32(ctor, scalar_base + 24, fp32);

    CHECK(lean_ctor_get_uint8(ctor, scalar_base + 0) == 0xab);
    CHECK(lean_ctor_get_uint16(ctor, scalar_base + 2) == 0xcdef);
    CHECK(lean_ctor_get_uint32(ctor, scalar_base + 4) == 0x89abcdefU);
    CHECK(lean_ctor_get_uint64(ctor, scalar_base + 8) == 0x0123456789abcdefULL);
    CHECK(memcmp(&fp64, &(double){lean_ctor_get_float(ctor, scalar_base + 16)}, sizeof(double)) == 0);
    CHECK(memcmp(&fp32, &(float){lean_ctor_get_float32(ctor, scalar_base + 24)}, sizeof(float)) == 0);

    lean_ctor_set_tag(ctor, 12);
    CHECK(lean_obj_tag(ctor) == 12);

    lean_dec(ctor);
    lean_finalize_thread();
    return 0;
}
