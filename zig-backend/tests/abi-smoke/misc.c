#include <lean/lean.h>

#include <stdint.h>
#include <stdio.h>

#define CHECK(cond)                                                                 \
    do {                                                                            \
        if (!(cond)) {                                                              \
            fprintf(stderr, "FAIL:%s:%d: %s\n", __FILE__, __LINE__, #cond);         \
            return 1;                                                               \
        }                                                                           \
    } while (0)

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);

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

static lean_object *mk_name_num(lean_object *prefix, unsigned value, uint64_t hash) {
    lean_object *name = make_ctor(0, 2, sizeof(uint64_t));
    if (name == NULL) return NULL;
    lean_ctor_set(name, 0, prefix);
    lean_ctor_set(name, 1, lean_box(value));
    lean_ctor_set_uint64(name, (unsigned)(sizeof(lean_object *) * 2), hash);
    return name;
}

static lean_object *mk_name_str(lean_object *prefix, const char *suffix, uint64_t hash) {
    lean_object *name = make_ctor(1, 2, sizeof(uint64_t));
    if (name == NULL) return NULL;
    lean_ctor_set(name, 0, prefix);
    lean_ctor_set(name, 1, lean_mk_string(suffix));
    lean_ctor_set_uint64(name, (unsigned)(sizeof(lean_object *) * 2), hash);
    return name;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_initialize_thread();

    {
        lean_object *lhs = mk_name_str(mk_name_num(lean_box(0), 7, UINT64_C(0xaaaa)), "leaf", UINT64_C(0xbbbb));
        lean_object *rhs = mk_name_str(mk_name_num(lean_box(0), 7, UINT64_C(0xaaaa)), "leaf", UINT64_C(0xbbbb));
        lean_object *diff = mk_name_str(mk_name_num(lean_box(0), 8, UINT64_C(0xaaaa)), "leaf", UINT64_C(0xbbbb));

        CHECK(lean_name_eq(lhs, rhs) == 1);
        CHECK(lean_name_eq(lhs, diff) == 0);

        lean_dec(lhs);
        lean_dec(rhs);
        lean_dec(diff);
    }

    lean_finalize_thread();
    return 0;
}
