#include <lean/lean.h>

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define CHECK(cond)                                                                 \
    do {                                                                            \
        if (!(cond)) {                                                              \
            fprintf(stderr, "FAIL:%s:%d: %s\n", __FILE__, __LINE__, #cond);         \
            return 1;                                                               \
        }                                                                           \
    } while (0)

/* Mimics a mimalloc-allocated legacy object: the payload is the allocation
 * itself (no size prefix), matching what the runtime's mi_free expects. */
static void *legacy_small_alloc(size_t payload_size) {
    void *payload = malloc(payload_size);
    if (payload == NULL) {
        return NULL;
    }

    memset(payload, 0, payload_size);
    return payload;
}

int main(void) {
    lean_object *x = (lean_object *)legacy_small_alloc(sizeof(lean_object));
    lean_object *y = (lean_object *)legacy_small_alloc(sizeof(lean_object));
    lean_object *z = (lean_object *)legacy_small_alloc(sizeof(lean_object));
    CHECK(x != NULL);
    CHECK(y != NULL);
    CHECK(z != NULL);

    x->m_rc = 1;
    x->m_cs_sz = 0;
    x->m_other = 0;
    x->m_tag = 0;

    y->m_rc = 1;
    y->m_cs_sz = 0;
    y->m_other = 0;
    y->m_tag = 0;

    z->m_rc = 1;
    z->m_cs_sz = 0;
    z->m_other = 0;
    z->m_tag = 0;

    lean_inc(x);
    lean_object *ref = lean_st_mk_ref(x);
    CHECK(ref != NULL);
    CHECK(lean_obj_tag(ref) == LeanRef);
    CHECK(((lean_ref_object *)ref)->m_value == x);

    lean_object *got = lean_st_ref_get(ref);
    CHECK(got == x);
    CHECK(((lean_ref_object *)ref)->m_value == x);
    CHECK(!lean_is_exclusive(x));
    lean_dec(got);
    CHECK(!lean_is_exclusive(x));

    lean_inc(y);
    CHECK(lean_st_ref_set(ref, y) == lean_box(0));
    CHECK(((lean_ref_object *)ref)->m_value == y);
    CHECK(lean_is_exclusive(x));

    lean_inc(z);
    lean_object *swapped = lean_st_ref_swap(ref, z);
    CHECK(swapped == y);
    CHECK(((lean_ref_object *)ref)->m_value == z);
    CHECK(!lean_is_exclusive(y));
    lean_dec(swapped);
    CHECK(lean_is_exclusive(y));

    lean_mark_mt(ref);
    CHECK(((lean_ref_object *)ref)->m_header.m_rc < 0);

    lean_object *mt_got = lean_st_ref_get(ref);
    CHECK(mt_got == z);
    lean_dec(mt_got);

    lean_object *mt_value = (lean_object *)legacy_small_alloc(sizeof(lean_object));
    CHECK(mt_value != NULL);
    mt_value->m_rc = 1;
    mt_value->m_cs_sz = 0;
    mt_value->m_other = 0;
    mt_value->m_tag = 0;
    lean_inc(mt_value);
    CHECK(lean_st_ref_set(ref, mt_value) == lean_box(0));
    CHECK(((lean_ref_object *)ref)->m_value == mt_value);
    CHECK(mt_value->m_rc < 0);
    CHECK(z->m_rc == -1);

    lean_object *result = lean_st_ref_reset(ref);
    CHECK(result == lean_box(0));
    CHECK(((lean_ref_object *)ref)->m_value == NULL);
    CHECK(mt_value->m_rc == -1);

    lean_dec(mt_value);
    lean_dec(z);
    lean_dec(y);
    lean_dec(x);
    lean_dec(ref);
    return 0;
}
