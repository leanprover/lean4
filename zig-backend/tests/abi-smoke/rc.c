#include <lean/lean.h>

#include <malloc/malloc.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);

static size_t g_malloc_count = 0;
static size_t g_free_count = 0;
static bool g_track_allocations = false;

void *malloc(size_t size) {
    void *ptr = malloc_zone_malloc(malloc_default_zone(), size);
    if (g_track_allocations && ptr != NULL) {
        g_malloc_count += 1;
    }
    return ptr;
}

void free(void *ptr) {
    if (g_track_allocations && ptr != NULL) {
        g_free_count += 1;
    }
    malloc_zone_free(malloc_default_zone(), ptr);
}

#define CHECK(cond)                                                                 \
    do {                                                                            \
        if (!(cond)) {                                                              \
            fprintf(stderr, "FAIL:%s:%d: %s\n", __FILE__, __LINE__, #cond);         \
            return 1;                                                               \
        }                                                                           \
    } while (0)

static int check_rc_field(lean_object *obj, int expected) {
    if (obj->m_rc != expected) {
        fprintf(stderr, "FAIL:%s:%d: rc=%d expected=%d\n", __FILE__, __LINE__, obj->m_rc, expected);
        return 1;
    }
    return 0;
}

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
    lean_initialize_runtime_module();
    lean_initialize_thread();

    g_malloc_count = 0;
    g_free_count = 0;
    g_track_allocations = true;
    lean_object *tracked = make_ctor(0, 0, 5000);
    g_track_allocations = false;

    CHECK(tracked != NULL);
    CHECK(g_malloc_count == 1);
    CHECK(check_rc_field(tracked, 1) == 0);
    CHECK(lean_is_exclusive(tracked));
    CHECK(!lean_is_shared(tracked));

    lean_inc(tracked);
    CHECK(check_rc_field(tracked, 2) == 0);
    CHECK(!lean_is_exclusive(tracked));
    CHECK(lean_is_shared(tracked));

    lean_dec(tracked);
    CHECK(check_rc_field(tracked, 1) == 0);
    CHECK(lean_is_exclusive(tracked));
    CHECK(!lean_is_shared(tracked));

    g_track_allocations = true;
    lean_dec(tracked);
    g_track_allocations = false;
    CHECK(g_free_count == 1);
    CHECK(g_malloc_count == g_free_count);

    lean_object *persistent = make_ctor(0, 0, 5000);
    CHECK(persistent != NULL);
    CHECK(check_rc_field(persistent, 1) == 0);

    lean_mark_persistent(persistent);
    CHECK(check_rc_field(persistent, 0) == 0);

    lean_inc(persistent);
    lean_dec(persistent);
    CHECK(check_rc_field(persistent, 0) == 0);
    CHECK(!lean_is_shared(persistent));

    lean_free_object(persistent);
    lean_finalize_thread();
    return 0;
}
