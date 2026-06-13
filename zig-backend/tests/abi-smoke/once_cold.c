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

static unsigned g_obj_count = 0;
static unsigned g_heap_obj_count = 0;
static unsigned g_uint8_count = 0;
static unsigned g_uint16_count = 0;
static unsigned g_uint32_count = 0;
static unsigned g_uint64_count = 0;
static unsigned g_usize_count = 0;

static lean_object *init_obj(void) {
    g_obj_count += 1;
    return lean_box(1);
}

static lean_object *init_heap_obj(void) {
    g_heap_obj_count += 1;
    lean_object *obj = lean_alloc_object(sizeof(lean_object));
    if (obj == NULL) {
        return NULL;
    }
    obj->m_rc = 1;
    obj->m_cs_sz = 0;
    obj->m_other = 0;
    obj->m_tag = 0;
    return obj;
}

static uint8_t init_uint8(void) {
    g_uint8_count += 1;
    return UINT8_C(0x8f);
}

static uint16_t init_uint16(void) {
    g_uint16_count += 1;
    return UINT16_C(0x8fed);
}

static uint32_t init_uint32(void) {
    g_uint32_count += 1;
    return UINT32_C(0x8fedc0de);
}

static uint64_t init_uint64(void) {
    g_uint64_count += 1;
    return UINT64_C(0x8fedc0dedeadbeef);
}

static size_t init_usize(void) {
    g_usize_count += 1;
    return (size_t)0x12345678;
}

int main(void) {
    {
        lean_once_cell_t tok = LEAN_ONCE_CELL_INITIALIZER;
        lean_object *loc = NULL;
        lean_object *first = lean_obj_once_cold(&loc, &tok, init_obj);
        lean_object *second = lean_obj_once_cold(&loc, &tok, init_obj);

        CHECK(first == lean_box(1));
        CHECK(second == first);
        CHECK(loc == first);
        CHECK(g_obj_count == 1);
    }

    {
        lean_once_cell_t tok = LEAN_ONCE_CELL_INITIALIZER;
        lean_object *loc = NULL;
        lean_object *first = lean_obj_once_cold(&loc, &tok, init_heap_obj);
        lean_object *second = lean_obj_once_cold(&loc, &tok, init_heap_obj);

        CHECK(first != NULL);
        CHECK(!lean_is_scalar(first));
        CHECK(second == first);
        CHECK(loc == first);
        CHECK(first->m_rc == 0);
        CHECK(g_heap_obj_count == 1);

        first->m_rc = 1;
        lean_dec_ref(first);
    }

    {
        lean_once_cell_t tok = LEAN_ONCE_CELL_INITIALIZER;
        uint8_t loc = 0;
        CHECK(lean_uint8_once_cold(&loc, &tok, init_uint8) == UINT8_C(0x8f));
        CHECK(lean_uint8_once_cold(&loc, &tok, init_uint8) == UINT8_C(0x8f));
        CHECK(loc == UINT8_C(0x8f));
        CHECK(g_uint8_count == 1);
    }

    {
        lean_once_cell_t tok = LEAN_ONCE_CELL_INITIALIZER;
        uint16_t loc = 0;
        CHECK(lean_uint16_once_cold(&loc, &tok, init_uint16) == UINT16_C(0x8fed));
        CHECK(lean_uint16_once_cold(&loc, &tok, init_uint16) == UINT16_C(0x8fed));
        CHECK(loc == UINT16_C(0x8fed));
        CHECK(g_uint16_count == 1);
    }

    {
        lean_once_cell_t tok = LEAN_ONCE_CELL_INITIALIZER;
        uint32_t loc = 0;
        CHECK(lean_uint32_once_cold(&loc, &tok, init_uint32) == UINT32_C(0x8fedc0de));
        CHECK(lean_uint32_once_cold(&loc, &tok, init_uint32) == UINT32_C(0x8fedc0de));
        CHECK(loc == UINT32_C(0x8fedc0de));
        CHECK(g_uint32_count == 1);
    }

    {
        lean_once_cell_t tok = LEAN_ONCE_CELL_INITIALIZER;
        uint64_t loc = 0;
        CHECK(lean_uint64_once_cold(&loc, &tok, init_uint64) == UINT64_C(0x8fedc0dedeadbeef));
        CHECK(lean_uint64_once_cold(&loc, &tok, init_uint64) == UINT64_C(0x8fedc0dedeadbeef));
        CHECK(loc == UINT64_C(0x8fedc0dedeadbeef));
        CHECK(g_uint64_count == 1);
    }

    {
        lean_once_cell_t tok = LEAN_ONCE_CELL_INITIALIZER;
        size_t loc = 0;
        CHECK(lean_usize_once_cold(&loc, &tok, init_usize) == (size_t)0x12345678);
        CHECK(lean_usize_once_cold(&loc, &tok, init_usize) == (size_t)0x12345678);
        CHECK(loc == (size_t)0x12345678);
        CHECK(g_usize_count == 1);
    }

    return 0;
}
