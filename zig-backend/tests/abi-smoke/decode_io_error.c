#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <lean/lean.h>

#define CHECK(cond)                                                                 \
    do {                                                                            \
        if (!(cond)) {                                                              \
            fprintf(stderr, "FAIL:%s:%d: %s\n", __FILE__, __LINE__, #cond);         \
            return 1;                                                               \
        }                                                                           \
    } while (0)

extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
extern void leanrt_test_allocator_reset_counters(void);
extern size_t leanrt_test_allocator_alloc_count(void);
extern size_t leanrt_test_allocator_free_count(void);

static int check_tag(lean_object *result, unsigned expected_tag) {
    CHECK(result != NULL);
    CHECK(!lean_is_scalar(result));
    CHECK(lean_obj_tag(result) == expected_tag);
    return 0;
}

static int check_option_some_filename(lean_object *result, unsigned expected_tag, lean_object *filename) {
    lean_ctor_object *ctor = (lean_ctor_object *)result;
    lean_ctor_object *some = (lean_ctor_object *)ctor->m_objs[0];
    CHECK(check_tag(result, expected_tag) == 0);
    CHECK(ctor->m_header.m_other == 2);
    CHECK(some != NULL);
    CHECK(!lean_is_scalar((lean_object *)some));
    CHECK(lean_obj_tag((lean_object *)some) == 1);
    CHECK(some->m_objs[0] == filename);
    return 0;
}

static int check_direct_filename(lean_object *result, unsigned expected_tag, lean_object *filename) {
    lean_ctor_object *ctor = (lean_ctor_object *)result;
    CHECK(check_tag(result, expected_tag) == 0);
    CHECK(ctor->m_header.m_other == 2);
    CHECK(ctor->m_objs[0] == filename);
    return 0;
}

static int check_errno_tag(int errnum, int uv_errnum, unsigned expected_tag) {
    lean_object *io_result = lean_decode_io_error(errnum, NULL);
    lean_object *uv_result = lean_decode_uv_error(uv_errnum, NULL);
    CHECK(check_tag(io_result, expected_tag) == 0);
    CHECK(check_tag(uv_result, expected_tag) == 0);
    lean_dec(io_result);
    lean_dec(uv_result);
    return 0;
}

static int check_filename_variant(int errnum, int uv_errnum, unsigned expected_tag, int direct_ctor) {
    lean_object *filename = lean_mk_string("test-path");
    lean_object *io_result = lean_decode_io_error(errnum, filename);
    lean_object *uv_result = lean_decode_uv_error(uv_errnum, filename);
    if (direct_ctor) {
        CHECK(check_direct_filename(io_result, expected_tag, filename) == 0);
        CHECK(check_direct_filename(uv_result, expected_tag, filename) == 0);
    } else {
        CHECK(check_option_some_filename(io_result, expected_tag, filename) == 0);
        CHECK(check_option_some_filename(uv_result, expected_tag, filename) == 0);
    }
    lean_dec(io_result);
    lean_dec(uv_result);
    lean_dec(filename);
    return 0;
}

static int check_unknown_errno(void) {
    lean_ctor_object *ctor;
    lean_object *result = lean_decode_io_error(0xDEAD, NULL);
    CHECK(check_tag(result, 1) == 0);
    ctor = (lean_ctor_object *)result;
    CHECK(strstr(lean_string_cstr(ctor->m_objs[0]), "57005") != NULL);
    lean_dec(result);
    return 0;
}

static int check_reference_ownership(void) {
    int i;
    leanrt_test_allocator_reset_counters();
    for (i = 0; i < 100; ++i) {
        lean_object *result = lean_decode_io_error(ENOENT, NULL);
        CHECK(result != NULL);
        lean_dec(result);
    }
    CHECK(leanrt_test_allocator_alloc_count() == leanrt_test_allocator_free_count());
    return 0;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_initialize_thread();

    CHECK(check_errno_tag(ENOENT, -ENOENT, 11) == 0);
    CHECK(check_errno_tag(EACCES, -EACCES, 13) == 0);
    CHECK(check_errno_tag(EEXIST, -EEXIST, 0) == 0);
    CHECK(check_errno_tag(EBUSY, -EBUSY, 2) == 0);
    CHECK(check_errno_tag(ENOSPC, -ENOSPC, 14) == 0);
    CHECK(check_errno_tag(EAGAIN, -EAGAIN, 14) == 0);
    CHECK(check_errno_tag(EINTR, -EINTR, 10) == 0);
    CHECK(check_errno_tag(EPIPE, -EPIPE, 3) == 0);

    CHECK(check_filename_variant(ENOENT, -ENOENT, 11, 1) == 0);
    CHECK(check_filename_variant(EACCES, -EACCES, 13, 0) == 0);
    CHECK(check_filename_variant(EEXIST, -EEXIST, 0, 0) == 0);
    CHECK(check_filename_variant(ENOSPC, -ENOSPC, 14, 0) == 0);
    CHECK(check_filename_variant(EAGAIN, -EAGAIN, 14, 0) == 0);
    CHECK(check_filename_variant(EINTR, -EINTR, 10, 1) == 0);

    CHECK(check_unknown_errno() == 0);
    CHECK(check_reference_ownership() == 0);

    lean_finalize_thread();
    return 0;
}
