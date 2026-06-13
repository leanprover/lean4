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

static int check_option_some(lean_object *opt, lean_object *expected) {
    lean_ctor_object *ctor = (lean_ctor_object *)opt;
    CHECK(opt != NULL);
    CHECK(!lean_is_scalar(opt));
    CHECK(lean_obj_tag(opt) == 1);
    CHECK(ctor->m_header.m_other == 1);
    CHECK(ctor->m_objs[0] == expected);
    return 0;
}

static int check_heap_ctor(lean_object *result, unsigned tag, unsigned num_objs) {
    lean_ctor_object *ctor = (lean_ctor_object *)result;
    CHECK(result != NULL);
    CHECK(!lean_is_scalar(result));
    CHECK(lean_obj_tag(result) == tag);
    CHECK(ctor->m_header.m_other == num_objs);
    return 0;
}

static uint32_t get_ctor_uint32(lean_object *result, unsigned num_objs) {
    lean_ctor_object *ctor = (lean_ctor_object *)result;
    return *(uint32_t *)((uint8_t *)ctor->m_objs + ((size_t)num_objs * sizeof(void *)));
}

static int check_details_only(lean_object *result, unsigned tag, uint32_t code, lean_object *details) {
    lean_ctor_object *ctor = (lean_ctor_object *)result;
    CHECK(check_heap_ctor(result, tag, 1) == 0);
    CHECK(ctor->m_objs[0] == details);
    CHECK(get_ctor_uint32(result, 1) == code);
    return 0;
}

static int check_option_none(lean_object *result, unsigned tag, uint32_t code, lean_object *details) {
    lean_ctor_object *ctor = (lean_ctor_object *)result;
    CHECK(check_heap_ctor(result, tag, 2) == 0);
    CHECK(ctor->m_objs[0] == lean_box(0));
    CHECK(ctor->m_objs[1] == details);
    CHECK(get_ctor_uint32(result, 2) == code);
    return 0;
}

static int check_option_some_ctor(
    lean_object *result,
    unsigned tag,
    lean_object *filename,
    uint32_t code,
    lean_object *details
) {
    lean_ctor_object *ctor = (lean_ctor_object *)result;
    CHECK(check_heap_ctor(result, tag, 2) == 0);
    CHECK(check_option_some(ctor->m_objs[0], filename) == 0);
    CHECK(ctor->m_objs[1] == details);
    CHECK(get_ctor_uint32(result, 2) == code);
    return 0;
}

static int check_direct_filename(
    lean_object *result,
    unsigned tag,
    lean_object *filename,
    uint32_t code,
    lean_object *details
) {
    lean_ctor_object *ctor = (lean_ctor_object *)result;
    CHECK(check_heap_ctor(result, tag, 2) == 0);
    CHECK(ctor->m_objs[0] == filename);
    CHECK(ctor->m_objs[1] == details);
    CHECK(get_ctor_uint32(result, 2) == code);
    return 0;
}

int main(void) {
    const uint32_t code = 0xdecafbadU;

    {
        lean_object *details = lean_mk_string("already exists");
        lean_object *result = lean_mk_io_error_already_exists(code, details);
        CHECK(check_option_none(result, 0, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *filename = lean_mk_string("exists.txt");
        lean_object *details = lean_mk_string("already exists file");
        lean_object *result = lean_mk_io_error_already_exists_file(filename, code, details);
        CHECK(check_option_some_ctor(result, 0, filename, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *result = lean_mk_io_error_eof(lean_box(0));
        CHECK(result != NULL);
        CHECK(lean_is_scalar(result));
        CHECK(lean_obj_tag(result) == 17);
    }

    {
        lean_object *details = lean_mk_string("hardware fault");
        lean_object *result = lean_mk_io_error_hardware_fault(code, details);
        CHECK(check_details_only(result, 5, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *details = lean_mk_string("illegal operation");
        lean_object *result = lean_mk_io_error_illegal_operation(code, details);
        CHECK(check_details_only(result, 7, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *details = lean_mk_string("inappropriate type");
        lean_object *result = lean_mk_io_error_inappropriate_type(code, details);
        CHECK(check_option_none(result, 15, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *filename = lean_mk_string("dir");
        lean_object *details = lean_mk_string("inappropriate type file");
        lean_object *result = lean_mk_io_error_inappropriate_type_file(filename, code, details);
        CHECK(check_option_some_ctor(result, 15, filename, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *filename = lean_mk_string("interrupt");
        lean_object *details = lean_mk_string("interrupted");
        lean_object *result = lean_mk_io_error_interrupted(filename, code, details);
        CHECK(check_direct_filename(result, 10, filename, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *details = lean_mk_string("invalid argument");
        lean_object *result = lean_mk_io_error_invalid_argument(code, details);
        CHECK(check_option_none(result, 12, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *filename = lean_mk_string("bad.txt");
        lean_object *details = lean_mk_string("invalid argument file");
        lean_object *result = lean_mk_io_error_invalid_argument_file(filename, code, details);
        CHECK(check_option_some_ctor(result, 12, filename, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *filename = lean_mk_string("missing.txt");
        lean_object *details = lean_mk_string("no file or directory");
        lean_object *result = lean_mk_io_error_no_file_or_directory(filename, code, details);
        CHECK(check_direct_filename(result, 11, filename, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *details = lean_mk_string("no such thing");
        lean_object *result = lean_mk_io_error_no_such_thing(code, details);
        CHECK(check_option_none(result, 16, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *filename = lean_mk_string("ghost");
        lean_object *details = lean_mk_string("no such thing file");
        lean_object *result = lean_mk_io_error_no_such_thing_file(filename, code, details);
        CHECK(check_option_some_ctor(result, 16, filename, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *details = lean_mk_string("other error");
        lean_object *result = lean_mk_io_error_other_error(code, details);
        CHECK(check_details_only(result, 1, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *details = lean_mk_string("permission denied");
        lean_object *result = lean_mk_io_error_permission_denied(code, details);
        CHECK(check_option_none(result, 13, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *filename = lean_mk_string("secret");
        lean_object *details = lean_mk_string("permission denied file");
        lean_object *result = lean_mk_io_error_permission_denied_file(filename, code, details);
        CHECK(check_option_some_ctor(result, 13, filename, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *details = lean_mk_string("protocol error");
        lean_object *result = lean_mk_io_error_protocol_error(code, details);
        CHECK(check_details_only(result, 8, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *details = lean_mk_string("resource busy");
        lean_object *result = lean_mk_io_error_resource_busy(code, details);
        CHECK(check_details_only(result, 2, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *details = lean_mk_string("resource exhausted");
        lean_object *result = lean_mk_io_error_resource_exhausted(code, details);
        CHECK(check_option_none(result, 14, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *filename = lean_mk_string("full");
        lean_object *details = lean_mk_string("resource exhausted file");
        lean_object *result = lean_mk_io_error_resource_exhausted_file(filename, code, details);
        CHECK(check_option_some_ctor(result, 14, filename, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *details = lean_mk_string("resource vanished");
        lean_object *result = lean_mk_io_error_resource_vanished(code, details);
        CHECK(check_details_only(result, 3, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *details = lean_mk_string("time expired");
        lean_object *result = lean_mk_io_error_time_expired(code, details);
        CHECK(check_details_only(result, 9, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *details = lean_mk_string("unsatisfied constraints");
        lean_object *result = lean_mk_io_error_unsatisfied_constraints(code, details);
        CHECK(check_details_only(result, 6, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *details = lean_mk_string("unsupported operation");
        lean_object *result = lean_mk_io_error_unsupported_operation(code, details);
        CHECK(check_details_only(result, 4, code, details) == 0);
        lean_dec(result);
    }

    {
        lean_object *msg = lean_mk_string("user error");
        lean_object *result = lean_mk_io_user_error(msg);
        lean_ctor_object *ctor = (lean_ctor_object *)result;
        CHECK(check_heap_ctor(result, 18, 1) == 0);
        CHECK(ctor->m_objs[0] == msg);
        lean_dec(result);
    }

    return 0;
}
