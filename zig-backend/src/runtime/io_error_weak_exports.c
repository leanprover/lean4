// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

#include <stdint.h>

void *lean_mk_io_error_already_exists_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_already_exists_file_zig_impl(void *filename, uint32_t os_code, void *details);
void *lean_mk_io_error_eof_zig_impl(void *unit);
void *lean_mk_io_error_hardware_fault_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_illegal_operation_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_inappropriate_type_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_inappropriate_type_file_zig_impl(void *filename, uint32_t os_code, void *details);
void *lean_mk_io_error_interrupted_zig_impl(void *filename, uint32_t os_code, void *details);
void *lean_mk_io_error_invalid_argument_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_invalid_argument_file_zig_impl(void *filename, uint32_t os_code, void *details);
void *lean_mk_io_error_no_file_or_directory_zig_impl(void *filename, uint32_t os_code, void *details);
void *lean_mk_io_error_no_such_thing_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_no_such_thing_file_zig_impl(void *filename, uint32_t os_code, void *details);
void *lean_mk_io_error_other_error_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_permission_denied_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_permission_denied_file_zig_impl(void *filename, uint32_t os_code, void *details);
void *lean_mk_io_error_protocol_error_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_resource_busy_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_resource_exhausted_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_resource_exhausted_file_zig_impl(void *filename, uint32_t os_code, void *details);
void *lean_mk_io_error_resource_vanished_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_time_expired_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_unsatisfied_constraints_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_error_unsupported_operation_zig_impl(uint32_t os_code, void *details);
void *lean_mk_io_user_error_zig_impl(void *msg);

#define LEAN_IO_ERROR_WRAPPER(name)                                                 \
    __attribute__((weak)) void *name(uint32_t os_code, void *details) {             \
        return name##_zig_impl(os_code, details);                                   \
    }

#define LEAN_IO_ERROR_FILE_WRAPPER(name)                                            \
    __attribute__((weak)) void *name(void *filename, uint32_t os_code, void *details) { \
        return name##_zig_impl(filename, os_code, details);                         \
    }

LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_already_exists)
LEAN_IO_ERROR_FILE_WRAPPER(lean_mk_io_error_already_exists_file)

__attribute__((weak)) void *lean_mk_io_error_eof(void *unit) {
    return lean_mk_io_error_eof_zig_impl(unit);
}

LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_hardware_fault)
LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_illegal_operation)
LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_inappropriate_type)
LEAN_IO_ERROR_FILE_WRAPPER(lean_mk_io_error_inappropriate_type_file)
LEAN_IO_ERROR_FILE_WRAPPER(lean_mk_io_error_interrupted)
LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_invalid_argument)
LEAN_IO_ERROR_FILE_WRAPPER(lean_mk_io_error_invalid_argument_file)
LEAN_IO_ERROR_FILE_WRAPPER(lean_mk_io_error_no_file_or_directory)
LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_no_such_thing)
LEAN_IO_ERROR_FILE_WRAPPER(lean_mk_io_error_no_such_thing_file)
LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_other_error)
LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_permission_denied)
LEAN_IO_ERROR_FILE_WRAPPER(lean_mk_io_error_permission_denied_file)
LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_protocol_error)
LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_resource_busy)
LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_resource_exhausted)
LEAN_IO_ERROR_FILE_WRAPPER(lean_mk_io_error_resource_exhausted_file)
LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_resource_vanished)
LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_time_expired)
LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_unsatisfied_constraints)
LEAN_IO_ERROR_WRAPPER(lean_mk_io_error_unsupported_operation)

__attribute__((weak)) void *lean_mk_io_user_error(void *msg) {
    return lean_mk_io_user_error_zig_impl(msg);
}
