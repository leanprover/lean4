/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#define LEANRT_CPP_PARTIAL_HIDE(name) leanrt_cpp_partial_hidden_##name##_impl

#define lean_internal_panic LEANRT_CPP_PARTIAL_HIDE(lean_internal_panic)
#define lean_internal_panic_out_of_memory LEANRT_CPP_PARTIAL_HIDE(lean_internal_panic_out_of_memory)
#define lean_internal_panic_unreachable LEANRT_CPP_PARTIAL_HIDE(lean_internal_panic_unreachable)
#define lean_internal_panic_rc_overflow LEANRT_CPP_PARTIAL_HIDE(lean_internal_panic_rc_overflow)
#define lean_internal_panic_overflow LEANRT_CPP_PARTIAL_HIDE(lean_internal_panic_overflow)
#define lean_set_exit_on_panic LEANRT_CPP_PARTIAL_HIDE(lean_set_exit_on_panic)
#define lean_set_panic_messages LEANRT_CPP_PARTIAL_HIDE(lean_set_panic_messages)
#define lean_panic LEANRT_CPP_PARTIAL_HIDE(lean_panic)
#define lean_panic_fn LEANRT_CPP_PARTIAL_HIDE(lean_panic_fn)
#define lean_panic_fn_borrowed LEANRT_CPP_PARTIAL_HIDE(lean_panic_fn_borrowed)
#define lean_alloc_object LEANRT_CPP_PARTIAL_HIDE(lean_alloc_object)
#define lean_free_object LEANRT_CPP_PARTIAL_HIDE(lean_free_object)
#define lean_object_byte_size LEANRT_CPP_PARTIAL_HIDE(lean_object_byte_size)
#define lean_object_data_byte_size LEANRT_CPP_PARTIAL_HIDE(lean_object_data_byte_size)
#define lean_register_external_class LEANRT_CPP_PARTIAL_HIDE(lean_register_external_class)
#define lean_dec_ref_cold LEANRT_CPP_PARTIAL_HIDE(lean_dec_ref_cold)
#define lean_array_get_panic LEANRT_CPP_PARTIAL_HIDE(lean_array_get_panic)
#define lean_array_set_panic LEANRT_CPP_PARTIAL_HIDE(lean_array_set_panic)
#define lean_mark_persistent LEANRT_CPP_PARTIAL_HIDE(lean_mark_persistent)
#define lean_mark_mt LEANRT_CPP_PARTIAL_HIDE(lean_mark_mt)
#define lean_mk_string_unchecked LEANRT_CPP_PARTIAL_HIDE(lean_mk_string_unchecked)
#define lean_mk_string_from_bytes LEANRT_CPP_PARTIAL_HIDE(lean_mk_string_from_bytes)
#define lean_mk_string_from_bytes_unchecked LEANRT_CPP_PARTIAL_HIDE(lean_mk_string_from_bytes_unchecked)
#define lean_mk_string LEANRT_CPP_PARTIAL_HIDE(lean_mk_string)
#define lean_mk_ascii_string_unchecked LEANRT_CPP_PARTIAL_HIDE(lean_mk_ascii_string_unchecked)
#define lean_string_push LEANRT_CPP_PARTIAL_HIDE(lean_string_push)
#define lean_string_append LEANRT_CPP_PARTIAL_HIDE(lean_string_append)
#define lean_string_eq_cold LEANRT_CPP_PARTIAL_HIDE(lean_string_eq_cold)
#define lean_sarray_eq_cold LEANRT_CPP_PARTIAL_HIDE(lean_sarray_eq_cold)
#define lean_string_lt LEANRT_CPP_PARTIAL_HIDE(lean_string_lt)
#define lean_string_utf8_get LEANRT_CPP_PARTIAL_HIDE(lean_string_utf8_get)
#define lean_string_utf8_get_fast_cold LEANRT_CPP_PARTIAL_HIDE(lean_string_utf8_get_fast_cold)
#define lean_string_utf8_next LEANRT_CPP_PARTIAL_HIDE(lean_string_utf8_next)
#define lean_string_utf8_next_fast_cold LEANRT_CPP_PARTIAL_HIDE(lean_string_utf8_next_fast_cold)
#define lean_string_utf8_prev LEANRT_CPP_PARTIAL_HIDE(lean_string_utf8_prev)
#define lean_copy_byte_array LEANRT_CPP_PARTIAL_HIDE(lean_copy_byte_array)
#define lean_byte_array_mk LEANRT_CPP_PARTIAL_HIDE(lean_byte_array_mk)
#define lean_byte_array_data LEANRT_CPP_PARTIAL_HIDE(lean_byte_array_data)
#define lean_byte_array_push LEANRT_CPP_PARTIAL_HIDE(lean_byte_array_push)
#define lean_byte_array_hash LEANRT_CPP_PARTIAL_HIDE(lean_byte_array_hash)
#define lean_slice_hash leanrt_cpp_partial_hidden_misc_slice_hash_impl
#define lean_slice_dec_lt leanrt_cpp_partial_hidden_misc_slice_dec_lt_impl
#define lean_copy_float_array LEANRT_CPP_PARTIAL_HIDE(lean_copy_float_array)
#define lean_float_array_mk LEANRT_CPP_PARTIAL_HIDE(lean_float_array_mk)
#define lean_float_array_data LEANRT_CPP_PARTIAL_HIDE(lean_float_array_data)
#define lean_float_array_push LEANRT_CPP_PARTIAL_HIDE(lean_float_array_push)
#define lean_float_to_string LEANRT_CPP_PARTIAL_HIDE(lean_float_to_string)
#define lean_float_scaleb LEANRT_CPP_PARTIAL_HIDE(lean_float_scaleb)
#define lean_float_isnan LEANRT_CPP_PARTIAL_HIDE(lean_float_isnan)
#define lean_float_isfinite LEANRT_CPP_PARTIAL_HIDE(lean_float_isfinite)
#define lean_float_isinf LEANRT_CPP_PARTIAL_HIDE(lean_float_isinf)
#define lean_float_frexp LEANRT_CPP_PARTIAL_HIDE(lean_float_frexp)
#define lean_copy_expand_array LEANRT_CPP_PARTIAL_HIDE(lean_copy_expand_array)
#define lean_copy_expand_array_nonlinear LEANRT_CPP_PARTIAL_HIDE(lean_copy_expand_array_nonlinear)
#define lean_array_push LEANRT_CPP_PARTIAL_HIDE(lean_array_push)
#define lean_mk_array LEANRT_CPP_PARTIAL_HIDE(lean_mk_array)
#define lean_float_of_bits LEANRT_CPP_PARTIAL_HIDE(lean_float_of_bits)
#define lean_float_to_bits LEANRT_CPP_PARTIAL_HIDE(lean_float_to_bits)
#define lean_float_once_cold LEANRT_CPP_PARTIAL_HIDE(lean_float_once_cold)
#define lean_float32_to_string LEANRT_CPP_PARTIAL_HIDE(lean_float32_to_string)
#define lean_float32_scaleb LEANRT_CPP_PARTIAL_HIDE(lean_float32_scaleb)
#define lean_float32_isnan LEANRT_CPP_PARTIAL_HIDE(lean_float32_isnan)
#define lean_float32_isfinite LEANRT_CPP_PARTIAL_HIDE(lean_float32_isfinite)
#define lean_float32_isinf LEANRT_CPP_PARTIAL_HIDE(lean_float32_isinf)
#define lean_float32_frexp LEANRT_CPP_PARTIAL_HIDE(lean_float32_frexp)
#define lean_float32_of_bits LEANRT_CPP_PARTIAL_HIDE(lean_float32_of_bits)
#define lean_float32_to_bits LEANRT_CPP_PARTIAL_HIDE(lean_float32_to_bits)
#define lean_float32_once_cold LEANRT_CPP_PARTIAL_HIDE(lean_float32_once_cold)
#define lean_obj_once_cold LEANRT_CPP_PARTIAL_HIDE(lean_obj_once_cold)
#define lean_uint8_once_cold LEANRT_CPP_PARTIAL_HIDE(lean_uint8_once_cold)
#define lean_uint16_once_cold LEANRT_CPP_PARTIAL_HIDE(lean_uint16_once_cold)
#define lean_uint32_once_cold LEANRT_CPP_PARTIAL_HIDE(lean_uint32_once_cold)
#define lean_uint64_once_cold LEANRT_CPP_PARTIAL_HIDE(lean_uint64_once_cold)
#define lean_usize_once_cold LEANRT_CPP_PARTIAL_HIDE(lean_usize_once_cold)
#define lean_thunk_get_core leanrt_cpp_partial_hidden_thunk_get_core_impl
#define lean_dbg_trace LEANRT_CPP_PARTIAL_HIDE(lean_dbg_trace)
#define lean_dbg_sleep LEANRT_CPP_PARTIAL_HIDE(lean_dbg_sleep)
#define lean_dbg_trace_if_shared LEANRT_CPP_PARTIAL_HIDE(lean_dbg_trace_if_shared)
#define lean_name_eq leanrt_cpp_partial_hidden_misc_name_eq_impl

#include LEANRT_CPP_PARTIAL_OBJECT_CPP

extern "C" void leanrt_task_deactivate_task_impl(lean_task_object *);
extern "C" void leanrt_task_deactivate_promise_impl(lean_object *);

namespace lean {
scoped_task_manager::scoped_task_manager(unsigned num_workers) {
    lean_init_task_manager_using(num_workers);
}

scoped_task_manager::~scoped_task_manager() {
    lean_finalize_task_manager();
}

void deactivate_task(lean_task_object * task) {
    leanrt_task_deactivate_task_impl(task);
}

void deactivate_promise(lean_promise_object * promise) {
    leanrt_task_deactivate_promise_impl(reinterpret_cast<lean_object *>(promise));
}

lean_object * lean_promise_new() {
    return lean_io_promise_new();
}

void lean_promise_resolve(lean_object * value, lean_object * promise) {
    (void)lean_io_promise_resolve(value, promise);
}
}

extern "C" lean_task_object * leanrt_cpp_partial_hidden_current_task_get() {
    return lean::g_current_task_object;
}

extern "C" lean_task_object * leanrt_cpp_partial_hidden_current_task_swap(lean_task_object * task) {
    lean_task_object * prev = lean::g_current_task_object;
    lean::g_current_task_object = task;
    return prev;
}
