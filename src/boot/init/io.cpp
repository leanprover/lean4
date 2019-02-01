// Lean compiler output
// Module: init.io
// Imports: init.control.state init.control.except init.data.string.basic init.control.coroutine
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;
obj* _l_s8_io__unit_s9_has__eval(obj*, obj*);
obj* _l_s13_coroutine__io_s4_pipe(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s10_read__file_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*);
obj* _l_s8_function_s4_comp_s6___rarg(obj*, obj*, obj*);
obj* _l_s9_from__eio(obj*, obj*);
obj* _l_s2_io_s7_println(obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s9_get__line_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__8(obj*, obj*);
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__6(obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s9___private_3644302523__s8_put__str_s9___spec__1(obj*, obj*);
obj* _l_s9_monad__io;
obj* _l_s13_coroutine__io_s6_resume_s6___rarg(obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s4_bind_s6___rarg(obj*, obj*);
obj* _l_s2_id_s5_monad_s11___lambda__2(obj*, obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s9_monad__io(obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s6_resume(obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__8(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s2_mk_s9___spec__1(obj*, obj*);
obj* _l_s2_io_s4_prim_s7_iterate_s6___main_s6___rarg(obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s2_mk_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, unsigned char, unsigned char);
obj* _l_s2_io_s4_prim_s7_iterate_s6___rarg(obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s5_yield(obj*, obj*);
obj* _l_s2_io_s11_println_x27(obj*, obj*);
obj* _l_s2_io_s9_has__eval(obj*);
obj* _l_s9___private_3644302523__s8_put__str_s4___at_s2_io_s7_println_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s5_flush_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s5_close_s9___spec__1(obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s7_is__eof_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__1(obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s9_get__line_s9___spec__1(obj*, obj*);
obj* _l_s2_id_s5_monad_s11___lambda__3(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s7_println_s4___at_s2_io_s11_println_x27_s9___spec__1(obj*, obj*);
obj* _l_s2_io_s4_prim_s12_iterate__eio(obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s10_read__file_s6___rarg_s11___lambda__1(obj*, obj*, unsigned char);
obj* _l_s13_coroutine__io_s6_mk__st(obj*, obj*, obj*);
obj* _l_s9_coroutine_s5_yield_s6___rarg_s11___lambda__1_s11___closed__1;
obj* _l_s8_function_s5_const_s6___rarg(obj*, obj*);
obj* _l_s13_coroutine__io_s16_monad__coroutine(obj*, obj*);
obj* _l_s3_eio;
obj* _l_s2_io_s2_fs_s6_handle_s2_mk(obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s9_get__line_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s2_io_s7_println_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s2_io_s5_monad;
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s7_is__eof_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s9_has__repr_s9_has__eval(obj*);
obj* _l_s13_coroutine__io_s5_yield_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s5_close_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__4(obj*, obj*);
obj* _l_s9_eio__unit_s9_has__eval_s6___rarg(obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s4_bind_s6___main(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s9_get__line(obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio(obj*, obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s9___private_3644302523__s8_put__str_s9___spec__1_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s4_prim_s6_handle_s2_mk_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s13_read__to__end_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s4_pipe_s6___main(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s10_read__file_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s8_state__t_s5_monad_s6___rarg(obj*);
obj* _l_s13_coroutine__io_s6_resume_s6___main(obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__7(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s7_println_s6___rarg_s11___closed__1;
obj* _l_s13_coroutine__io_s5_monad(obj*, obj*);
obj* _l_s2_io_s4_prim_s7_iterate_s6___main(obj*, obj*);
obj* _l_s2_io_s4_prim_s7_iterate(obj*, obj*);
obj* _l_s2_io_s4_prim_s7_iterate_s6___main_s4___at_s2_io_s4_prim_s12_iterate__eio_s9___spec__1_s6___rarg(obj*, obj*, obj*);
obj* _l_s2_io_s9_has__eval_s6___rarg(obj*, obj*, obj*);
obj* _l_s2_id_s5_monad_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s6_mk__st_s6___rarg(obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s4_pipe_s6___rarg(obj*, obj*);
obj* _l_s13_coroutine__io_s4_read_s6___rarg(obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__7_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s5_yield_s6___rarg_s11___closed__1;
obj* _l_s9___private_3644302523__s8_put__str_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s5_flush(obj*, obj*);
obj* _l_s21_coroutine__result__io;
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s7_println_s9___spec__2(obj*, obj*);
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__1_s11___closed__1;
obj* _l_s2_io_s5_error_s15_has__to__string;
obj* _l_s2_io_s2_fs_s6_handle_s7_is__eof_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__2(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__7(obj*, obj*);
obj* _l_s2_io_s5_print_s4___at_s2_io_s11_println_x27_s9___spec__2(obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s9_monad__io_s6___rarg(obj*, obj*, obj*);
obj* _l_s2_io_s4_prim_s12_iterate__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__5(obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s5_flush_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_string_s4_join_s11___closed__1;
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s7_is__eof_s9___spec__1(obj*, obj*);
obj* _l_s2_io_s5_print(obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s5_flush_s9___spec__1(obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s2_mk_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s2_io_s4_prim_s7_iterate_s6___main_s4___at_s2_io_s4_prim_s12_iterate__eio_s9___spec__1(obj*, obj*, obj*);
obj* _l_s6_string_s9_has__lift(obj*);
obj* _l_s2_io_s4_prim_s7_iterate_s6___main_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__6(obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s10_read__file_s6___rarg(obj*, obj*, obj*, obj*, obj*, unsigned char);
obj* _l_s2_io;
obj* _l_s13_coroutine__io_s6_resume_s6___main_s6___rarg(obj*, obj*, obj*);
obj* _l_s2_io_s5_print_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s7_is__eof(obj*, obj*);
obj* _l_s13_coroutine__io_s5_yield_s6___rarg(obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__4(obj*, obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s4_pure(obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s13_monad__reader(obj*, obj*);
obj* _l_s9___private_3644302523__s8_put__str(obj*, obj*);
obj* _l_s13_coroutine__io_s5_monad_s11___closed__1;
obj* _l_s13_coroutine__io_s13_monad__reader_s6___rarg(obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s9___private_3644302523__s8_put__str_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s9_get__line_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__3(obj*, obj*);
obj* _l_s2_io_s2_fs_s10_read__file_s6___rarg_s7___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s4_bind(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s4_prim_s12_iterate__eio_s6___rarg(obj*, obj*, obj*);
obj* _l_s9_eio__unit_s9_has__eval(obj*);
obj* _l_s9_has__repr_s9_has__eval_s6___rarg(obj*, obj*, obj*);
obj* _l_s2_id(obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s7_println_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_string_s15_has__to__string(obj*);
obj* _l_s13_coroutine__io_s4_pipe_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s5_close(obj*, obj*);
obj* _l_s13_coroutine__io_s4_pure_s6___rarg(obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s13_read__to__end(obj*, obj*);
obj* _l_s13_coroutine__io_s4_read(obj*, obj*);
obj* _l_s3_eio_s9_has__eval_s6___rarg_s11___closed__1;
obj* _l_s2_io_s5_error;
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__2(obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s2_mk_s6___rarg_s7___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s13_coroutine__io_s4_bind_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s3_eio_s9_has__eval(obj*, obj*);
obj* _l_s2_io_s2_fs_s10_read__file(obj*, obj*);
obj* _l_s2_io_s2_fs_s10_read__file_s6___rarg_s11___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s5_close_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s2_mk_s6___rarg(obj*, obj*, obj*, obj*, obj*, unsigned char, unsigned char);
obj* _l_s9___private_3644302523__s8_put__str_s4___at_s2_io_s7_println_s9___spec__1(obj*, obj*);
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__3(obj*, obj*);
obj* _l_s2_id_s4_bind(obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s11_println_x27_s9___spec__4(obj*, obj*);
obj* _l_s9___private_3644302523__s8_put__str_s4___at_s2_io_s11_println_x27_s9___spec__3(obj*, obj*);
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__2(obj*, obj*);
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__5(obj*, obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s2_mk_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__1_s6___rarg_s7___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s2_io_s2_fs_s6_handle_s2_mk_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__1(obj*, obj*);
obj* _l_s3_eio_s9_has__eval_s6___rarg(obj*, obj*, obj*, obj*);
obj* _init__l_s2_io() {
{
obj* x_0;
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s2_io_s5_monad() {
{
obj* x_0;
obj* x_1;
obj* x_2;
obj* x_3;
obj* x_4;
obj* x_5;
obj* x_6;
obj* x_7;
obj* x_8;
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_5 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_0);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set(x_5, 4, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = _l_s8_state__t_s5_monad_s6___rarg(x_7);
return x_8;
}
}
obj* _init__l_s9_monad__io() {
{
obj* x_0;
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s2_io_s5_error() {
{
obj* x_0;
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s2_io_s5_error_s15_has__to__string() {
{
obj* x_0;
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_string_s15_has__to__string), 1, 0);
return x_0;
}
}
obj* _l_s6_string_s9_has__lift(obj* x_0) {
{
return x_0;
}
}
obj* _init__l_s3_eio() {
{
obj* x_0;
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s2_io_s4_prim_s7_iterate_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4;
obj* x_5;
obj* x_7;
obj* x_9;
lean::inc(x_1);
x_4 = lean::apply_2(x_1, x_0, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
}
if (lean::obj_tag(x_5) == 0)
{
obj* x_11;
obj* x_14;
lean::dec(x_9);
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
lean::dec(x_5);
x_14 = _l_s2_io_s4_prim_s7_iterate_s6___main_s6___rarg(x_11, x_1, x_7);
return x_14;
}
else
{
obj* x_16;
obj* x_19;
lean::dec(x_1);
x_16 = lean::cnstr_get(x_5, 0);
lean::inc(x_16);
lean::dec(x_5);
if (lean::is_scalar(x_9)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_9;
}
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_7);
return x_19;
}
}
}
obj* _l_s2_io_s4_prim_s7_iterate_s6___main(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s7_iterate_s6___main_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s2_io_s4_prim_s7_iterate_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
x_3 = _l_s2_io_s4_prim_s7_iterate_s6___main_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s2_io_s4_prim_s7_iterate(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s7_iterate_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s2_io_s4_prim_s12_iterate__eio_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
x_3 = _l_s2_io_s4_prim_s7_iterate_s6___main_s4___at_s2_io_s4_prim_s12_iterate__eio_s9___spec__1_s6___rarg(x_1, x_0, x_2);
return x_3;
}
}
obj* _l_s2_io_s4_prim_s12_iterate__eio(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s12_iterate__eio_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s2_io_s4_prim_s7_iterate_s6___main_s4___at_s2_io_s4_prim_s12_iterate__eio_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4;
obj* x_5;
obj* x_7;
obj* x_9;
lean::inc(x_0);
x_4 = lean::apply_2(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
}
if (lean::obj_tag(x_5) == 0)
{
obj* x_11;
obj* x_13;
obj* x_14;
obj* x_15;
lean::dec(x_0);
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_13 = x_5;
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_7);
return x_15;
}
else
{
obj* x_16;
obj* x_18;
x_16 = lean::cnstr_get(x_5, 0);
lean::inc(x_16);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_18 = x_5;
}
if (lean::obj_tag(x_16) == 0)
{
obj* x_21;
obj* x_24;
lean::dec(x_9);
lean::dec(x_18);
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
lean::dec(x_16);
x_24 = _l_s2_io_s4_prim_s7_iterate_s6___main_s4___at_s2_io_s4_prim_s12_iterate__eio_s9___spec__1_s6___rarg(x_0, x_21, x_7);
return x_24;
}
else
{
obj* x_26;
obj* x_29;
obj* x_30;
lean::dec(x_0);
x_26 = lean::cnstr_get(x_16, 0);
lean::inc(x_26);
lean::dec(x_16);
if (lean::is_scalar(x_18)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_18;
}
lean::cnstr_set(x_29, 0, x_26);
if (lean::is_scalar(x_9)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_9;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
return x_30;
}
}
}
}
obj* _l_s2_io_s4_prim_s7_iterate_s6___main_s4___at_s2_io_s4_prim_s12_iterate__eio_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s7_iterate_s6___main_s4___at_s2_io_s4_prim_s12_iterate__eio_s9___spec__1_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s2_io_s4_prim_s6_handle_s2_mk_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4;
unsigned char x_5;
obj* x_6;
x_4 = lean::unbox(x_1);
x_5 = lean::unbox(x_2);
x_6 = lean::io_prim_handle_mk(x_0, x_4, x_5, x_3);
return x_6;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_7;
obj* x_8;
obj* x_9;
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5;
obj* x_8;
obj* x_11;
obj* x_12;
lean::dec(x_2);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::apply_1(x_1, x_5);
x_12 = lean::apply_2(x_8, lean::box(0), x_11);
return x_12;
}
else
{
obj* x_15;
obj* x_18;
obj* x_21;
obj* x_24;
lean::dec(x_0);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = lean::apply_2(x_21, lean::box(0), x_15);
return x_24;
}
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s6___rarg), 5, 0);
return x_6;
}
}
obj* _l_s9___private_3644302523__s8_put__str_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_6;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_put_str), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = _l_s2_io_s4_prim_s9_lift__eio_s4___at_s9___private_3644302523__s8_put__str_s9___spec__1_s6___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* _l_s9___private_3644302523__s8_put__str(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_3644302523__s8_put__str_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s9___private_3644302523__s8_put__str_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_7;
obj* x_8;
obj* x_9;
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s9___private_3644302523__s8_put__str_s9___spec__1_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s9___private_3644302523__s8_put__str_s9___spec__1_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5;
obj* x_8;
obj* x_11;
obj* x_12;
lean::dec(x_2);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::apply_1(x_1, x_5);
x_12 = lean::apply_2(x_8, lean::box(0), x_11);
return x_12;
}
else
{
obj* x_15;
obj* x_18;
obj* x_21;
obj* x_24;
lean::dec(x_0);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = lean::apply_2(x_21, lean::box(0), x_15);
return x_24;
}
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s9___private_3644302523__s8_put__str_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s9___private_3644302523__s8_put__str_s9___spec__1_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s5_print_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
obj* x_8;
obj* x_9;
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_6);
x_9 = _l_s9___private_3644302523__s8_put__str_s6___rarg(x_0, x_1, x_2, x_3, x_8);
return x_9;
}
}
obj* _l_s2_io_s5_print(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s5_print_s6___rarg), 7, 0);
return x_4;
}
}
obj* _l_s2_io_s7_println_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
obj* x_8;
obj* x_10;
obj* x_17;
obj* x_18;
obj* x_20;
obj* x_21;
lean::dec(x_4);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 4);
lean::inc(x_10);
lean::dec(x_8);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_17 = _l_s2_io_s5_print_s6___rarg(x_0, x_1, x_2, x_3, lean::box(0), x_5, x_6);
x_18 = _l_s2_io_s7_println_s6___rarg_s11___closed__1;
lean::inc(x_18);
x_20 = _l_s9___private_3644302523__s8_put__str_s4___at_s2_io_s7_println_s9___spec__1_s6___rarg(x_0, x_1, x_2, x_3, x_18);
x_21 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_17, x_20);
return x_21;
}
}
obj* _init__l_s2_io_s7_println_s6___rarg_s11___closed__1() {
{
obj* x_0;
x_0 = lean::mk_string("\n");
return x_0;
}
}
obj* _l_s2_io_s7_println(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s7_println_s6___rarg), 7, 0);
return x_4;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s7_println_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_7;
obj* x_8;
obj* x_9;
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s9___private_3644302523__s8_put__str_s9___spec__1_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s7_println_s9___spec__2(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s7_println_s9___spec__2_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s9___private_3644302523__s8_put__str_s4___at_s2_io_s7_println_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_6;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_put_str), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s7_println_s9___spec__2_s6___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* _l_s9___private_3644302523__s8_put__str_s4___at_s2_io_s7_println_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_3644302523__s8_put__str_s4___at_s2_io_s7_println_s9___spec__1_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s2_mk_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, unsigned char x_5, unsigned char x_6) {
{
obj* x_7;
obj* x_8;
obj* x_9;
obj* x_10;
x_7 = lean::box(x_5);
x_8 = lean::box(x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s6_handle_s2_mk_s7___boxed), 4, 3);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_7);
lean::closure_set(x_9, 2, x_8);
x_10 = _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s2_mk_s9___spec__1_s6___rarg(x_0, x_1, x_2, x_3, x_9);
return x_10;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s2_mk(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s2_fs_s6_handle_s2_mk_s6___rarg_s7___boxed), 7, 0);
return x_4;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s2_mk_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_7;
obj* x_8;
obj* x_9;
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s2_mk_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s2_mk_s9___spec__1_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s2_mk_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
unsigned char x_7;
unsigned char x_8;
obj* x_9;
x_7 = lean::unbox(x_5);
x_8 = lean::unbox(x_6);
x_9 = _l_s2_io_s2_fs_s6_handle_s2_mk_s6___rarg(x_0, x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s7_is__eof_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_6;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_handle_is_eof), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s7_is__eof_s9___spec__1_s6___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s7_is__eof(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s2_fs_s6_handle_s7_is__eof_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s7_is__eof_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_7;
obj* x_8;
obj* x_9;
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s9___private_3644302523__s8_put__str_s9___spec__1_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s7_is__eof_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s7_is__eof_s9___spec__1_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s5_flush_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_6;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_handle_flush), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s5_flush_s9___spec__1_s6___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s5_flush(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s2_fs_s6_handle_s5_flush_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s5_flush_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_7;
obj* x_8;
obj* x_9;
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s9___private_3644302523__s8_put__str_s9___spec__1_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s5_flush_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s5_flush_s9___spec__1_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s5_close_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_6;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_handle_flush), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s5_close_s9___spec__1_s6___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s5_close(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s2_fs_s6_handle_s5_close_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s5_close_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_7;
obj* x_8;
obj* x_9;
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s9___private_3644302523__s8_put__str_s9___spec__1_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s5_close_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s5_close_s9___spec__1_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s9_get__line_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_6;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_handle_get_line), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s9_get__line_s9___spec__1_s6___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s9_get__line(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s2_fs_s6_handle_s9_get__line_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s9_get__line_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_7;
obj* x_8;
obj* x_9;
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s9_get__line_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s9_get__line_s9___spec__1_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s13_read__to__end_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_6;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s12_iterate__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__5), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__7_s6___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s13_read__to__end(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s2_fs_s6_handle_s13_read__to__end_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__2(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_3;
obj* x_5;
obj* x_7;
x_2 = lean::apply_1(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_7 = x_2;
}
if (lean::obj_tag(x_3) == 0)
{
obj* x_8;
obj* x_10;
obj* x_11;
obj* x_12;
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
return x_12;
}
else
{
obj* x_13;
obj* x_15;
obj* x_16;
obj* x_17;
x_13 = lean::cnstr_get(x_3, 0);
lean::inc(x_13);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_15 = x_3;
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
if (lean::is_scalar(x_7)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_7;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_5);
return x_17;
}
}
}
obj* _l_s2_io_s2_fs_s6_handle_s7_is__eof_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_3;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_handle_is_eof), 2, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__2(x_2, x_1);
return x_3;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__4(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_3;
obj* x_5;
obj* x_7;
x_2 = lean::apply_1(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_7 = x_2;
}
if (lean::obj_tag(x_3) == 0)
{
obj* x_8;
obj* x_10;
obj* x_11;
obj* x_12;
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
return x_12;
}
else
{
obj* x_13;
obj* x_15;
obj* x_16;
obj* x_17;
x_13 = lean::cnstr_get(x_3, 0);
lean::inc(x_13);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_15 = x_3;
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
if (lean::is_scalar(x_7)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_7;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_5);
return x_17;
}
}
}
obj* _l_s2_io_s2_fs_s6_handle_s9_get__line_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__3(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_3;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_handle_get_line), 2, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__4(x_2, x_1);
return x_3;
}
}
obj* _l_s2_io_s4_prim_s7_iterate_s6___main_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__6(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
obj* x_4;
obj* x_7;
obj* x_8;
obj* x_10;
lean::inc(x_0);
x_7 = _l_s2_io_s2_fs_s6_handle_s7_is__eof_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__1(x_0, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_14;
obj* x_16;
obj* x_17;
lean::dec(x_1);
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_16 = x_8;
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
x_3 = x_17;
x_4 = x_10;
goto lbl_5;
}
else
{
obj* x_18;
obj* x_20;
unsigned char x_21;
x_18 = lean::cnstr_get(x_8, 0);
lean::inc(x_18);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_20 = x_8;
}
x_21 = lean::unbox(x_18);
lean::dec(x_18);
if (x_21 == 0)
{
obj* x_24;
obj* x_25;
obj* x_27;
lean::inc(x_0);
x_24 = _l_s2_io_s2_fs_s6_handle_s9_get__line_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__3(x_0, x_10);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_31;
obj* x_34;
lean::dec(x_1);
x_31 = lean::cnstr_get(x_25, 0);
lean::inc(x_31);
lean::dec(x_25);
if (lean::is_scalar(x_20)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_20;
}
lean::cnstr_set(x_34, 0, x_31);
x_3 = x_34;
x_4 = x_27;
goto lbl_5;
}
else
{
obj* x_35;
obj* x_38;
obj* x_40;
obj* x_41;
x_35 = lean::cnstr_get(x_25, 0);
lean::inc(x_35);
lean::dec(x_25);
x_38 = lean::string_append(x_1, x_35);
lean::dec(x_35);
x_40 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_40, 0, x_38);
if (lean::is_scalar(x_20)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_20;
}
lean::cnstr_set(x_41, 0, x_40);
x_3 = x_41;
x_4 = x_27;
goto lbl_5;
}
}
else
{
obj* x_42;
obj* x_43;
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_1);
if (lean::is_scalar(x_20)) {
 x_43 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_43 = x_20;
}
lean::cnstr_set(x_43, 0, x_42);
x_3 = x_43;
x_4 = x_10;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_45;
obj* x_47;
obj* x_48;
obj* x_49;
lean::dec(x_0);
x_45 = lean::cnstr_get(x_3, 0);
lean::inc(x_45);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_47 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_47 = x_3;
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_4);
return x_49;
}
else
{
obj* x_50;
obj* x_52;
x_50 = lean::cnstr_get(x_3, 0);
lean::inc(x_50);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_52 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_52 = x_3;
}
if (lean::obj_tag(x_50) == 0)
{
obj* x_54;
obj* x_57;
lean::dec(x_52);
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
lean::dec(x_50);
x_57 = _l_s2_io_s4_prim_s7_iterate_s6___main_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__6(x_0, x_54, x_4);
return x_57;
}
else
{
obj* x_59;
obj* x_62;
obj* x_63;
lean::dec(x_0);
x_59 = lean::cnstr_get(x_50, 0);
lean::inc(x_59);
lean::dec(x_50);
if (lean::is_scalar(x_52)) {
 x_62 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_62 = x_52;
}
lean::cnstr_set(x_62, 0, x_59);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_4);
return x_63;
}
}
}
}
}
obj* _l_s2_io_s4_prim_s12_iterate__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__5(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_4;
x_2 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_2);
x_4 = _l_s2_io_s4_prim_s7_iterate_s6___main_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__6(x_0, x_2, x_1);
return x_4;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__7_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_7;
obj* x_8;
obj* x_9;
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__7(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s6_handle_s13_read__to__end_s9___spec__7_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s2_fs_s10_read__file_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, unsigned char x_5) {
{
obj* x_6;
unsigned char x_8;
obj* x_13;
obj* x_15;
obj* x_16;
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = 0;
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_13 = _l_s2_io_s2_fs_s6_handle_s2_mk_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__1_s6___rarg(x_0, x_1, x_2, x_3, x_4, x_8, x_5);
lean::inc(x_6);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s2_fs_s10_read__file_s6___rarg_s11___lambda__3), 6, 5);
lean::closure_set(x_15, 0, x_0);
lean::closure_set(x_15, 1, x_1);
lean::closure_set(x_15, 2, x_2);
lean::closure_set(x_15, 3, x_3);
lean::closure_set(x_15, 4, x_6);
x_16 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_13, x_15);
return x_16;
}
}
obj* _l_s2_io_s2_fs_s10_read__file_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, unsigned char x_2) {
{
obj* x_3;
obj* x_6;
obj* x_9;
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_2(x_6, lean::box(0), x_1);
return x_9;
}
}
obj* _l_s2_io_s2_fs_s10_read__file_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
obj* x_8;
obj* x_9;
obj* x_10;
lean::inc(x_3);
x_8 = _l_s2_io_s2_fs_s6_handle_s5_close_s6___rarg(x_0, x_1, x_2, x_3, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s2_fs_s10_read__file_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_6);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* _l_s2_io_s2_fs_s10_read__file_s6___rarg_s11___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_11;
obj* x_13;
obj* x_14;
lean::inc(x_5);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_11 = _l_s2_io_s2_fs_s6_handle_s13_read__to__end_s6___rarg(x_0, x_1, x_2, x_3, x_5);
lean::inc(x_4);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s2_fs_s10_read__file_s6___rarg_s11___lambda__2), 7, 6);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_3);
lean::closure_set(x_13, 4, x_5);
lean::closure_set(x_13, 5, x_4);
x_14 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_11, x_13);
return x_14;
}
}
obj* _l_s2_io_s2_fs_s10_read__file(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s2_fs_s10_read__file_s6___rarg_s7___boxed), 6, 0);
return x_4;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5;
obj* x_7;
obj* x_8;
obj* x_9;
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__2(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__2_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s2_mk_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, unsigned char x_5, unsigned char x_6) {
{
obj* x_7;
obj* x_8;
obj* x_9;
obj* x_10;
x_7 = lean::box(x_5);
x_8 = lean::box(x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s4_prim_s6_handle_s2_mk_s7___boxed), 4, 3);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_7);
lean::closure_set(x_9, 2, x_8);
x_10 = _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__2_s6___rarg(x_0, x_1, x_2, x_3, x_9);
return x_10;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s2_mk_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s2_fs_s6_handle_s2_mk_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__1_s6___rarg_s7___boxed), 7, 0);
return x_4;
}
}
obj* _l_s2_io_s2_fs_s10_read__file_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
unsigned char x_6;
obj* x_7;
x_6 = lean::unbox(x_5);
x_7 = _l_s2_io_s2_fs_s10_read__file_s6___rarg(x_0, x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* _l_s2_io_s2_fs_s10_read__file_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3;
obj* x_4;
x_3 = lean::unbox(x_2);
x_4 = _l_s2_io_s2_fs_s10_read__file_s6___rarg_s11___lambda__1(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s2_io_s2_fs_s6_handle_s2_mk_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__1_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
unsigned char x_7;
unsigned char x_8;
obj* x_9;
x_7 = lean::unbox(x_5);
x_8 = lean::unbox(x_6);
x_9 = _l_s2_io_s2_fs_s6_handle_s2_mk_s4___at_s2_io_s2_fs_s10_read__file_s9___spec__1_s6___rarg(x_0, x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
obj* _l_s9_from__eio(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_3;
obj* x_5;
unsigned char x_6;
obj* x_7;
obj* x_8;
x_2 = lean::apply_1(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_5 = x_2;
}
x_6 = 0;
x_7 = lean::box(x_6);
if (lean::is_scalar(x_5)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_5;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* _l_s2_io_s11_println_x27(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_3;
obj* x_5;
unsigned char x_6;
obj* x_7;
obj* x_8;
x_2 = _l_s2_io_s7_println_s4___at_s2_io_s11_println_x27_s9___spec__1(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_5 = x_2;
}
x_6 = 0;
x_7 = lean::box(x_6);
if (lean::is_scalar(x_5)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_5;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s11_println_x27_s9___spec__4(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_3;
obj* x_5;
obj* x_7;
x_2 = lean::apply_1(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_7 = x_2;
}
if (lean::obj_tag(x_3) == 0)
{
obj* x_8;
obj* x_10;
obj* x_11;
obj* x_12;
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
return x_12;
}
else
{
obj* x_13;
obj* x_15;
obj* x_16;
obj* x_17;
x_13 = lean::cnstr_get(x_3, 0);
lean::inc(x_13);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_15 = x_3;
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
if (lean::is_scalar(x_7)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_7;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_5);
return x_17;
}
}
}
obj* _l_s9___private_3644302523__s8_put__str_s4___at_s2_io_s11_println_x27_s9___spec__3(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_3;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_put_str), 2, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = _l_s2_io_s4_prim_s9_lift__eio_s4___at_s2_io_s11_println_x27_s9___spec__4(x_2, x_1);
return x_3;
}
}
obj* _l_s2_io_s5_print_s4___at_s2_io_s11_println_x27_s9___spec__2(obj* x_0, obj* x_1) {
{
obj* x_2;
x_2 = _l_s9___private_3644302523__s8_put__str_s4___at_s2_io_s11_println_x27_s9___spec__3(x_0, x_1);
return x_2;
}
}
obj* _l_s2_io_s7_println_s4___at_s2_io_s11_println_x27_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_3;
obj* x_5;
obj* x_7;
x_2 = _l_s9___private_3644302523__s8_put__str_s4___at_s2_io_s11_println_x27_s9___spec__3(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_7 = x_2;
}
if (lean::obj_tag(x_3) == 0)
{
obj* x_8;
obj* x_10;
obj* x_11;
obj* x_12;
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
return x_12;
}
else
{
obj* x_15;
obj* x_17;
lean::dec(x_7);
lean::dec(x_3);
x_15 = _l_s2_io_s7_println_s6___rarg_s11___closed__1;
lean::inc(x_15);
x_17 = _l_s9___private_3644302523__s8_put__str_s4___at_s2_io_s11_println_x27_s9___spec__3(x_15, x_5);
return x_17;
}
}
}
obj* _l_s9_has__repr_s9_has__eval_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
obj* x_4;
x_3 = lean::apply_1(x_0, x_1);
x_4 = _l_s2_io_s11_println_x27(x_3, x_2);
return x_4;
}
}
obj* _l_s9_has__repr_s9_has__eval(obj* x_0) {
{
obj* x_2;
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_has__repr_s9_has__eval_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s2_io_s9_has__eval_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
obj* x_4;
obj* x_6;
obj* x_9;
x_3 = lean::apply_1(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_2(x_0, x_4, x_6);
return x_9;
}
}
obj* _l_s2_io_s9_has__eval(obj* x_0) {
{
obj* x_2;
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_io_s9_has__eval_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s8_io__unit_s9_has__eval(obj* x_0, obj* x_1) {
{
obj* x_2;
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* _l_s3_eio_s9_has__eval_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4;
obj* x_5;
obj* x_7;
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_11;
obj* x_14;
obj* x_15;
obj* x_17;
obj* x_19;
lean::dec(x_1);
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
lean::dec(x_5);
x_14 = lean::apply_1(x_0, x_11);
x_15 = _l_s3_eio_s9_has__eval_s6___rarg_s11___closed__1;
lean::inc(x_15);
x_17 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_19 = _l_s2_io_s11_println_x27(x_17, x_7);
return x_19;
}
else
{
obj* x_21;
obj* x_24;
lean::dec(x_0);
x_21 = lean::cnstr_get(x_5, 0);
lean::inc(x_21);
lean::dec(x_5);
x_24 = lean::apply_2(x_1, x_21, x_7);
return x_24;
}
}
}
obj* _init__l_s3_eio_s9_has__eval_s6___rarg_s11___closed__1() {
{
obj* x_0;
x_0 = lean::mk_string("Error: ");
return x_0;
}
}
obj* _l_s3_eio_s9_has__eval(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_eio_s9_has__eval_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s9_eio__unit_s9_has__eval_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
obj* x_4;
obj* x_6;
obj* x_8;
x_3 = lean::apply_1(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_8 = x_3;
}
if (lean::obj_tag(x_4) == 0)
{
obj* x_10;
obj* x_13;
obj* x_14;
obj* x_16;
obj* x_18;
lean::dec(x_8);
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
lean::dec(x_4);
x_13 = lean::apply_1(x_0, x_10);
x_14 = _l_s3_eio_s9_has__eval_s6___rarg_s11___closed__1;
lean::inc(x_14);
x_16 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_18 = _l_s2_io_s11_println_x27(x_16, x_6);
return x_18;
}
else
{
unsigned char x_21;
obj* x_22;
obj* x_23;
lean::dec(x_4);
lean::dec(x_0);
x_21 = 0;
x_22 = lean::box(x_21);
if (lean::is_scalar(x_8)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_8;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_6);
return x_23;
}
}
}
obj* _l_s9_eio__unit_s9_has__eval(obj* x_0) {
{
obj* x_2;
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_eio__unit_s9_has__eval_s6___rarg), 3, 0);
return x_2;
}
}
obj* _init__l_s21_coroutine__result__io() {
{
obj* x_0;
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s13_coroutine__io_s6_mk__st_s6___rarg(obj* x_0) {
{
return x_0;
}
}
obj* _l_s13_coroutine__io_s6_mk__st(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s6_mk__st_s6___rarg), 1, 0);
return x_6;
}
}
obj* _l_s13_coroutine__io_s6_resume_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
x_3 = lean::apply_2(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s13_coroutine__io_s6_resume_s6___main(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s6_resume_s6___main_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s13_coroutine__io_s6_resume_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
x_3 = lean::apply_2(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s13_coroutine__io_s6_resume(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s6_resume_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s13_coroutine__io_s4_pure_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4;
obj* x_5;
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* _l_s13_coroutine__io_s4_pure(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_pure_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s13_coroutine__io_s4_read_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_3;
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* _l_s13_coroutine__io_s4_read(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_read_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s13_coroutine__io_s5_yield_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4;
obj* x_6;
obj* x_7;
lean::dec(x_1);
x_4 = _l_s13_coroutine__io_s5_yield_s6___rarg_s11___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_4);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
}
obj* _init__l_s13_coroutine__io_s5_yield_s6___rarg_s11___closed__1() {
{
obj* x_0;
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s5_yield_s6___rarg_s11___lambda__1), 2, 0);
return x_0;
}
}
obj* _l_s13_coroutine__io_s5_yield_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_3;
obj* x_5;
lean::dec(x_0);
x_3 = _l_s9_coroutine_s5_yield_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* _l_s13_coroutine__io_s5_yield(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s5_yield_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s13_coroutine__io_s4_bind_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5;
obj* x_6;
obj* x_8;
obj* x_10;
lean::inc(x_2);
x_5 = lean::apply_2(x_0, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_12;
obj* x_15;
lean::dec(x_10);
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_15 = lean::apply_3(x_1, x_12, x_2, x_8);
return x_15;
}
else
{
obj* x_17;
obj* x_19;
obj* x_21;
obj* x_22;
obj* x_23;
obj* x_24;
lean::dec(x_2);
x_17 = lean::cnstr_get(x_6, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_6, 1);
lean::inc(x_19);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_21 = x_6;
}
x_22 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_bind_s6___main_s6___rarg), 4, 2);
lean::closure_set(x_22, 0, x_19);
lean::closure_set(x_22, 1, x_1);
if (lean::is_scalar(x_21)) {
 x_23 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_23 = x_21;
}
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_22);
if (lean::is_scalar(x_10)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_10;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_8);
return x_24;
}
}
}
obj* _l_s13_coroutine__io_s4_bind_s6___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_8;
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_bind_s6___main_s6___rarg), 4, 0);
return x_8;
}
}
obj* _l_s13_coroutine__io_s4_bind_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_bind_s6___main_s6___rarg), 4, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s13_coroutine__io_s4_bind(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_8;
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_bind_s6___rarg), 2, 0);
return x_8;
}
}
obj* _l_s13_coroutine__io_s4_pipe_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4;
obj* x_5;
obj* x_7;
obj* x_9;
x_4 = lean::apply_2(x_0, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
}
if (lean::obj_tag(x_5) == 0)
{
obj* x_11;
obj* x_13;
obj* x_14;
obj* x_15;
lean::dec(x_1);
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_13 = x_5;
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_7);
return x_15;
}
else
{
obj* x_16;
obj* x_18;
obj* x_20;
obj* x_21;
obj* x_22;
obj* x_24;
x_16 = lean::cnstr_get(x_5, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_5, 1);
lean::inc(x_18);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_20 = x_5;
}
x_21 = lean::apply_2(x_1, x_16, x_7);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_29;
obj* x_31;
obj* x_32;
obj* x_33;
lean::dec(x_20);
lean::dec(x_18);
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_31 = x_22;
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_9)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_9;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_24);
return x_33;
}
else
{
obj* x_34;
obj* x_36;
obj* x_39;
obj* x_40;
obj* x_41;
x_34 = lean::cnstr_get(x_22, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_22, 1);
lean::inc(x_36);
lean::dec(x_22);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_pipe_s6___main_s6___rarg), 4, 2);
lean::closure_set(x_39, 0, x_18);
lean::closure_set(x_39, 1, x_36);
if (lean::is_scalar(x_20)) {
 x_40 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_40 = x_20;
}
lean::cnstr_set(x_40, 0, x_34);
lean::cnstr_set(x_40, 1, x_39);
if (lean::is_scalar(x_9)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_9;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_24);
return x_41;
}
}
}
}
obj* _l_s13_coroutine__io_s4_pipe_s6___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_8;
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_pipe_s6___main_s6___rarg), 4, 0);
return x_8;
}
}
obj* _l_s13_coroutine__io_s4_pipe_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_pipe_s6___main_s6___rarg), 4, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s13_coroutine__io_s4_pipe(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_8;
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_pipe_s6___rarg), 2, 0);
return x_8;
}
}
obj* _l_s13_coroutine__io_s5_monad(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = _l_s13_coroutine__io_s5_monad_s11___closed__1;
lean::inc(x_4);
return x_4;
}
}
obj* _init__l_s13_coroutine__io_s5_monad_s11___closed__1() {
{
obj* x_0;
obj* x_1;
obj* x_2;
obj* x_3;
obj* x_4;
obj* x_5;
obj* x_6;
obj* x_7;
obj* x_8;
obj* x_9;
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s5_monad_s11___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_pure), 3, 2);
lean::closure_set(x_3, 0, lean::box(0));
lean::closure_set(x_3, 1, lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s5_monad_s11___lambda__4), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s5_monad_s11___lambda__7), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s5_monad_s11___lambda__8), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_bind), 4, 2);
lean::closure_set(x_8, 0, lean::box(0));
lean::closure_set(x_8, 1, lean::box(0));
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_6;
obj* x_8;
obj* x_9;
lean::dec(x_1);
lean::dec(x_0);
x_6 = _l_s13_coroutine__io_s5_monad_s11___lambda__1_s11___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_2);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_bind_s6___main_s6___rarg), 4, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_8);
return x_9;
}
}
obj* _init__l_s13_coroutine__io_s5_monad_s11___lambda__1_s11___closed__1() {
{
obj* x_0;
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_pure_s6___rarg), 3, 0);
return x_0;
}
}
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_6;
obj* x_7;
obj* x_9;
obj* x_10;
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s5_const_s6___rarg), 2, 1);
lean::closure_set(x_6, 0, x_2);
x_7 = _l_s13_coroutine__io_s5_monad_s11___lambda__1_s11___closed__1;
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_bind_s6___main_s6___rarg), 4, 2);
lean::closure_set(x_10, 0, x_3);
lean::closure_set(x_10, 1, x_9);
return x_10;
}
}
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__3(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_4;
obj* x_5;
x_2 = _l_s13_coroutine__io_s5_monad_s11___lambda__1_s11___closed__1;
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_bind_s6___main_s6___rarg), 4, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_4);
return x_5;
}
}
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_6;
obj* x_7;
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s5_monad_s11___lambda__3), 2, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_bind_s6___main_s6___rarg), 4, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_6;
obj* x_7;
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
}
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__6(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_3;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s5_monad_s11___lambda__5), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_bind_s6___main_s6___rarg), 4, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_6;
obj* x_7;
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s5_monad_s11___lambda__6), 2, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_bind_s6___main_s6___rarg), 4, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* _l_s13_coroutine__io_s5_monad_s11___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_6;
obj* x_7;
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg_s11___lambda__8), 2, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s4_bind_s6___main_s6___rarg), 4, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* _l_s13_coroutine__io_s13_monad__reader_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_3;
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* _l_s13_coroutine__io_s13_monad__reader(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s13_monad__reader_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s13_coroutine__io_s16_monad__coroutine(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s5_yield_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s13_coroutine__io_s9_monad__io_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4;
obj* x_5;
obj* x_7;
obj* x_9;
obj* x_10;
obj* x_11;
lean::dec(x_1);
x_4 = lean::apply_1(x_0, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
}
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_5);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_7);
return x_11;
}
}
obj* _l_s13_coroutine__io_s9_monad__io(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_coroutine__io_s9_monad__io_s6___rarg), 3, 0);
return x_6;
}
}
void _l_initialize__l_s4_init_s7_control_s5_state();
void _l_initialize__l_s4_init_s7_control_s6_except();
void _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
void _l_initialize__l_s4_init_s7_control_s9_coroutine();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s2_io() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s7_control_s5_state();
 _l_initialize__l_s4_init_s7_control_s6_except();
 _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
 _l_initialize__l_s4_init_s7_control_s9_coroutine();
 _l_s2_io = _init__l_s2_io();
 _l_s2_io_s5_monad = _init__l_s2_io_s5_monad();
 _l_s9_monad__io = _init__l_s9_monad__io();
 _l_s2_io_s5_error = _init__l_s2_io_s5_error();
 _l_s2_io_s5_error_s15_has__to__string = _init__l_s2_io_s5_error_s15_has__to__string();
 _l_s3_eio = _init__l_s3_eio();
 _l_s2_io_s7_println_s6___rarg_s11___closed__1 = _init__l_s2_io_s7_println_s6___rarg_s11___closed__1();
 _l_s3_eio_s9_has__eval_s6___rarg_s11___closed__1 = _init__l_s3_eio_s9_has__eval_s6___rarg_s11___closed__1();
 _l_s21_coroutine__result__io = _init__l_s21_coroutine__result__io();
 _l_s13_coroutine__io_s5_yield_s6___rarg_s11___closed__1 = _init__l_s13_coroutine__io_s5_yield_s6___rarg_s11___closed__1();
 _l_s13_coroutine__io_s5_monad_s11___closed__1 = _init__l_s13_coroutine__io_s5_monad_s11___closed__1();
 _l_s13_coroutine__io_s5_monad_s11___lambda__1_s11___closed__1 = _init__l_s13_coroutine__io_s5_monad_s11___lambda__1_s11___closed__1();
}
