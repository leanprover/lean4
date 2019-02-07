// Lean compiler output
// Module: init.io
// Imports: init.control.state init.control.except init.data.string.basic init.control.coroutine
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_coroutine__io_resume(obj*, obj*, obj*);
obj* l_coroutine__io_monad___lambda__6(obj*, obj*);
obj* l_io_fs_handle_mk___rarg(obj*, obj*, obj*, obj*, obj*, uint8, uint8);
obj* l_io_fs_handle_is__eof___at_io_fs_handle_read__to__end___spec__1(obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_handle_flush___spec__1(obj*, obj*);
obj* l_io_println___at_io_println_x_27___spec__1(obj*, obj*);
obj* l_from__eio(obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_handle_flush___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_handle_close___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_handle_read__to__end___spec__7(obj*, obj*);
obj* l_io_prim_lift__eio___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_io;
obj* l_coroutine__io_mk__st(obj*, obj*, obj*);
obj* l_coroutine__io_monad___closed__1;
obj* l___private_3511541383__put__str___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_coroutine__io_pipe___main(obj*, obj*, obj*, obj*);
obj* l_io_fs_handle_flush___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_coroutine__io_resume___main(obj*, obj*, obj*);
obj* l_coroutine__io_yield___rarg(obj*, obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_handle_is__eof___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_io_has__eval(obj*);
obj* l_has__repr_has__eval___rarg(obj*, obj*, obj*);
obj* l_coroutine__io_resume___rarg(obj*, obj*, obj*);
obj* l_io_prim_iterate___rarg(obj*, obj*, obj*);
obj* l_id_monad___lambda__1(obj*, obj*, obj*, obj*);
obj* l_io_has__eval___rarg(obj*, obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_handle_read__to__end___spec__7___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate___main___at_io_prim_iterate__eio___spec__1___rarg(obj*, obj*, obj*);
obj* l_io_fs_handle_flush(obj*, obj*);
obj* l_io_prim_lift__eio___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate___main(obj*, obj*);
obj* l_io_prim_handle_mk___boxed(obj*, obj*, obj*, obj*);
obj* l_io_fs_read__file___rarg(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_coroutine__io_pure(obj*, obj*, obj*);
obj* l_io_prim_lift__eio(obj*, obj*, obj*);
obj* l_function_const___rarg(obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_handle_is__eof___spec__1(obj*, obj*);
obj* l_coroutine__io_monad__reader___rarg(obj*, obj*);
obj* l_io_println___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_lift__eio___at_io_println_x_27___spec__4(obj*, obj*);
obj* l_coroutine__io_monad___lambda__8(obj*, obj*, obj*, obj*);
obj* l_coroutine__io_yield(obj*, obj*);
obj* l_coroutine__io_read___rarg(obj*, obj*);
obj* l_io_fs_handle_is__eof___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_eio_has__eval(obj*, obj*);
obj* l_io_print___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_coroutine__io_monad___lambda__4(obj*, obj*, obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l___private_3511541383__put__str___at_io_println___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_monad___rarg___lambda__3(obj*, obj*, obj*);
obj* l_coroutine__io_bind___rarg(obj*, obj*);
obj* l_coroutine__io_mk__st___rarg(obj*);
obj* l_io_prim_iterate___main___at_io_prim_iterate__eio___spec__1(obj*, obj*, obj*);
obj* l_io_fs_read__file___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_io_fs_handle_read__to__end(obj*, obj*);
obj* l_id_bind(obj*, obj*);
obj* l_coroutine__io_monad___lambda__7(obj*, obj*, obj*, obj*);
obj* l_coroutine__io_bind(obj*, obj*, obj*, obj*);
obj* l_io_error_has__to__string;
obj* l_io_prim_lift__eio___at_io_fs_handle_read__to__end___spec__4(obj*, obj*);
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_coroutine__result__io;
obj* l_monad__io;
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1(obj*, obj*);
obj* l_io_prim_iterate(obj*, obj*);
obj* l_io_prim_iterate__eio___rarg(obj*, obj*, obj*);
obj* l_has__repr_has__eval(obj*);
obj* l___private_3511541383__put__str___at_io_println___spec__1(obj*, obj*);
obj* l_id(obj*);
obj* l_io_println___rarg___closed__1;
obj* l_io_print(obj*, obj*);
obj* l_io_fs_handle_is__eof(obj*, obj*);
obj* l_coroutine__io_pipe___main___rarg(obj*, obj*, obj*, obj*);
obj* l_coroutine__io_bind___main___rarg(obj*, obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_coroutine__io_monad__reader(obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_read__file___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_coroutine__io_monad___lambda__1(obj*, obj*, obj*, obj*);
obj* l_io_prim_lift__eio___at_io_println___spec__2(obj*, obj*);
obj* l_io_fs_handle_close___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_coroutine__io_pure___rarg(obj*, obj*, obj*);
obj* l_id_monad___lambda__3(obj*, obj*, obj*, obj*);
obj* l_coroutine__io_yield___rarg___lambda__1(obj*, obj*);
obj* l_io_fs_read__file___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_io_monad;
obj* l_coroutine__io_read(obj*, obj*);
obj* l_string_has__to__string(obj*);
obj* l_state__t_monad___rarg(obj*);
obj* l_coroutine__io_monad__coroutine(obj*, obj*);
obj* l_eio__unit_has__eval(obj*);
obj* l_io_error;
obj* l_eio;
obj* l_io_fs_handle_get__line___at_io_fs_handle_read__to__end___spec__3(obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_handle_is__eof___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_eio_has__eval___rarg(obj*, obj*, obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_read__file___spec__2(obj*, obj*);
obj* l_io_fs_handle_get__line___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_handle_read__to__end___spec__2(obj*, obj*);
obj* l_coroutine__io_monad___lambda__3(obj*, obj*);
obj* l___private_3511541383__put__str(obj*, obj*);
obj* l_eio__unit_has__eval___rarg(obj*, obj*, obj*);
obj* l___private_3511541383__put__str___at_io_println_x_27___spec__3(obj*, obj*);
obj* l_io_fs_read__file(obj*, obj*);
obj* l_coroutine__io_monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_coroutine__io_monad(obj*, obj*);
obj* l_coroutine__io_monad___lambda__5(obj*, obj*, obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_handle_get__line___spec__1(obj*, obj*);
obj* l_coroutine__io_yield___rarg___closed__1;
obj* l_io_prim_lift__eio___at_io_fs_handle_close___spec__1(obj*, obj*);
obj* l_io_prim_lift__eio___at___private_3511541383__put__str___spec__1(obj*, obj*);
obj* l_io_prim_lift__eio___at_io_println___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_io_fs_handle_mk(obj*, obj*);
obj* l_io_println_x_27(obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_handle_mk___spec__1(obj*, obj*);
obj* l_io_fs_handle_read__to__end___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_coroutine__io_bind___main(obj*, obj*, obj*, obj*);
obj* l_coroutine__io_resume___main___rarg(obj*, obj*, obj*);
extern obj* l_coroutine_yield___rarg___lambda__1___closed__1;
obj* l_io_println(obj*, obj*);
obj* l_coroutine__io_monad__io___rarg(obj*, obj*, obj*);
obj* l_io_print___at_io_println_x_27___spec__2(obj*, obj*);
obj* l_io_prim_iterate__eio___at_io_fs_handle_read__to__end___spec__5(obj*, obj*);
obj* l_io_fs_handle_mk___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_id_monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, uint8, uint8);
obj* l_coroutine__io_pipe___rarg(obj*, obj*);
obj* l_io_fs_handle_close(obj*, obj*);
obj* l_coroutine__io_monad___lambda__1___closed__1;
obj* l_io_prim_lift__eio___at___private_3511541383__put__str___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_io__unit_has__eval(obj*, obj*);
obj* l_eio_has__eval___rarg___closed__1;
obj* l_string_has__lift(obj*);
obj* l_io_fs_handle_get__line(obj*, obj*);
obj* l_coroutine__io_monad__io(obj*, obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_handle_get__line___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate___main___at_io_fs_handle_read__to__end___spec__6(obj*, obj*, obj*);
obj* l_io_fs_read__file___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate__eio(obj*, obj*, obj*);
obj* l_coroutine__io_pipe(obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate___main___rarg(obj*, obj*, obj*);
obj* l_io_prim_lift__eio___at_io_fs_handle_mk___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_monad___rarg___lambda__8(obj*, obj*);
obj* _init_l_io_monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_state__t_monad___rarg(x_9);
return x_10;
}
}
obj* _init_l_io() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_monad__io() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_io_error_has__to__string() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_string_has__to__string), 1, 0);
return x_0;
}
}
obj* _init_l_io_error() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_string_has__lift(obj* x_0) {
_start:
{
return x_0;
}
}
obj* _init_l_eio() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_io_prim_iterate___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
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
lean::dec(x_9);
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
lean::dec(x_5);
x_0 = x_11;
x_2 = x_7;
goto _start;
}
else
{
obj* x_16; obj* x_19; 
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
obj* l_io_prim_iterate___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___rarg), 3, 0);
return x_4;
}
}
obj* l_io_prim_iterate___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_io_prim_iterate(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___rarg), 3, 0);
return x_4;
}
}
obj* l_io_prim_iterate___main___at_io_prim_iterate__eio___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
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
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
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
obj* x_16; obj* x_18; 
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
lean::dec(x_9);
lean::dec(x_18);
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
lean::dec(x_16);
x_1 = x_21;
x_2 = x_7;
goto _start;
}
else
{
obj* x_26; obj* x_29; obj* x_30; 
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
obj* l_io_prim_iterate___main___at_io_prim_iterate__eio___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___at_io_prim_iterate__eio___spec__1___rarg), 3, 0);
return x_6;
}
}
obj* l_io_prim_iterate__eio___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate___main___at_io_prim_iterate__eio___spec__1___rarg(x_1, x_0, x_2);
return x_3;
}
}
obj* l_io_prim_iterate__eio(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__eio___rarg), 3, 0);
return x_6;
}
}
obj* l_io_prim_handle_mk___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox(x_1);
x_5 = lean::unbox(x_2);
x_6 = lean::io_prim_handle_mk(x_0, x_4, x_5, x_3);
return x_6;
}
}
obj* l_io_prim_lift__eio___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_io_prim_lift__eio___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
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
obj* x_15; obj* x_18; obj* x_21; obj* x_24; 
lean::dec(x_1);
lean::dec(x_0);
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
obj* l_io_prim_lift__eio(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg), 5, 0);
return x_6;
}
}
obj* l_io_prim_lift__eio___at___private_3511541383__put__str___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_io_prim_lift__eio___at___private_3511541383__put__str___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___at___private_3511541383__put__str___spec__1___rarg), 5, 0);
return x_4;
}
}
obj* l___private_3511541383__put__str___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_put_str), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = l_io_prim_lift__eio___at___private_3511541383__put__str___spec__1___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l___private_3511541383__put__str(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3511541383__put__str___rarg), 5, 0);
return x_4;
}
}
obj* l_io_print___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_9; 
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_6);
x_9 = l___private_3511541383__put__str___rarg(x_0, x_1, x_2, x_3, x_8);
return x_9;
}
}
obj* l_io_print(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_print___rarg), 7, 0);
return x_4;
}
}
obj* l_io_prim_lift__eio___at_io_println___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_io_prim_lift__eio___at_io_println___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___at_io_println___spec__2___rarg), 5, 0);
return x_4;
}
}
obj* l___private_3511541383__put__str___at_io_println___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_put_str), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = l_io_prim_lift__eio___at_io_println___spec__2___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l___private_3511541383__put__str___at_io_println___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3511541383__put__str___at_io_println___spec__1___rarg), 5, 0);
return x_4;
}
}
obj* l_io_println___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_10; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
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
x_17 = l_io_print___rarg(x_0, x_1, x_2, x_3, lean::box(0), x_5, x_6);
x_18 = l_io_println___rarg___closed__1;
lean::inc(x_18);
x_20 = l___private_3511541383__put__str___at_io_println___spec__1___rarg(x_0, x_1, x_2, x_3, x_18);
x_21 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_17, x_20);
return x_21;
}
}
obj* _init_l_io_println___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\n");
return x_0;
}
}
obj* l_io_println(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_println___rarg), 7, 0);
return x_4;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_mk___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_mk___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___at_io_fs_handle_mk___spec__1___rarg), 5, 0);
return x_4;
}
}
obj* l_io_fs_handle_mk___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5, uint8 x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::box(x_5);
x_8 = lean::box(x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_handle_mk___boxed), 4, 3);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_7);
lean::closure_set(x_9, 2, x_8);
x_10 = l_io_prim_lift__eio___at_io_fs_handle_mk___spec__1___rarg(x_0, x_1, x_2, x_3, x_9);
return x_10;
}
}
obj* l_io_fs_handle_mk(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_mk___rarg___boxed), 7, 0);
return x_4;
}
}
obj* l_io_fs_handle_mk___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; uint8 x_8; obj* x_9; 
x_7 = lean::unbox(x_5);
x_8 = lean::unbox(x_6);
x_9 = l_io_fs_handle_mk___rarg(x_0, x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_is__eof___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___at_io_fs_handle_is__eof___spec__1___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_is__eof___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
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
obj* x_15; obj* x_18; obj* x_21; obj* x_24; 
lean::dec(x_1);
lean::dec(x_0);
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
obj* l_io_prim_lift__eio___at_io_fs_handle_is__eof___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___at_io_fs_handle_is__eof___spec__1___rarg), 5, 0);
return x_4;
}
}
obj* l_io_fs_handle_is__eof___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_handle_is_eof), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = l_io_prim_lift__eio___at_io_fs_handle_is__eof___spec__1___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_io_fs_handle_is__eof(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_is__eof___rarg), 5, 0);
return x_4;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_flush___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_flush___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___at_io_fs_handle_flush___spec__1___rarg), 5, 0);
return x_4;
}
}
obj* l_io_fs_handle_flush___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_handle_flush), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = l_io_prim_lift__eio___at_io_fs_handle_flush___spec__1___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_io_fs_handle_flush(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_flush___rarg), 5, 0);
return x_4;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_close___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_close___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___at_io_fs_handle_close___spec__1___rarg), 5, 0);
return x_4;
}
}
obj* l_io_fs_handle_close___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_handle_flush), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = l_io_prim_lift__eio___at_io_fs_handle_close___spec__1___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_io_fs_handle_close(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_close___rarg), 5, 0);
return x_4;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_get__line___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_get__line___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___at_io_fs_handle_get__line___spec__1___rarg), 5, 0);
return x_4;
}
}
obj* l_io_fs_handle_get__line___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_handle_get_line), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = l_io_prim_lift__eio___at_io_fs_handle_get__line___spec__1___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_io_fs_handle_get__line(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_get__line___rarg), 5, 0);
return x_4;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_read__to__end___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_7; 
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
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
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
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
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
obj* l_io_fs_handle_is__eof___at_io_fs_handle_read__to__end___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_handle_is_eof), 2, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = l_io_prim_lift__eio___at_io_fs_handle_read__to__end___spec__2(x_2, x_1);
return x_3;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_read__to__end___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_7; 
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
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
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
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
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
obj* l_io_fs_handle_get__line___at_io_fs_handle_read__to__end___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_handle_get_line), 2, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = l_io_prim_lift__eio___at_io_fs_handle_read__to__end___spec__4(x_2, x_1);
return x_3;
}
}
obj* l_io_prim_iterate___main___at_io_fs_handle_read__to__end___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; 
lean::inc(x_0);
x_7 = l_io_fs_handle_is__eof___at_io_fs_handle_read__to__end___spec__1(x_0, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
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
obj* x_18; obj* x_20; uint8 x_21; 
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
obj* x_24; obj* x_25; obj* x_27; 
lean::inc(x_0);
x_24 = l_io_fs_handle_get__line___at_io_fs_handle_read__to__end___spec__3(x_0, x_10);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_31; obj* x_34; 
lean::dec(x_1);
x_31 = lean::cnstr_get(x_25, 0);
lean::inc(x_31);
lean::dec(x_25);
if (lean::is_scalar(x_20)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_20;
 lean::cnstr_set_tag(x_20, 0);
}
lean::cnstr_set(x_34, 0, x_31);
x_3 = x_34;
x_4 = x_27;
goto lbl_5;
}
else
{
obj* x_35; obj* x_38; obj* x_40; obj* x_41; 
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
obj* x_42; obj* x_43; 
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
obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
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
obj* x_50; obj* x_52; 
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
lean::dec(x_52);
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
lean::dec(x_50);
x_1 = x_54;
x_2 = x_4;
goto _start;
}
else
{
obj* x_59; obj* x_62; obj* x_63; 
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
obj* l_io_prim_iterate__eio___at_io_fs_handle_read__to__end___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = l_io_prim_iterate___main___at_io_fs_handle_read__to__end___spec__6(x_0, x_2, x_1);
return x_4;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_read__to__end___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_io_prim_lift__eio___at_io_fs_handle_read__to__end___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___at_io_fs_handle_read__to__end___spec__7___rarg), 5, 0);
return x_4;
}
}
obj* l_io_fs_handle_read__to__end___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__eio___at_io_fs_handle_read__to__end___spec__5), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = l_io_prim_lift__eio___at_io_fs_handle_read__to__end___spec__7___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_io_fs_handle_read__to__end(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_read__to__end___rarg), 5, 0);
return x_4;
}
}
obj* l_io_prim_lift__eio___at_io_fs_read__file___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_io_prim_lift__eio___at_io_fs_read__file___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___at_io_fs_read__file___spec__2___rarg), 5, 0);
return x_4;
}
}
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5, uint8 x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::box(x_5);
x_8 = lean::box(x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_handle_mk___boxed), 4, 3);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_7);
lean::closure_set(x_9, 2, x_8);
x_10 = l_io_prim_lift__eio___at_io_fs_read__file___spec__2___rarg(x_0, x_1, x_2, x_3, x_9);
return x_10;
}
}
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg___boxed), 7, 0);
return x_4;
}
}
obj* l_io_fs_read__file___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_6; uint8 x_8; obj* x_13; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = 0;
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_13 = l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_8, x_5);
lean::inc(x_6);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_read__file___rarg___lambda__2), 6, 5);
lean::closure_set(x_15, 0, x_0);
lean::closure_set(x_15, 1, x_1);
lean::closure_set(x_15, 2, x_2);
lean::closure_set(x_15, 3, x_3);
lean::closure_set(x_15, 4, x_6);
x_16 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_13, x_15);
return x_16;
}
}
obj* l_io_fs_read__file___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_3);
x_8 = l_io_fs_handle_close___rarg(x_0, x_1, x_2, x_3, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad___rarg___lambda__3), 3, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_6);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_io_fs_read__file___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_11; obj* x_13; obj* x_14; 
lean::inc(x_5);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_11 = l_io_fs_handle_read__to__end___rarg(x_0, x_1, x_2, x_3, x_5);
lean::inc(x_4);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_read__file___rarg___lambda__1), 7, 6);
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
obj* l_io_fs_read__file(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_read__file___rarg___boxed), 6, 0);
return x_4;
}
}
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; uint8 x_8; obj* x_9; 
x_7 = lean::unbox(x_5);
x_8 = lean::unbox(x_6);
x_9 = l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
obj* l_io_fs_read__file___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_io_fs_read__file___rarg(x_0, x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_from__eio(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
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
x_6 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_5;
}
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
}
obj* l_io_prim_lift__eio___at_io_println_x_27___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_7; 
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
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
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
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
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
obj* l___private_3511541383__put__str___at_io_println_x_27___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_put_str), 2, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = l_io_prim_lift__eio___at_io_println_x_27___spec__4(x_2, x_1);
return x_3;
}
}
obj* l_io_print___at_io_println_x_27___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_3511541383__put__str___at_io_println_x_27___spec__3(x_0, x_1);
return x_2;
}
}
obj* l_io_println___at_io_println_x_27___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_7; 
x_2 = l___private_3511541383__put__str___at_io_println_x_27___spec__3(x_0, x_1);
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
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
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
obj* x_15; obj* x_17; 
lean::dec(x_7);
lean::dec(x_3);
x_15 = l_io_println___rarg___closed__1;
lean::inc(x_15);
x_17 = l___private_3511541383__put__str___at_io_println_x_27___spec__3(x_15, x_5);
return x_17;
}
}
}
obj* l_io_println_x_27(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_2 = l_io_println___at_io_println_x_27___spec__1(x_0, x_1);
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
x_6 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_5;
}
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
}
obj* l_has__repr_has__eval___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_0, x_1);
x_4 = l_io_println_x_27(x_3, x_2);
return x_4;
}
}
obj* l_has__repr_has__eval(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_has__repr_has__eval___rarg), 3, 0);
return x_2;
}
}
obj* l_io_has__eval___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_9; 
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
obj* l_io_has__eval(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_has__eval___rarg), 3, 0);
return x_2;
}
}
obj* l_io__unit_has__eval(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_eio_has__eval___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; 
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_11; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
lean::dec(x_1);
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
lean::dec(x_5);
x_14 = lean::apply_1(x_0, x_11);
x_15 = l_eio_has__eval___rarg___closed__1;
lean::inc(x_15);
x_17 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_19 = l_io_println_x_27(x_17, x_7);
return x_19;
}
else
{
obj* x_21; obj* x_24; 
lean::dec(x_0);
x_21 = lean::cnstr_get(x_5, 0);
lean::inc(x_21);
lean::dec(x_5);
x_24 = lean::apply_2(x_1, x_21, x_7);
return x_24;
}
}
}
obj* _init_l_eio_has__eval___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("Error: ");
return x_0;
}
}
obj* l_eio_has__eval(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_eio_has__eval___rarg), 4, 0);
return x_4;
}
}
obj* l_eio__unit_has__eval___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; 
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
obj* x_10; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
lean::dec(x_8);
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
lean::dec(x_4);
x_13 = lean::apply_1(x_0, x_10);
x_14 = l_eio_has__eval___rarg___closed__1;
lean::inc(x_14);
x_16 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_18 = l_io_println_x_27(x_16, x_6);
return x_18;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_4);
lean::dec(x_0);
x_21 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_8;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_6);
return x_22;
}
}
}
obj* l_eio__unit_has__eval(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_eio__unit_has__eval___rarg), 3, 0);
return x_2;
}
}
obj* _init_l_coroutine__result__io() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_coroutine__io_mk__st___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_coroutine__io_mk__st(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_mk__st___rarg), 1, 0);
return x_6;
}
}
obj* l_coroutine__io_resume___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_0, x_1, x_2);
return x_3;
}
}
obj* l_coroutine__io_resume___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_resume___main___rarg), 3, 0);
return x_6;
}
}
obj* l_coroutine__io_resume___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_0, x_1, x_2);
return x_3;
}
}
obj* l_coroutine__io_resume(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_resume___rarg), 3, 0);
return x_6;
}
}
obj* l_coroutine__io_pure___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* l_coroutine__io_pure(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_pure___rarg), 3, 0);
return x_6;
}
}
obj* l_coroutine__io_read___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_coroutine__io_read(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_read___rarg), 2, 0);
return x_4;
}
}
obj* l_coroutine__io_yield___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_4 = l_coroutine__io_yield___rarg___closed__1;
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
obj* _init_l_coroutine__io_yield___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_yield___rarg___lambda__1), 2, 0);
return x_0;
}
}
obj* l_coroutine__io_yield___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_5; 
lean::dec(x_0);
x_3 = l_coroutine_yield___rarg___lambda__1___closed__1;
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_coroutine__io_yield(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_yield___rarg), 3, 0);
return x_4;
}
}
obj* l_coroutine__io_bind___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
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
obj* x_12; obj* x_15; 
lean::dec(x_10);
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_15 = lean::apply_3(x_1, x_12, x_2, x_8);
return x_15;
}
else
{
obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
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
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_bind___main___rarg), 4, 2);
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
obj* l_coroutine__io_bind___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_bind___main___rarg), 4, 0);
return x_8;
}
}
obj* l_coroutine__io_bind___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_bind___main___rarg), 4, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_coroutine__io_bind(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_bind___rarg), 2, 0);
return x_8;
}
}
obj* l_coroutine__io_pipe___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
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
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
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
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_24; 
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
obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_18);
lean::dec(x_20);
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
obj* x_34; obj* x_36; obj* x_39; obj* x_40; obj* x_41; 
x_34 = lean::cnstr_get(x_22, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_22, 1);
lean::inc(x_36);
lean::dec(x_22);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_pipe___main___rarg), 4, 2);
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
obj* l_coroutine__io_pipe___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_pipe___main___rarg), 4, 0);
return x_8;
}
}
obj* l_coroutine__io_pipe___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_pipe___main___rarg), 4, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_coroutine__io_pipe(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_pipe___rarg), 2, 0);
return x_8;
}
}
obj* l_coroutine__io_monad(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = l_coroutine__io_monad___closed__1;
lean::inc(x_4);
return x_4;
}
}
obj* _init_l_coroutine__io_monad___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_monad___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_pure), 3, 2);
lean::closure_set(x_3, 0, lean::box(0));
lean::closure_set(x_3, 1, lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_monad___lambda__4), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_monad___lambda__7), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_monad___lambda__8), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_bind), 4, 2);
lean::closure_set(x_8, 0, lean::box(0));
lean::closure_set(x_8, 1, lean::box(0));
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_coroutine__io_monad___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_coroutine__io_monad___lambda__1___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_2);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_bind___main___rarg), 4, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_8);
return x_9;
}
}
obj* _init_l_coroutine__io_monad___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_pure___rarg), 3, 0);
return x_0;
}
}
obj* l_coroutine__io_monad___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_function_const___rarg), 2, 1);
lean::closure_set(x_6, 0, x_2);
x_7 = l_coroutine__io_monad___lambda__1___closed__1;
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_bind___main___rarg), 4, 2);
lean::closure_set(x_10, 0, x_3);
lean::closure_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_coroutine__io_monad___lambda__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; 
x_2 = l_coroutine__io_monad___lambda__1___closed__1;
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_bind___main___rarg), 4, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_coroutine__io_monad___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_monad___lambda__3), 2, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_bind___main___rarg), 4, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_coroutine__io_monad___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
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
obj* l_coroutine__io_monad___lambda__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_monad___lambda__5), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_bind___main___rarg), 4, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_coroutine__io_monad___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_monad___lambda__6), 2, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_bind___main___rarg), 4, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_coroutine__io_monad___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__8), 2, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_bind___main___rarg), 4, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_coroutine__io_monad__reader___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_coroutine__io_monad__reader(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_monad__reader___rarg), 2, 0);
return x_4;
}
}
obj* l_coroutine__io_monad__coroutine(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_yield___rarg), 3, 0);
return x_4;
}
}
obj* l_coroutine__io_monad__io___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
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
obj* l_coroutine__io_monad__io(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine__io_monad__io___rarg), 3, 0);
return x_6;
}
}
void initialize_init_control_state();
void initialize_init_control_except();
void initialize_init_data_string_basic();
void initialize_init_control_coroutine();
static bool _G_initialized = false;
void initialize_init_io() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_control_state();
 initialize_init_control_except();
 initialize_init_data_string_basic();
 initialize_init_control_coroutine();
 l_io_monad = _init_l_io_monad();
 l_io = _init_l_io();
 l_monad__io = _init_l_monad__io();
 l_io_error_has__to__string = _init_l_io_error_has__to__string();
 l_io_error = _init_l_io_error();
 l_eio = _init_l_eio();
 l_io_println___rarg___closed__1 = _init_l_io_println___rarg___closed__1();
 l_eio_has__eval___rarg___closed__1 = _init_l_eio_has__eval___rarg___closed__1();
 l_coroutine__result__io = _init_l_coroutine__result__io();
 l_coroutine__io_yield___rarg___closed__1 = _init_l_coroutine__io_yield___rarg___closed__1();
 l_coroutine__io_monad___closed__1 = _init_l_coroutine__io_monad___closed__1();
 l_coroutine__io_monad___lambda__1___closed__1 = _init_l_coroutine__io_monad___lambda__1___closed__1();
}
