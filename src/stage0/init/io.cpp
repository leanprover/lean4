// Lean compiler output
// Module: init.io
// Imports: init.control.estate init.data.string.basic
#include "runtime/object.h"
#include "runtime/apply.h"
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
obj* l_IO_Prim_handle_mk___boxed(obj*, obj*, obj*, obj*);
extern "C" obj* lean_io_prim_handle_get_line(obj*, obj*);
obj* l_IO_println(obj*);
obj* l_IO_Ref_set___boxed(obj*, obj*);
obj* l_IO_Fs_handle_isEof___at_IO_Fs_handle_readToEnd___spec__1___boxed(obj*, obj*);
obj* l_ioOfExcept___rarg(obj*, obj*, obj*);
obj* l_IO_Ref_get___rarg(obj*, obj*, obj*);
obj* l_EState_Monad(obj*, obj*);
obj* l_IO_Ref_swap___boxed(obj*, obj*);
obj* l_IO_HasEval(obj*);
obj* l_IO_Ref_modify(obj*);
obj* l_IO_Fs_handle_isEof___rarg(obj*, obj*);
obj* l_getModify___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_IO_Fs_handle_close___rarg(obj*, obj*);
obj* l_IO_Ref_swap(obj*, obj*);
obj* l_IO_RefPointed___boxed(obj*);
obj* l_EIO_Inhabited___rarg(obj*);
obj* l_HasRepr_HasEval___rarg(obj*, obj*, obj*);
obj* l_IO_Prim_Ref_swap___boxed(obj*, obj*, obj*, obj*);
obj* l_IO_error_Inhabited;
obj* l_IO_Fs_handle_mk(obj*, obj*);
extern "C" obj* lean_io_prim_handle_is_eof(obj*, obj*);
obj* l_IO_println___at_HasRepr_HasEval___spec__1___boxed(obj*, obj*);
obj* l_IO_Prim_iterate___main___at_IO_Fs_handle_readToEnd___spec__4___boxed(obj*, obj*, obj*);
obj* l_IO_Fs_handle_getLine(obj*, obj*);
obj* l_IO_print___boxed(obj*, obj*);
obj* l_IO_print___at_HasRepr_HasEval___spec__2___boxed(obj*, obj*);
obj* l_IO_Prim_iterate___at_IO_Fs_handle_readToEnd___spec__3___boxed(obj*, obj*, obj*);
obj* l_IO_Ref_reset___rarg(obj*, obj*, obj*);
obj* l_EIO_Inhabited(obj*, obj*);
obj* l_unsafeIO(obj*);
obj* l_IO_Prim_iterate___at_IO_Fs_handle_readToEnd___spec__3(obj*, obj*, obj*);
obj* l_EIO_Monad(obj*);
obj* l_IO_HasEval___boxed(obj*);
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
obj* l_IO_Ref_modify___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_IO_Ref_modify___boxed(obj*);
obj* l_IO_Prim_putStr___boxed(obj*, obj*);
obj* l_IO_print___at_HasRepr_HasEval___spec__2(obj*, obj*);
obj* l_ioOfExcept___boxed(obj*, obj*);
extern obj* l_String_Inhabited;
obj* l_allocprof___boxed(obj*, obj*, obj*, obj*);
obj* l_EIO_MonadExcept(obj*);
extern "C" obj* lean_io_initializing(obj*);
obj* l_IO_print___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_EIO_MonadExcept___closed__1;
obj* l_IO_userError(obj*);
obj* l_IO_Ref_swap___rarg(obj*, obj*, obj*, obj*);
obj* l_IO_Fs_handle_flush(obj*, obj*);
obj* l_IO_Prim_Ref_get___boxed(obj*, obj*, obj*);
obj* l_EIO_Monad___boxed(obj*);
extern "C" obj* lean_io_prim_get_line(obj*);
extern "C" obj* lean_io_allocprof(obj*, obj*, obj*, obj*);
obj* l_IO_Prim_iterate___boxed(obj*, obj*);
obj* l_IO_Ref_set___rarg(obj*, obj*, obj*, obj*);
obj* l_IO_print___rarg(obj*, obj*, obj*, obj*);
obj* l_IO_userError___boxed(obj*);
obj* l_IO_Prim_getLine___boxed(obj*);
obj* l_IO_Prim_handle_isEof___boxed(obj*, obj*);
obj* l_IO_Ref_set___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_IO_Ref_get(obj*, obj*);
obj* l_IO_Prim_liftIO___boxed(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_IO_Ref_modify___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_IO_Ref_set(obj*, obj*);
obj* l_IO_Ref_reset(obj*, obj*);
obj* l_IO_mkRef___rarg___boxed(obj*, obj*, obj*);
obj* l_IO_mkRef___rarg(obj*, obj*, obj*);
obj* l_IO_Fs_handle_mk___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_IO_Prim_iterate(obj*, obj*);
obj* l_IO_Fs_readFile___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l_unsafeIO___boxed(obj*);
obj* l_String_HasToString___boxed(obj*);
obj* l_IO_Prim_liftIO(obj*, obj*);
obj* l_IO_Inhabited(obj*);
obj* l_IO_Ref_modify___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_IO_Prim_handle_close___boxed(obj*, obj*);
obj* l_IO_error_HasToString;
obj* l_IO_Prim_handle_flush___boxed(obj*, obj*);
obj* l_IO_Prim_iterate___main___boxed(obj*, obj*);
obj* l_IO_Ref_get___rarg___boxed(obj*, obj*, obj*);
obj* l_IO_println___boxed(obj*);
obj* l_HasRepr_HasEval___boxed(obj*);
obj* l_ioOfExcept(obj*, obj*);
obj* l_IO_Fs_handle_flush___boxed(obj*, obj*);
extern "C" obj* lean_io_prim_handle_close(obj*, obj*);
obj* l_unsafeIO___rarg___closed__1;
obj* l_IO_Ref_modify___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_IO_Inhabited___boxed(obj*);
obj* l_IO_mkRef(obj*, obj*);
obj* l_IO_Fs_readFile___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_IO_Fs_readFile___rarg(obj*, obj*, obj*, uint8);
obj* l_IO_Fs_handle_mk___boxed(obj*, obj*);
obj* l_IO_mkRef___boxed(obj*, obj*);
obj* l_EIO_Inhabited___boxed(obj*, obj*);
obj* l_IO_Fs_readFile___boxed(obj*);
obj* l_IO_Ref_get___boxed(obj*, obj*);
obj* l_IO_Fs_handle_getLine___at_IO_Fs_handle_readToEnd___spec__2(obj*, obj*);
obj* l_IO_println___at_HasRepr_HasEval___spec__1(obj*, obj*);
obj* l_IO_HasEval___rarg(obj*, obj*, obj*);
obj* l_IO_Fs_handle_readToEnd(obj*, obj*);
obj* l_IO_println___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_IO_Fs_handle_getLine___at_IO_Fs_handle_readToEnd___spec__2___boxed(obj*, obj*);
obj* l_IO_Fs_handle_getLine___boxed(obj*, obj*);
extern "C" obj* lean_io_prim_handle_flush(obj*, obj*);
obj* l___private_init_io_1__putStr(obj*, obj*);
obj* l_IO_print(obj*, obj*);
obj* l_IO_Fs_handle_getLine___rarg(obj*, obj*);
obj* l_IO_Prim_handle_getLine___boxed(obj*, obj*);
obj* l_IO_lazyPure(obj*);
obj* l_IO_Prim_Ref_set___boxed(obj*, obj*, obj*, obj*);
obj* l_IO_Ref_swap___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_EIO_MonadExcept___boxed(obj*);
obj* l_IO_initializing___boxed(obj*);
obj* l_IO_Fs_handle_close___boxed(obj*, obj*);
obj* l_IO_Ref_reset___rarg___boxed(obj*, obj*, obj*);
obj* l_IOUnit_HasEval(obj*, obj*);
obj* l_EIO_Monad___closed__1;
obj* l_IO_Fs_handle_readToEnd___boxed(obj*, obj*);
obj* l_IO_Prim_Ref_reset___boxed(obj*, obj*, obj*);
obj* l_IO_Fs_handle_isEof(obj*, obj*);
obj* l_IO_Prim_iterate___rarg(obj*, obj*, obj*);
obj* l_IO_Ref_reset___boxed(obj*, obj*);
obj* l_IO_Fs_readFile___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_IO_Fs_handle_readToEnd___rarg(obj*, obj*);
obj* l_HasRepr_HasEval(obj*);
obj* l_EState_MonadExcept(obj*, obj*);
obj* l_timeit___boxed(obj*, obj*, obj*, obj*);
obj* l_IO_Fs_handle_isEof___boxed(obj*, obj*);
obj* l_IO_Prim_iterate___main(obj*, obj*);
obj* l_unsafeIO___rarg(obj*);
obj* l_IO_Prim_iterate___main___at_IO_Fs_handle_readToEnd___spec__4(obj*, obj*, obj*);
obj* l_IO_Fs_handle_flush___rarg(obj*, obj*);
extern "C" obj* lean_io_timeit(obj*, obj*, obj*, obj*);
obj* l_IO_Prim_iterate___main___rarg(obj*, obj*, obj*);
extern "C" obj* lean_io_prim_handle_mk(obj*, uint8, uint8, obj*);
obj* l_IO_lazyPure___boxed(obj*);
obj* l_IO_Fs_handle_isEof___at_IO_Fs_handle_readToEnd___spec__1(obj*, obj*);
obj* l_IO_Fs_handle_close(obj*, obj*);
obj* l_IO_Fs_handle_mk___rarg(obj*, obj*, uint8, uint8);
obj* l_IO_Prim_liftIO___rarg(obj*, obj*);
obj* l_IO_RefPointed(obj*);
obj* l_IO_println___rarg___closed__1;
obj* l_IO_Prim_mkRef___boxed(obj*, obj*, obj*);
obj* l_IO_lazyPure___rarg(obj*, obj*);
obj* l_IO_Fs_readFile(obj*);
obj* l_EState_Inhabited___rarg(obj*, obj*);
obj* l___private_init_io_1__putStr___boxed(obj*, obj*);
obj* l___private_init_io_1__putStr___at_HasRepr_HasEval___spec__3(obj*, obj*);
obj* l___private_init_io_1__putStr___at_HasRepr_HasEval___spec__3___boxed(obj*, obj*);
obj* l_IO_println___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_io_1__putStr___rarg(obj*, obj*);
obj* l_IO_Ref_modify___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* _init_l_EIO_Monad___closed__1() {
_start:
{
obj* x_0; 
x_0 = l_EState_Monad(lean::box(0), lean::box(0));
return x_0;
}
}
obj* l_EIO_Monad(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_EIO_Monad___closed__1;
return x_1;
}
}
obj* l_EIO_Monad___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_EIO_Monad(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_EIO_MonadExcept___closed__1() {
_start:
{
obj* x_0; 
x_0 = l_EState_MonadExcept(lean::box(0), lean::box(0));
return x_0;
}
}
obj* l_EIO_MonadExcept(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_EIO_MonadExcept___closed__1;
return x_1;
}
}
obj* l_EIO_MonadExcept___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_EIO_MonadExcept(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_EIO_Inhabited___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_Inhabited___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_EIO_Inhabited(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_EIO_Inhabited___rarg), 1, 0);
return x_2;
}
}
obj* l_EIO_Inhabited___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_EIO_Inhabited(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_IO_error_HasToString() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_String_HasToString___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_IO_error_Inhabited() {
_start:
{
obj* x_0; 
x_0 = l_String_Inhabited;
return x_0;
}
}
obj* l_IO_userError(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_IO_userError___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_IO_userError(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_unsafeIO___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1, 0, x_0);
lean::cnstr_set(x_1, 1, x_0);
return x_1;
}
}
obj* l_unsafeIO___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_unsafeIO___rarg___closed__1;
x_2 = lean::apply_1(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::box(0);
return x_8;
}
}
}
obj* l_unsafeIO(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_unsafeIO___rarg), 1, 0);
return x_1;
}
}
obj* l_unsafeIO___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_unsafeIO(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_timeit___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_io_timeit(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_allocprof___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_io_allocprof(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_IO_initializing___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean_io_initializing(x_0);
return x_1;
}
}
obj* l_ioOfExcept___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_8 = x_2;
} else {
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = lean::apply_1(x_0, x_3);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_8;
 lean::cnstr_set_tag(x_8, 1);
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
else
{
obj* x_12; obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_0);
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_17 = x_2;
} else {
 lean::inc(x_15);
 lean::dec(x_2);
 x_17 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_12);
lean::cnstr_set(x_18, 1, x_15);
return x_18;
}
}
}
obj* l_ioOfExcept(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ioOfExcept___rarg), 3, 0);
return x_2;
}
}
obj* l_ioOfExcept___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ioOfExcept(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_lazyPure___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
x_5 = lean::box(0);
x_6 = lean::apply_1(x_0, x_5);
if (lean::is_scalar(x_4)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_4;
}
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
}
obj* l_IO_lazyPure(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_lazyPure___rarg), 2, 0);
return x_1;
}
}
obj* l_IO_lazyPure___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_IO_lazyPure(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_IO_Prim_iterate___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = lean::apply_2(x_1, x_0, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
x_0 = x_10;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; obj* x_19; obj* x_20; obj* x_23; 
lean::dec(x_1);
x_17 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_19 = x_4;
} else {
 lean::inc(x_17);
 lean::dec(x_4);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_5, 0);
lean::inc(x_20);
lean::dec(x_5);
if (lean::is_scalar(x_19)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_19;
}
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_17);
return x_23;
}
}
else
{
obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_1);
x_25 = lean::cnstr_get(x_4, 0);
x_27 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_29 = x_4;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_4);
 x_29 = lean::box(0);
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_25);
lean::cnstr_set(x_30, 1, x_27);
return x_30;
}
}
}
obj* l_IO_Prim_iterate___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___rarg), 3, 0);
return x_2;
}
}
obj* l_IO_Prim_iterate___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Prim_iterate___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_Prim_iterate___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_Prim_iterate___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_IO_Prim_iterate(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___rarg), 3, 0);
return x_2;
}
}
obj* l_IO_Prim_iterate___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Prim_iterate(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_Prim_putStr___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_put_str(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_IO_Prim_getLine___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean_io_prim_get_line(x_0);
return x_1;
}
}
obj* l_IO_Prim_handle_mk___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox(x_1);
x_5 = lean::unbox(x_2);
x_6 = lean_io_prim_handle_mk(x_0, x_4, x_5, x_3);
lean::dec(x_0);
return x_6;
}
}
obj* l_IO_Prim_handle_isEof___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_handle_is_eof(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_IO_Prim_handle_flush___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_handle_flush(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_IO_Prim_handle_close___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_handle_close(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_IO_Prim_handle_getLine___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_handle_get_line(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_IO_Prim_liftIO___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_IO_Prim_liftIO(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_liftIO___rarg), 2, 0);
return x_2;
}
}
obj* l_IO_Prim_liftIO___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Prim_liftIO(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_io_1__putStr___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_putStr___boxed), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_2);
return x_3;
}
}
obj* l___private_init_io_1__putStr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_io_1__putStr___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_io_1__putStr___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_io_1__putStr(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_print___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_2, x_3);
x_5 = l___private_init_io_1__putStr___rarg(x_0, x_4);
return x_5;
}
}
obj* l_IO_print(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_print___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_IO_print___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_IO_print___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_IO_print___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_print(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_IO_println___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\n");
return x_0;
}
}
obj* l_IO_println___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 4);
lean::inc(x_8);
lean::dec(x_5);
lean::inc(x_1);
x_12 = l_IO_print___rarg(x_1, lean::box(0), x_3, x_4);
x_13 = l_IO_println___rarg___closed__1;
x_14 = l___private_init_io_1__putStr___rarg(x_1, x_13);
x_15 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_12, x_14);
return x_15;
}
}
obj* l_IO_println(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_println___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_IO_println___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_IO_println___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_IO_println___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_IO_println(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_IO_Fs_handle_mk___rarg(obj* x_0, obj* x_1, uint8 x_2, uint8 x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::box(x_2);
x_5 = lean::box(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_handle_mk___boxed), 4, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_6);
return x_7;
}
}
obj* l_IO_Fs_handle_mk(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Fs_handle_mk___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_IO_Fs_handle_mk___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox(x_2);
x_5 = lean::unbox(x_3);
x_6 = l_IO_Fs_handle_mk___rarg(x_0, x_1, x_4, x_5);
return x_6;
}
}
obj* l_IO_Fs_handle_mk___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Fs_handle_mk(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_Fs_handle_isEof___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_handle_isEof___boxed), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_2);
return x_3;
}
}
obj* l_IO_Fs_handle_isEof(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Fs_handle_isEof___rarg), 2, 0);
return x_2;
}
}
obj* l_IO_Fs_handle_isEof___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Fs_handle_isEof(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_Fs_handle_flush___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_handle_flush___boxed), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_2);
return x_3;
}
}
obj* l_IO_Fs_handle_flush(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Fs_handle_flush___rarg), 2, 0);
return x_2;
}
}
obj* l_IO_Fs_handle_flush___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Fs_handle_flush(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_Fs_handle_close___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_handle_flush___boxed), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_2);
return x_3;
}
}
obj* l_IO_Fs_handle_close(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Fs_handle_close___rarg), 2, 0);
return x_2;
}
}
obj* l_IO_Fs_handle_close___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Fs_handle_close(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_Fs_handle_getLine___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_handle_getLine___boxed), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_2);
return x_3;
}
}
obj* l_IO_Fs_handle_getLine(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Fs_handle_getLine___rarg), 2, 0);
return x_2;
}
}
obj* l_IO_Fs_handle_getLine___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Fs_handle_getLine(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_Fs_handle_isEof___at_IO_Fs_handle_readToEnd___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_handle_is_eof(x_0, x_1);
return x_2;
}
}
obj* l_IO_Fs_handle_getLine___at_IO_Fs_handle_readToEnd___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_handle_get_line(x_0, x_1);
return x_2;
}
}
obj* l_IO_Prim_iterate___main___at_IO_Fs_handle_readToEnd___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_io_prim_handle_is_eof(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; uint8 x_6; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::unbox(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_9 = x_3;
} else {
 lean::inc(x_7);
 lean::dec(x_3);
 x_9 = lean::box(0);
}
x_10 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_7);
x_12 = lean_io_prim_handle_get_line(x_0, x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; 
x_13 = lean::cnstr_get(x_12, 0);
x_15 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 x_17 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_12);
 x_17 = lean::box(0);
}
x_18 = lean::string_append(x_1, x_13);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_17;
}
lean::cnstr_set(x_20, 0, x_10);
lean::cnstr_set(x_20, 1, x_15);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
else
{
obj* x_23; obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_1);
x_23 = lean::cnstr_get(x_12, 0);
x_25 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 x_27 = x_12;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_12);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_23);
lean::cnstr_set(x_28, 1, x_25);
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_31 = x_3;
} else {
 lean::inc(x_29);
 lean::dec(x_3);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_1);
lean::cnstr_set(x_32, 1, x_29);
return x_32;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_1);
x_34 = lean::cnstr_get(x_3, 0);
x_36 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_38 = x_3;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_3);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_34);
lean::cnstr_set(x_39, 1, x_36);
return x_39;
}
}
}
obj* l_IO_Prim_iterate___at_IO_Fs_handle_readToEnd___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_Prim_iterate___main___at_IO_Fs_handle_readToEnd___spec__4(x_0, x_1, x_2);
return x_3;
}
}
obj* l_IO_Fs_handle_readToEnd___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___at_IO_Fs_handle_readToEnd___spec__3___boxed), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::apply_2(x_0, lean::box(0), x_3);
return x_4;
}
}
obj* l_IO_Fs_handle_readToEnd(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Fs_handle_readToEnd___rarg), 2, 0);
return x_2;
}
}
obj* l_IO_Fs_handle_isEof___at_IO_Fs_handle_readToEnd___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Fs_handle_isEof___at_IO_Fs_handle_readToEnd___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_IO_Fs_handle_getLine___at_IO_Fs_handle_readToEnd___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Fs_handle_getLine___at_IO_Fs_handle_readToEnd___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_IO_Prim_iterate___main___at_IO_Fs_handle_readToEnd___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_Prim_iterate___main___at_IO_Fs_handle_readToEnd___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_IO_Prim_iterate___at_IO_Fs_handle_readToEnd___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_Prim_iterate___at_IO_Fs_handle_readToEnd___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_IO_Fs_handle_readToEnd___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Fs_handle_readToEnd(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_Fs_readFile___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_IO_Fs_handle_close___rarg(x_0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_getModify___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_6, 0, x_2);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_5, x_6);
return x_7;
}
}
obj* l_IO_Fs_readFile___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; 
lean::inc(x_3);
lean::inc(x_0);
x_6 = l_IO_Fs_handle_readToEnd___rarg(x_0, x_3);
lean::inc(x_2);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Fs_readFile___rarg___lambda__1), 5, 4);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_3);
lean::closure_set(x_8, 2, x_1);
lean::closure_set(x_8, 3, x_2);
x_9 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_6, x_8);
return x_9;
}
}
obj* l_IO_Fs_readFile___rarg(obj* x_0, obj* x_1, obj* x_2, uint8 x_3) {
_start:
{
obj* x_4; uint8 x_6; obj* x_8; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = 0;
lean::inc(x_1);
x_8 = l_IO_Fs_handle_mk___rarg(x_1, x_2, x_6, x_3);
lean::inc(x_4);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Fs_readFile___rarg___lambda__2), 4, 3);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_0);
lean::closure_set(x_10, 2, x_4);
x_11 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_8, x_10);
return x_11;
}
}
obj* l_IO_Fs_readFile(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Fs_readFile___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_IO_Fs_readFile___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
x_5 = l_IO_Fs_readFile___rarg(x_0, x_1, x_2, x_4);
return x_5;
}
}
obj* l_IO_Fs_readFile___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_IO_Fs_readFile(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_IO_RefPointed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_IO_RefPointed___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_IO_RefPointed(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_IO_Inhabited(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_IO_Inhabited___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_IO_Inhabited(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_IO_Prim_mkRef___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::io_mk_ref(x_1, x_2);
return x_3;
}
}
obj* l_IO_Prim_Ref_get___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::io_ref_get(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_IO_Prim_Ref_set___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::io_ref_set(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_IO_Prim_Ref_swap___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::io_ref_swap(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_IO_Prim_Ref_reset___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::io_ref_reset(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_IO_mkRef___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_mkRef___boxed), 3, 2);
lean::closure_set(x_3, 0, lean::box(0));
lean::closure_set(x_3, 1, x_2);
x_4 = lean::apply_2(x_0, lean::box(0), x_3);
return x_4;
}
}
obj* l_IO_mkRef(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_mkRef___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_IO_mkRef___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_mkRef___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_IO_mkRef___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_mkRef(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_Ref_get___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_Ref_get___boxed), 3, 2);
lean::closure_set(x_3, 0, lean::box(0));
lean::closure_set(x_3, 1, x_2);
x_4 = lean::apply_2(x_0, lean::box(0), x_3);
return x_4;
}
}
obj* l_IO_Ref_get(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Ref_get___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_IO_Ref_get___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_Ref_get___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_IO_Ref_get___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Ref_get(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_Ref_set___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_Ref_set___boxed), 4, 3);
lean::closure_set(x_4, 0, lean::box(0));
lean::closure_set(x_4, 1, x_2);
lean::closure_set(x_4, 2, x_3);
x_5 = lean::apply_2(x_0, lean::box(0), x_4);
return x_5;
}
}
obj* l_IO_Ref_set(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Ref_set___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_IO_Ref_set___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_IO_Ref_set___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_IO_Ref_set___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Ref_set(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_Ref_swap___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_Ref_swap___boxed), 4, 3);
lean::closure_set(x_4, 0, lean::box(0));
lean::closure_set(x_4, 1, x_2);
lean::closure_set(x_4, 2, x_3);
x_5 = lean::apply_2(x_0, lean::box(0), x_4);
return x_5;
}
}
obj* l_IO_Ref_swap(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Ref_swap___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_IO_Ref_swap___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_IO_Ref_swap___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_IO_Ref_swap___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Ref_swap(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_Ref_reset___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_Ref_reset___boxed), 3, 2);
lean::closure_set(x_3, 0, lean::box(0));
lean::closure_set(x_3, 1, x_2);
x_4 = lean::apply_2(x_0, lean::box(0), x_3);
return x_4;
}
}
obj* l_IO_Ref_reset(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Ref_reset___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_IO_Ref_reset___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_Ref_reset___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_IO_Ref_reset___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_Ref_reset(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_IO_Ref_modify___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::apply_1(x_0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_Ref_set___boxed), 4, 3);
lean::closure_set(x_6, 0, lean::box(0));
lean::closure_set(x_6, 1, x_2);
lean::closure_set(x_6, 2, x_5);
x_7 = lean::apply_2(x_3, lean::box(0), x_6);
return x_7;
}
}
obj* l_IO_Ref_modify___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_Ref_reset___boxed), 3, 2);
lean::closure_set(x_6, 0, lean::box(0));
lean::closure_set(x_6, 1, x_0);
lean::inc(x_1);
x_8 = lean::apply_2(x_1, lean::box(0), x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Ref_modify___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_9, 0, x_2);
lean::closure_set(x_9, 1, x_4);
lean::closure_set(x_9, 2, x_0);
lean::closure_set(x_9, 3, x_1);
x_10 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_IO_Ref_modify___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
lean::inc(x_3);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_Ref_get___boxed), 3, 2);
lean::closure_set(x_9, 0, lean::box(0));
lean::closure_set(x_9, 1, x_3);
lean::inc(x_1);
x_11 = lean::apply_2(x_1, lean::box(0), x_9);
lean::inc(x_5);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Ref_modify___rarg___lambda__2), 5, 4);
lean::closure_set(x_13, 0, x_3);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_4);
lean::closure_set(x_13, 3, x_5);
x_14 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_11, x_13);
return x_14;
}
}
obj* l_IO_Ref_modify(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Ref_modify___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_IO_Ref_modify___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_IO_Ref_modify___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_IO_Ref_modify___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_IO_Ref_modify___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_IO_Ref_modify___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_IO_Ref_modify(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_io_1__putStr___at_HasRepr_HasEval___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_put_str(x_0, x_1);
return x_2;
}
}
obj* l_IO_print___at_HasRepr_HasEval___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_put_str(x_0, x_1);
return x_2;
}
}
obj* l_IO_println___at_HasRepr_HasEval___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_put_str(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_5;
}
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = l_IO_println___rarg___closed__1;
x_9 = lean_io_prim_put_str(x_8, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_14 = x_2;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_2);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_12);
return x_15;
}
}
}
obj* l_HasRepr_HasEval___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_0, x_1);
x_4 = l_IO_println___at_HasRepr_HasEval___spec__1(x_3, x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_HasRepr_HasEval(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_HasRepr_HasEval___rarg), 3, 0);
return x_1;
}
}
obj* l___private_init_io_1__putStr___at_HasRepr_HasEval___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_io_1__putStr___at_HasRepr_HasEval___spec__3(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_IO_print___at_HasRepr_HasEval___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_print___at_HasRepr_HasEval___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_IO_println___at_HasRepr_HasEval___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_println___at_HasRepr_HasEval___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_HasRepr_HasEval___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_HasRepr_HasEval(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_IO_HasEval___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
x_11 = lean::apply_2(x_0, x_4, x_10);
return x_11;
}
else
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_0);
x_13 = lean::cnstr_get(x_3, 0);
x_15 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_17 = x_3;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_13);
lean::cnstr_set(x_18, 1, x_15);
return x_18;
}
}
}
obj* l_IO_HasEval(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_HasEval___rarg), 3, 0);
return x_1;
}
}
obj* l_IO_HasEval___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_IO_HasEval(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_IOUnit_HasEval(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* initialize_init_control_estate(obj*);
obj* initialize_init_data_string_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_io(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_estate(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_string_basic(w);
if (io_result_is_error(w)) return w;
 l_EIO_Monad___closed__1 = _init_l_EIO_Monad___closed__1();
lean::mark_persistent(l_EIO_Monad___closed__1);
 l_EIO_MonadExcept___closed__1 = _init_l_EIO_MonadExcept___closed__1();
lean::mark_persistent(l_EIO_MonadExcept___closed__1);
 l_IO_error_HasToString = _init_l_IO_error_HasToString();
lean::mark_persistent(l_IO_error_HasToString);
 l_IO_error_Inhabited = _init_l_IO_error_Inhabited();
lean::mark_persistent(l_IO_error_Inhabited);
 l_unsafeIO___rarg___closed__1 = _init_l_unsafeIO___rarg___closed__1();
lean::mark_persistent(l_unsafeIO___rarg___closed__1);
 l_IO_println___rarg___closed__1 = _init_l_IO_println___rarg___closed__1();
lean::mark_persistent(l_IO_println___rarg___closed__1);
return w;
}
