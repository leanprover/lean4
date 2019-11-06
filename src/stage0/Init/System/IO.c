// Lean compiler output
// Module: Init.System.IO
// Imports: Init.Control.EState Init.Data.String.Basic Init.System.FilePath
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_IO_Prim_handle_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
lean_object* l_IO_println(lean_object*);
lean_object* l___private_Init_System_IO_1__putStr___rarg(lean_object*, lean_object*);
lean_object* l_IO_Ref_set___boxed(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_isEof___at_IO_Fs_handle_readToEnd___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_Ref_get___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Ref_swap___boxed(lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* l_IO_HasEval(lean_object*);
lean_object* l_IO_Ref_modify(lean_object*);
lean_object* l_IO_fileExists(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_isEof___rarg(lean_object*, lean_object*);
lean_object* l_getModify___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_close___rarg(lean_object*, lean_object*);
lean_object* l_IO_Ref_swap(lean_object*, lean_object*);
lean_object* l_EIO_Inhabited___rarg(lean_object*);
lean_object* l_HasRepr_HasEval___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_swap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_HasOrelse(lean_object*, lean_object*);
lean_object* l_IO_fileExists___rarg(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_mk(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_is_eof(lean_object*, lean_object*);
lean_object* l_IO_println___at_HasRepr_HasEval___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_IO_readTextFile___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_iterate___main___at_IO_Fs_handle_readToEnd___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_getLine(lean_object*, lean_object*);
lean_object* l_IO_print___boxed(lean_object*, lean_object*);
lean_object* l_IO_ofExcept(lean_object*, lean_object*);
lean_object* l_IO_print___at_HasRepr_HasEval___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_HasToString___closed__1;
lean_object* l_IO_Prim_iterate___at_IO_Fs_handle_readToEnd___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Ref_reset___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Error_Inhabited;
lean_object* l_EIO_Inhabited(lean_object*, lean_object*);
lean_object* lean_io_is_dir(lean_object*, lean_object*);
lean_object* l_IO_appDir___boxed(lean_object*);
lean_object* lean_io_app_dir(lean_object*);
lean_object* l_unsafeIO(lean_object*);
lean_object* l___private_Init_System_IO_1__putStr___at_HasRepr_HasEval___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_iterate___at_IO_Fs_handle_readToEnd___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_isDir___boxed(lean_object*, lean_object*);
lean_object* l_EIO_Monad(lean_object*);
lean_object* l_EIO_HasOrelse___closed__1;
lean_object* l_IO_fileExists___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_put_str(lean_object*, lean_object*);
lean_object* l_IO_Ref_modify___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Ref_modify___boxed(lean_object*);
lean_object* l_IO_realPath___rarg(lean_object*, lean_object*);
lean_object* l_IO_Prim_putStr___boxed(lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_IO_appDir___rarg(lean_object*, lean_object*);
lean_object* l_IO_print___at_HasRepr_HasEval___spec__2(lean_object*, lean_object*);
extern lean_object* l_String_Inhabited;
lean_object* l_allocprof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_MonadExcept(lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_EIO_MonadExcept___closed__1;
lean_object* l_IO_userError(lean_object*);
lean_object* l_IO_Ref_swap___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_flush(lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_get_line(lean_object*);
lean_object* l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_allocprof(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Ref_set___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
lean_object* l_IO_Error_HasToString;
lean_object* l_IO_appPath(lean_object*, lean_object*);
lean_object* l_IO_print___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_MonadExcept___closed__2;
lean_object* l_IO_userError___boxed(lean_object*);
lean_object* l_IO_Prim_getLine___boxed(lean_object*);
lean_object* l_IO_Prim_handle_isEof___boxed(lean_object*, lean_object*);
lean_object* lean_io_file_exists(lean_object*, lean_object*);
lean_object* l___private_Init_System_IO_1__putStr___at_HasRepr_HasEval___spec__3(lean_object*, lean_object*);
lean_object* l_IO_Ref_get(lean_object*, lean_object*);
lean_object* l_IO_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_liftIO___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_Ref_modify___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Ref_set(lean_object*, lean_object*);
lean_object* l_IO_Ref_reset(lean_object*, lean_object*);
lean_object* l_IO_appDir(lean_object*);
lean_object* lean_io_ref_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_getEnv___rarg(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_mk___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_realPath___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_iterate(lean_object*, lean_object*);
lean_object* l_IO_ofExcept___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Fs_readFile___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_dirName(lean_object*);
lean_object* l_IO_isDir(lean_object*, lean_object*);
lean_object* l_String_HasToString___boxed(lean_object*);
lean_object* l_IO_realPath___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_liftIO(lean_object*, lean_object*);
lean_object* l_IO_Inhabited(lean_object*);
lean_object* l_IO_Ref_modify___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_handle_close___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_handle_flush___boxed(lean_object*, lean_object*);
lean_object* l_IO_readTextFile(lean_object*, lean_object*);
lean_object* l_IO_println___boxed(lean_object*);
lean_object* l_EStateM_Monad(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_flush___boxed(lean_object*, lean_object*);
lean_object* l_IO_appPath___rarg___closed__1;
lean_object* lean_io_prim_handle_close(lean_object*, lean_object*);
lean_object* l_IO_Ref_modify___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef(lean_object*, lean_object*);
lean_object* l_IO_appPath___rarg(lean_object*);
lean_object* l_IO_Fs_readFile___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_readTextFile___rarg(lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_IO_Fs_readFile___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_IO_Prim_readTextFile___boxed(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_mk___boxed(lean_object*, lean_object*);
lean_object* l_IO_mkRef___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_System_IO_1__putStr___boxed(lean_object*, lean_object*);
lean_object* l_IO_Fs_readFile___boxed(lean_object*);
lean_object* l_IO_Prim_fileExists___boxed(lean_object*, lean_object*);
lean_object* l_IO_Ref_get___boxed(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_getLine___at_IO_Fs_handle_readToEnd___spec__2(lean_object*, lean_object*);
lean_object* l_IO_println___at_HasRepr_HasEval___spec__1(lean_object*, lean_object*);
lean_object* l_IO_HasEval___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_readToEnd(lean_object*, lean_object*);
lean_object* lean_io_prim_read_text_file(lean_object*, lean_object*);
lean_object* l_IO_println___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_getLine___at_IO_Fs_handle_readToEnd___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_getLine___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_IO_realPath(lean_object*, lean_object*);
lean_object* l_IO_print(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_getLine___rarg(lean_object*, lean_object*);
lean_object* l_IO_Prim_handle_getLine___boxed(lean_object*, lean_object*);
lean_object* l_IO_lazyPure(lean_object*);
lean_object* l_IO_Prim_Ref_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_nonBacktrackable(lean_object*);
lean_object* l_IO_initializing___boxed(lean_object*);
lean_object* l_IO_appDir___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_close___boxed(lean_object*, lean_object*);
lean_object* l_IO_isDir___boxed(lean_object*, lean_object*);
lean_object* l_IOUnit_HasEval(lean_object*, lean_object*);
lean_object* l_EIO_Monad___closed__1;
lean_object* l_IO_Fs_handle_readToEnd___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_reset___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_Inhabited___rarg(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_isEof(lean_object*, lean_object*);
lean_object* l_IO_getEnv(lean_object*, lean_object*);
lean_object* l_IO_Prim_iterate___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_System_IO_1__putStr(lean_object*, lean_object*);
lean_object* l_IO_Ref_reset___boxed(lean_object*, lean_object*);
lean_object* l_IO_Fs_readFile___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_readToEnd___rarg(lean_object*, lean_object*);
lean_object* l_HasRepr_HasEval(lean_object*);
lean_object* l_timeit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_isDir___rarg(lean_object*, lean_object*);
lean_object* l_EStateM_MonadExcept___rarg(lean_object*);
lean_object* l_IO_Fs_handle_isEof___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_iterate___main(lean_object*, lean_object*);
lean_object* l_unsafeIO___rarg(lean_object*);
lean_object* l_IO_Prim_iterate___main___at_IO_Fs_handle_readToEnd___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_flush___rarg(lean_object*, lean_object*);
lean_object* lean_io_timeit(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_iterate___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_appPath___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_IO_Prim_appPath___boxed(lean_object*);
lean_object* l_IO_Fs_handle_isEof___at_IO_Fs_handle_readToEnd___spec__1(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_close(lean_object*, lean_object*);
lean_object* l_IO_Fs_handle_mk___rarg(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_IO_Prim_liftIO___rarg(lean_object*, lean_object*);
lean_object* l_IO_RefPointed(lean_object*);
lean_object* l_IO_println___rarg___closed__1;
lean_object* l_IO_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_lazyPure___rarg(lean_object*, lean_object*);
lean_object* l_IO_Fs_readFile(lean_object*);
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* _init_l_EIO_Monad___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_Monad(lean_box(0), lean_box(0));
return x_1;
}
}
lean_object* l_EIO_Monad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_EIO_Monad___closed__1;
return x_2;
}
}
lean_object* _init_l_EIO_MonadExcept___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_nonBacktrackable(lean_box(0));
return x_1;
}
}
lean_object* _init_l_EIO_MonadExcept___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EIO_MonadExcept___closed__1;
x_2 = l_EStateM_MonadExcept___rarg(x_1);
return x_2;
}
}
lean_object* l_EIO_MonadExcept(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_EIO_MonadExcept___closed__2;
return x_2;
}
}
lean_object* l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* _init_l_EIO_HasOrelse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1___rarg), 3, 0);
return x_1;
}
}
lean_object* l_EIO_HasOrelse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_EIO_HasOrelse___closed__1;
return x_3;
}
}
lean_object* l_EIO_Inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_EStateM_Inhabited___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_EIO_Inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_Inhabited___rarg), 1, 0);
return x_3;
}
}
lean_object* _init_l_IO_Error_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_HasToString___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_IO_Error_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_Error_HasToString___closed__1;
return x_1;
}
}
lean_object* _init_l_IO_Error_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_String_Inhabited;
return x_1;
}
}
lean_object* l_IO_userError(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_IO_userError___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_userError(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* lean_io_error_to_string(lean_object* x_1) {
_start:
{
return x_1;
}
}
lean_object* l_unsafeIO___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
lean_object* l_unsafeIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_unsafeIO___rarg), 1, 0);
return x_2;
}
}
lean_object* l_timeit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_timeit(x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_allocprof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_allocprof(x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_IO_initializing___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_initializing(x_1);
return x_2;
}
}
lean_object* l_IO_ofExcept___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
}
lean_object* l_IO_ofExcept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_ofExcept___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_lazyPure___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_IO_lazyPure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_lazyPure___rarg), 2, 0);
return x_2;
}
}
lean_object* l_IO_Prim_iterate___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = lean_apply_2(x_2, x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_1 = x_7;
x_3 = x_6;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_IO_Prim_iterate___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_iterate___main___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_Prim_iterate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Prim_iterate___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_IO_Prim_iterate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_iterate___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_Prim_putStr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_put_str(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_readTextFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_read_text_file(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_getLine___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_prim_get_line(x_1);
return x_2;
}
}
lean_object* l_IO_Prim_handle_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = lean_io_prim_handle_mk(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_IO_Prim_handle_isEof___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_is_eof(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_handle_flush___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_flush(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_handle_close___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_close(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_handle_getLine___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_get_line(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_getenv(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_realPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_Prim_isDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_is_dir(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_fileExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_file_exists(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_appPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_app_dir(x_1);
return x_2;
}
}
lean_object* l_IO_Prim_liftIO___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_IO_Prim_liftIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_liftIO___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_Prim_liftIO___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Prim_liftIO(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_System_IO_1__putStr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_putStr___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l___private_Init_System_IO_1__putStr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_System_IO_1__putStr___rarg), 2, 0);
return x_3;
}
}
lean_object* l___private_Init_System_IO_1__putStr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_System_IO_1__putStr(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_print___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_3, x_4);
x_6 = l___private_Init_System_IO_1__putStr___rarg(x_1, x_5);
return x_6;
}
}
lean_object* l_IO_print(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_print___rarg), 4, 0);
return x_3;
}
}
lean_object* l_IO_print___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_IO_println___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
return x_1;
}
}
lean_object* l_IO_println___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_2);
x_8 = l_IO_print___rarg(x_2, lean_box(0), x_4, x_5);
x_9 = l_IO_println___rarg___closed__1;
x_10 = l___private_Init_System_IO_1__putStr___rarg(x_2, x_9);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_IO_println(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_println___rarg), 5, 0);
return x_2;
}
}
lean_object* l_IO_println___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_println(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_IO_readTextFile___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_readTextFile___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_readTextFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_readTextFile___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_readTextFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_readTextFile(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_getEnv___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_getEnv___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_getEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_getEnv___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_getEnv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_realPath___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_realPath___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_realPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_realPath___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_realPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_realPath(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_isDir___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_isDir___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_isDir(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_isDir___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_isDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_isDir(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_fileExists___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_fileExists___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_fileExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_fileExists___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_fileExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_fileExists(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_IO_appPath___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_Prim_appPath___boxed), 1, 0);
return x_1;
}
}
lean_object* l_IO_appPath___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_appPath___rarg___closed__1;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_IO_appPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_appPath___rarg), 1, 0);
return x_3;
}
}
lean_object* l_IO_appPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_appPath(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_appDir___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_System_FilePath_dirName(x_2);
x_4 = l_IO_realPath___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_IO_appDir___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_IO_appPath___rarg___closed__1;
lean_inc(x_2);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
x_6 = lean_alloc_closure((void*)(l_IO_appDir___rarg___lambda__1), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_IO_appDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_appDir___rarg), 2, 0);
return x_2;
}
}
lean_object* l_IO_appDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_appDir(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_IO_Fs_handle_mk___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(x_3);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_IO_Prim_handle_mk___boxed), 4, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_IO_Fs_handle_mk(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Fs_handle_mk___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_IO_Fs_handle_mk___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_IO_Fs_handle_mk___rarg(x_1, x_2, x_5, x_6);
return x_7;
}
}
lean_object* l_IO_Fs_handle_mk___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Fs_handle_mk(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Fs_handle_isEof___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_handle_isEof___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_Fs_handle_isEof(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Fs_handle_isEof___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_Fs_handle_isEof___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Fs_handle_isEof(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Fs_handle_flush___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_handle_flush___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_Fs_handle_flush(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Fs_handle_flush___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_Fs_handle_flush___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Fs_handle_flush(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Fs_handle_close___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_handle_flush___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_Fs_handle_close(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Fs_handle_close___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_Fs_handle_close___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Fs_handle_close(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Fs_handle_getLine___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_handle_getLine___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_Fs_handle_getLine(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Fs_handle_getLine___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_Fs_handle_getLine___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Fs_handle_getLine(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Fs_handle_isEof___at_IO_Fs_handle_readToEnd___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_is_eof(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_Fs_handle_getLine___at_IO_Fs_handle_readToEnd___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_get_line(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_Prim_iterate___main___at_IO_Fs_handle_readToEnd___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_is_eof(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_io_prim_handle_get_line(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_string_append(x_2, x_9);
lean_dec(x_9);
x_2 = x_11;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_4, 0);
lean_dec(x_18);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
return x_4;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_IO_Prim_iterate___at_IO_Fs_handle_readToEnd___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Prim_iterate___main___at_IO_Fs_handle_readToEnd___spec__4(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_IO_Fs_handle_readToEnd___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_alloc_closure((void*)(l_IO_Prim_iterate___at_IO_Fs_handle_readToEnd___spec__3___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_IO_Fs_handle_readToEnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Fs_handle_readToEnd___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_Fs_handle_isEof___at_IO_Fs_handle_readToEnd___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Fs_handle_isEof___at_IO_Fs_handle_readToEnd___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Fs_handle_getLine___at_IO_Fs_handle_readToEnd___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Fs_handle_getLine___at_IO_Fs_handle_readToEnd___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_iterate___main___at_IO_Fs_handle_readToEnd___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Prim_iterate___main___at_IO_Fs_handle_readToEnd___spec__4(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_Prim_iterate___at_IO_Fs_handle_readToEnd___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Prim_iterate___at_IO_Fs_handle_readToEnd___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_Fs_handle_readToEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Fs_handle_readToEnd(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Fs_readFile___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_IO_Fs_handle_close___rarg(x_1, x_2);
x_7 = lean_alloc_closure((void*)(l_getModify___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_IO_Fs_readFile___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_1);
x_5 = l_IO_Fs_handle_readToEnd___rarg(x_1, x_4);
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l_IO_Fs_readFile___rarg___lambda__1), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_IO_Fs_readFile___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = 0;
lean_inc(x_2);
x_7 = l_IO_Fs_handle_mk___rarg(x_2, x_3, x_6, x_4);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_IO_Fs_readFile___rarg___lambda__2), 4, 3);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_5);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_IO_Fs_readFile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_Fs_readFile___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_IO_Fs_readFile___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_IO_Fs_readFile___rarg(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_IO_Fs_readFile___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Fs_readFile(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_IO_RefPointed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_IO_Inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_IO_Prim_mkRef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_mk_ref(x_2, x_3);
return x_4;
}
}
lean_object* l_IO_Prim_Ref_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_ref_get(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_IO_Prim_Ref_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_ref_set(x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_IO_Prim_Ref_swap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_ref_swap(x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_IO_Prim_Ref_reset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_ref_reset(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_IO_mkRef___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_IO_Prim_mkRef___boxed), 3, 2);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_IO_mkRef(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_mkRef___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_mkRef___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_mkRef(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Ref_get___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_IO_Prim_Ref_get___boxed), 3, 2);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_IO_Ref_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Ref_get___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_Ref_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Ref_get(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Ref_set___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_IO_Prim_Ref_set___boxed), 4, 3);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_IO_Ref_set(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Ref_set___rarg), 4, 0);
return x_3;
}
}
lean_object* l_IO_Ref_set___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Ref_set(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Ref_swap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_IO_Prim_Ref_swap___boxed), 4, 3);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_IO_Ref_swap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Ref_swap___rarg), 4, 0);
return x_3;
}
}
lean_object* l_IO_Ref_swap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Ref_swap(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Ref_reset___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_IO_Prim_Ref_reset___boxed), 3, 2);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_IO_Ref_reset(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Ref_reset___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_Ref_reset___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Ref_reset(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Ref_modify___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_alloc_closure((void*)(l_IO_Prim_Ref_set___boxed), 4, 3);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_6);
x_8 = lean_apply_2(x_4, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_IO_Ref_modify___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_IO_Prim_Ref_reset___boxed), 3, 2);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_1);
lean_inc(x_2);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
x_8 = lean_alloc_closure((void*)(l_IO_Ref_modify___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, x_2);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_IO_Ref_modify___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_IO_Prim_Ref_get___boxed), 3, 2);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_4);
lean_inc(x_2);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_IO_Ref_modify___rarg___lambda__2), 5, 4);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_5);
lean_closure_set(x_9, 3, x_6);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_IO_Ref_modify(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_Ref_modify___rarg), 5, 0);
return x_2;
}
}
lean_object* l_IO_Ref_modify___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_Ref_modify___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_IO_Ref_modify___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Ref_modify(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_System_IO_1__putStr___at_HasRepr_HasEval___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_put_str(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_print___at_HasRepr_HasEval___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_put_str(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_println___at_HasRepr_HasEval___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_put_str(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_IO_println___rarg___closed__1;
x_6 = lean_io_prim_put_str(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* l_HasRepr_HasEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = l_IO_println___at_HasRepr_HasEval___spec__1(x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_HasRepr_HasEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HasRepr_HasEval___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_System_IO_1__putStr___at_HasRepr_HasEval___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_System_IO_1__putStr___at_HasRepr_HasEval___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_print___at_HasRepr_HasEval___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print___at_HasRepr_HasEval___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_println___at_HasRepr_HasEval___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_println___at_HasRepr_HasEval___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_HasEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_1, x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* l_IO_HasEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_HasEval___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IOUnit_HasEval(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Init_Control_EState(lean_object*);
lean_object* initialize_Init_Data_String_Basic(lean_object*);
lean_object* initialize_Init_System_FilePath(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_System_IO(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_EState(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_EIO_Monad___closed__1 = _init_l_EIO_Monad___closed__1();
lean_mark_persistent(l_EIO_Monad___closed__1);
l_EIO_MonadExcept___closed__1 = _init_l_EIO_MonadExcept___closed__1();
lean_mark_persistent(l_EIO_MonadExcept___closed__1);
l_EIO_MonadExcept___closed__2 = _init_l_EIO_MonadExcept___closed__2();
lean_mark_persistent(l_EIO_MonadExcept___closed__2);
l_EIO_HasOrelse___closed__1 = _init_l_EIO_HasOrelse___closed__1();
lean_mark_persistent(l_EIO_HasOrelse___closed__1);
l_IO_Error_HasToString___closed__1 = _init_l_IO_Error_HasToString___closed__1();
lean_mark_persistent(l_IO_Error_HasToString___closed__1);
l_IO_Error_HasToString = _init_l_IO_Error_HasToString();
lean_mark_persistent(l_IO_Error_HasToString);
l_IO_Error_Inhabited = _init_l_IO_Error_Inhabited();
lean_mark_persistent(l_IO_Error_Inhabited);
l_IO_println___rarg___closed__1 = _init_l_IO_println___rarg___closed__1();
lean_mark_persistent(l_IO_println___rarg___closed__1);
l_IO_appPath___rarg___closed__1 = _init_l_IO_appPath___rarg___closed__1();
lean_mark_persistent(l_IO_appPath___rarg___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
