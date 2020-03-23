// Lean compiler output
// Module: Init.System.IO
// Imports: Init.Control.EState Init.Data.String.Basic Init.Data.ByteArray Init.System.IOError Init.System.FilePath
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
lean_object* l_IO_FS_linesAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_linesAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStrLn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_System_IO_1__putStr(lean_object*, lean_object*);
lean_object* l_allocprof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef___boxed(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* l_IO_print___at_Lean_HasRepr_hasEval___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_IO_Ref_modify___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_appPath___rarg___closed__1;
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
lean_object* lean_io_timeit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IO_HasEval___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_is_eof(lean_object*, lean_object*);
lean_object* l_IO_Prim_iterate___main(lean_object*, lean_object*);
lean_object* l_IO_Ref_set___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_chmod(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_Prim_getEnv___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_put_str(lean_object*, lean_object*);
lean_object* l_IO_println(lean_object*);
lean_object* l_Lean_Unit_hasEval(lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__12;
lean_object* l_EIO_Monad___closed__1;
lean_object* l_IO_FS_Handle_read___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Unit_hasEval___rarg___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_withFile___rarg(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_is_dir(lean_object*, lean_object*);
lean_object* l_IO_print___at_Lean_HasRepr_hasEval___spec__2(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStr___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_System_IO_1__putStr___at_Lean_HasRepr_hasEval___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_IO_getEnv___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_getLine___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_mk___boxed(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_IO_Ref_ptrEq___boxed(lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_unsafeIO___rarg(lean_object*);
uint32_t l_UInt32_shiftLeft(uint32_t, uint32_t);
lean_object* l_IO_FS_Handle_write(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_IO_print(lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_flush___rarg(lean_object*, lean_object*);
extern lean_object* l_Unit_HasRepr___closed__1;
lean_object* l_IO_Ref_get___boxed(lean_object*, lean_object*);
lean_object* l_IO_Ref_modify___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Handle_mk___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_fileExists___boxed(lean_object*, lean_object*);
lean_object* l_IO_Ref_swap___boxed(lean_object*, lean_object*);
lean_object* l_EIO_MonadExcept___closed__1;
uint32_t l_IO_AccessRight_flags___closed__6;
lean_object* l_IO_FS_Handle_readToEnd___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Unit_hasEval___boxed(lean_object*);
lean_object* l_IO_isDir(lean_object*, lean_object*);
lean_object* l_IO_Ref_swap___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_Inhabited(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStr___boxed(lean_object*, lean_object*);
lean_object* l_EIO_adaptExcept___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__11;
lean_object* l_IO_FS_Handle_getByte(lean_object*, lean_object*);
lean_object* l_IO_FS_lines___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags___closed__13;
lean_object* l_IO_setAccessRights(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Ref_get___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putByte___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Handle_isEof___boxed(lean_object*, lean_object*);
lean_object* l_Lean_HasRepr_hasEval___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_getLine___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEndAux(lean_object*);
uint32_t l_IO_AccessRight_flags___closed__8;
lean_object* l_EIO_Inhabited___rarg(lean_object*);
lean_object* l_IO_FS_Handle_putByte___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__7;
lean_object* l_EStateM_Inhabited___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_linesAux___main(lean_object*);
lean_object* l_IO_lazyPure___rarg(lean_object*, lean_object*);
lean_object* l_IO_Prim_liftIO(lean_object*, lean_object*);
lean_object* l_IO_AccessRight_flags___boxed(lean_object*);
lean_object* l_IO_Ref_get(lean_object*, lean_object*);
lean_object* l_IO_Prim_realPath___boxed(lean_object*, lean_object*);
lean_object* l_IO_appDir(lean_object*);
uint32_t l_IO_AccessRight_flags___closed__1;
uint32_t l_IO_AccessRight_flags___closed__9;
lean_object* l_IO_appPath___rarg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags___closed__2;
lean_object* l_IO_Ref_set___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putByte(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_read___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_liftIO___rarg(lean_object*, lean_object*);
lean_object* l_IO_println___at_Lean_HasRepr_hasEval___spec__1(lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags___closed__4;
lean_object* l_EIO_MonadExcept(lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__10;
lean_object* l_IO_Ref_reset___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_write___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_realPath___boxed(lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* l_System_FilePath_dirName(lean_object*);
lean_object* l_IO_Prim_Ref_reset___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEndAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags(uint8_t, uint8_t);
lean_object* l_IO_Ref_modify___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_linesAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Inhabited(lean_object*);
lean_object* l_IO_Ref_modify___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_String_back(lean_object*);
lean_object* l_IO_Prim_Handle_write___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_allocprof(lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_HasOrelse(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_getLine(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEndAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_appPath___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_getByte___rarg(lean_object*, lean_object*);
lean_object* l_IO_println___rarg___closed__1;
lean_object* l_IO_initializing___boxed(lean_object*);
lean_object* l_IO_println___at_Lean_HasRepr_hasEval___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_iterate(lean_object*, lean_object*);
lean_object* l_IO_Prim_iterate___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_write_byte(lean_object*, uint8_t, lean_object*);
lean_object* l_IO_FS_Handle_mk(lean_object*, lean_object*);
lean_object* l_IO_FS_linesAux(lean_object*);
lean_object* l_IO_Prim_Handle_getLine___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_mk___rarg(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_IO_println___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_adaptExcept(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_isDir___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEndAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_fileExists___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_isEof(lean_object*, lean_object*);
lean_object* l_IO_realPath___rarg(lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__6;
lean_object* l_IO_Prim_appPath___boxed(lean_object*);
lean_object* l_IO_FileRight_flags___boxed(lean_object*);
uint32_t l_IO_AccessRight_flags___closed__11;
lean_object* l_IO_Ref_modify(lean_object*);
lean_object* l_IO_FS_Handle_read(lean_object*, lean_object*);
lean_object* l_String_dropRight(lean_object*, lean_object*);
lean_object* l_EIO_catchExceptions(lean_object*, lean_object*);
lean_object* l_IO_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_IO_Prim_putStr___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putByte___rarg(lean_object*, lean_object*, uint8_t);
lean_object* l_IO_ofExcept___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_fileExists___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_System_IO_1__putStr___at_Lean_HasRepr_hasEval___spec__3(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_realPath(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_HasOrelse___closed__1;
lean_object* l_IO_ofExcept(lean_object*, lean_object*);
lean_object* lean_io_file_exists(lean_object*, lean_object*);
lean_object* l_Lean_IO_HasEval(lean_object*);
lean_object* l_EStateM_nonBacktrackable(lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_IO_Prim_isDir___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStr(lean_object*, lean_object*);
lean_object* l_IO_Prim_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_isDir___rarg(lean_object*, lean_object*);
lean_object* l_IO_getEnv(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEndAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Handle_getByte___boxed(lean_object*, lean_object*);
lean_object* l_IO_lazyPure(lean_object*);
lean_object* l_EStateM_Monad(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_mk___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_ptr_eq(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_write___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__5;
lean_object* l_IO_Prim_fopenFlags___closed__14;
lean_object* l_IO_FS_Handle_readToEndAux___main(lean_object*);
lean_object* l_IO_FS_readFile___rarg(lean_object*, lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags(lean_object*);
lean_object* l_unsafeIO(lean_object*);
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__3;
lean_object* lean_io_ref_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_IO_print___boxed(lean_object*, lean_object*);
lean_object* l_IO_Ref_swap(lean_object*, lean_object*);
lean_object* l_IO_Ref_ptrEq(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*);
lean_object* l_IO_FS_lines___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_swap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_read_byte(lean_object*, lean_object*);
lean_object* l_IO_appDir___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_read___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Ref_reset___boxed(lean_object*, lean_object*);
lean_object* l_EStateM_MonadExcept___rarg(lean_object*);
lean_object* l_IO_Prim_Handle_putByte___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_MonadExcept___closed__2;
uint32_t l_IO_AccessRight_flags___closed__10;
lean_object* l_IO_FS_Handle_getByte___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Unit_hasEval___rarg(uint8_t, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*, lean_object*);
uint32_t l_UInt32_lor(uint32_t, uint32_t);
lean_object* l_IO_Prim_fopenFlags___closed__4;
lean_object* l_IO_appPath(lean_object*, lean_object*);
lean_object* l_IO_Ref_set(lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__9;
lean_object* lean_string_length(lean_object*);
lean_object* l_IO_mkRef(lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_ptrEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_isEof___boxed(lean_object*, lean_object*);
lean_object* l_IO_Ref_ptrEq___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_Monad(lean_object*);
lean_object* l___private_Init_System_IO_1__putStr___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__8;
lean_object* l_IO_Prim_Handle_putStr___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IO_HasEval___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_timeit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_app_dir(lean_object*);
lean_object* l_IO_FS_Handle_isEof___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_flush(lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags___closed__12;
lean_object* l_IO_Prim_fopenFlags___boxed(lean_object*, lean_object*);
lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HasRepr_hasEval___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__1;
lean_object* l_IO_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_withFile___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_read(lean_object*, size_t, lean_object*);
lean_object* l_IO_FS_lines(lean_object*);
lean_object* l_IO_FS_Handle_mk___at_IO_FS_withFile___spec__1(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_IO_fileExists(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_flush___boxed(lean_object*, lean_object*);
lean_object* l_IO_print___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__2;
lean_object* l_IO_RefPointed(lean_object*);
lean_object* l___private_Init_System_IO_1__putStr___rarg(lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags___closed__5;
lean_object* lean_io_prim_handle_mk(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_appDir___rarg(lean_object*, lean_object*);
lean_object* l_IO_Prim_iterate___main___rarg(lean_object*, lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags___closed__7;
uint32_t l_IO_FileRight_flags(lean_object*);
lean_object* l_EIO_catchExceptions___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Handle_read___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_mk___at_IO_FS_withFile___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__13;
uint32_t l_IO_AccessRight_flags___closed__3;
lean_object* l_IO_FS_withFile(lean_object*);
lean_object* l_IO_Prim_Handle_flush___boxed(lean_object*, lean_object*);
lean_object* l_IO_Ref_reset(lean_object*, lean_object*);
lean_object* l_Lean_HasRepr_hasEval(lean_object*);
lean_object* l_EIO_adaptExcept___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_apply_1(x_1, x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_apply_1(x_1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
lean_object* l_EIO_adaptExcept(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_EIO_adaptExcept___rarg), 3, 0);
return x_4;
}
}
lean_object* l_EIO_catchExceptions___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_apply_2(x_2, x_9, x_10);
return x_11;
}
}
}
lean_object* l_EIO_catchExceptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_catchExceptions___rarg), 3, 0);
return x_3;
}
}
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
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
lean_object* _init_l_IO_Prim_fopenFlags___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("r");
return x_1;
}
}
lean_object* _init_l_IO_Prim_fopenFlags___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("t");
return x_1;
}
}
lean_object* _init_l_IO_Prim_fopenFlags___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__1;
x_2 = l_IO_Prim_fopenFlags___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_IO_Prim_fopenFlags___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("b");
return x_1;
}
}
lean_object* _init_l_IO_Prim_fopenFlags___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__1;
x_2 = l_IO_Prim_fopenFlags___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_IO_Prim_fopenFlags___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("w");
return x_1;
}
}
lean_object* _init_l_IO_Prim_fopenFlags___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__6;
x_2 = l_IO_Prim_fopenFlags___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_IO_Prim_fopenFlags___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__6;
x_2 = l_IO_Prim_fopenFlags___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_IO_Prim_fopenFlags___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("r+");
return x_1;
}
}
lean_object* _init_l_IO_Prim_fopenFlags___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__9;
x_2 = l_IO_Prim_fopenFlags___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_IO_Prim_fopenFlags___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__9;
x_2 = l_IO_Prim_fopenFlags___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_IO_Prim_fopenFlags___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a");
return x_1;
}
}
lean_object* _init_l_IO_Prim_fopenFlags___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__12;
x_2 = l_IO_Prim_fopenFlags___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_IO_Prim_fopenFlags___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__12;
x_2 = l_IO_Prim_fopenFlags___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_Prim_fopenFlags(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_IO_Prim_fopenFlags___closed__3;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_IO_Prim_fopenFlags___closed__5;
return x_4;
}
}
case 1:
{
if (x_2 == 0)
{
lean_object* x_5; 
x_5 = l_IO_Prim_fopenFlags___closed__7;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_IO_Prim_fopenFlags___closed__8;
return x_6;
}
}
case 2:
{
if (x_2 == 0)
{
lean_object* x_7; 
x_7 = l_IO_Prim_fopenFlags___closed__10;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_IO_Prim_fopenFlags___closed__11;
return x_8;
}
}
default: 
{
if (x_2 == 0)
{
lean_object* x_9; 
x_9 = l_IO_Prim_fopenFlags___closed__13;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_IO_Prim_fopenFlags___closed__14;
return x_10;
}
}
}
}
}
lean_object* l_IO_Prim_fopenFlags___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_Prim_fopenFlags(x_3, x_4);
return x_5;
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
lean_object* l_IO_Prim_Handle_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_mk(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_Prim_Handle_isEof___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_is_eof(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_Handle_flush___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_flush(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_Handle_read___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_io_prim_handle_read(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_IO_Prim_Handle_write___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_write(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_Prim_Handle_getByte___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_read_byte(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_Handle_putByte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = lean_io_prim_handle_write_byte(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_IO_Prim_Handle_getLine___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_get_line(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_Handle_putStr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_put_str(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
lean_object* l_IO_FS_Handle_mk___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_IO_Prim_fopenFlags(x_3, x_4);
x_6 = lean_alloc_closure((void*)(l_IO_Prim_Handle_mk___boxed), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_IO_FS_Handle_mk(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_mk___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_mk___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_IO_FS_Handle_mk___rarg(x_1, x_2, x_5, x_6);
return x_7;
}
}
lean_object* l_IO_FS_Handle_mk___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_mk(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_mk___at_IO_FS_withFile___spec__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_IO_Prim_fopenFlags(x_2, x_3);
x_6 = lean_io_prim_handle_mk(x_1, x_5, x_4);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_IO_FS_withFile___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_IO_FS_Handle_mk___at_IO_FS_withFile___spec__1(x_1, x_2, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_IO_FS_withFile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_withFile___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_Handle_mk___at_IO_FS_withFile___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_IO_FS_Handle_mk___at_IO_FS_withFile___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_IO_FS_withFile___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_IO_FS_withFile___rarg(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_IO_FS_Handle_isEof___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_Handle_isEof___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_FS_Handle_isEof(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_isEof___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_isEof___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_isEof(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_flush___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_Handle_flush___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_FS_Handle_flush(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_flush___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_flush___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_flush(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_read___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_usize_of_nat(x_3);
x_5 = lean_box_usize(x_4);
x_6 = lean_alloc_closure((void*)(l_IO_Prim_Handle_read___boxed), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_IO_FS_Handle_read(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_read___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_read___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_read___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_IO_FS_Handle_read___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_read(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_write___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_IO_Prim_Handle_write___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_IO_FS_Handle_write(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_write___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_write___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_write(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_getByte___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_Handle_getByte___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_FS_Handle_getByte(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_getByte___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_getByte___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_getByte(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_putByte___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_IO_Prim_Handle_putByte___boxed), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_IO_FS_Handle_putByte(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_putByte___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_putByte___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_IO_FS_Handle_putByte___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_IO_FS_Handle_putByte___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_putByte(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_getLine___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_Handle_getLine___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_FS_Handle_getLine(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_getLine___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_getLine___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_getLine(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_putStr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_IO_Prim_Handle_putStr___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_IO_FS_Handle_putStr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_putStr___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_putStr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_putStr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_putStrLn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_IO_FS_Handle_putStr___rarg(x_2, x_3, x_4);
x_8 = l_IO_println___rarg___closed__1;
x_9 = l_IO_FS_Handle_putStr___rarg(x_2, x_3, x_8);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
lean_object* l_IO_FS_Handle_putStrLn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Handle_putStrLn___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_Handle_readToEndAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_string_length(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_string_append(x_1, x_5);
x_10 = l_IO_FS_Handle_readToEndAux___main___rarg(x_2, x_3, x_4, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_1);
return x_13;
}
}
}
lean_object* l_IO_FS_Handle_readToEndAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_IO_FS_Handle_getLine___rarg(x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEndAux___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_IO_FS_Handle_readToEndAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEndAux___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_Handle_readToEndAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Handle_readToEndAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_IO_FS_Handle_readToEndAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Handle_readToEndAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_IO_FS_Handle_readToEndAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEndAux___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_Handle_readToEnd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_String_splitAux___main___closed__1;
x_5 = l_IO_FS_Handle_readToEndAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_IO_FS_Handle_readToEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEnd___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_FS_readFile___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_String_splitAux___main___closed__1;
x_5 = l_IO_FS_Handle_readToEndAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_IO_FS_readFile___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = 0;
x_6 = 0;
lean_inc(x_2);
x_7 = l_IO_FS_Handle_mk___rarg(x_2, x_3, x_5, x_6);
x_8 = lean_alloc_closure((void*)(l_IO_FS_readFile___rarg___lambda__1), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_IO_FS_readFile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_readFile___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_FS_linesAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_string_length(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; uint8_t x_30; 
x_9 = l_String_back(x_5);
x_10 = 10;
x_30 = x_9 == x_10;
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = 0;
x_11 = x_31;
goto block_29;
}
else
{
uint8_t x_32; 
x_32 = 1;
x_11 = x_32;
goto block_29;
}
block_29:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_array_push(x_2, x_5);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_String_dropRight(x_5, x_16);
lean_dec(x_5);
x_18 = l_System_Platform_isWindows;
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_push(x_2, x_17);
x_20 = l_IO_FS_linesAux___main___rarg(x_1, x_3, x_4, x_19);
return x_20;
}
else
{
uint32_t x_21; uint32_t x_22; uint8_t x_23; 
x_21 = l_String_back(x_17);
x_22 = 13;
x_23 = x_21 == x_22;
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_array_push(x_2, x_17);
x_25 = l_IO_FS_linesAux___main___rarg(x_1, x_3, x_4, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_String_dropRight(x_17, x_16);
lean_dec(x_17);
x_27 = lean_array_push(x_2, x_26);
x_28 = l_IO_FS_linesAux___main___rarg(x_1, x_3, x_4, x_27);
return x_28;
}
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_apply_2(x_34, lean_box(0), x_2);
return x_35;
}
}
}
lean_object* l_IO_FS_linesAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_IO_FS_Handle_getLine___rarg(x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_IO_FS_linesAux___main___rarg___lambda__1), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_IO_FS_linesAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_linesAux___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_linesAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_linesAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_IO_FS_linesAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_linesAux___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_lines___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Array_empty___closed__1;
x_5 = l_IO_FS_linesAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_IO_FS_lines___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = 0;
x_6 = 0;
lean_inc(x_2);
x_7 = l_IO_FS_Handle_mk___rarg(x_2, x_3, x_5, x_6);
x_8 = lean_alloc_closure((void*)(l_IO_FS_lines___rarg___lambda__1), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_IO_FS_lines(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_lines___rarg), 3, 0);
return x_2;
}
}
uint32_t _init_l_IO_AccessRight_flags___closed__1() {
_start:
{
uint32_t x_1; uint32_t x_2; 
x_1 = 0;
x_2 = x_1 | x_1;
return x_2;
}
}
uint32_t _init_l_IO_AccessRight_flags___closed__2() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__1;
x_3 = x_1 | x_2;
return x_3;
}
}
uint32_t _init_l_IO_AccessRight_flags___closed__3() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = 1;
x_3 = x_1 | x_2;
return x_3;
}
}
uint32_t _init_l_IO_AccessRight_flags___closed__4() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__3;
x_3 = x_1 | x_2;
return x_3;
}
}
uint32_t _init_l_IO_AccessRight_flags___closed__5() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = 2;
x_3 = x_2 | x_1;
return x_3;
}
}
uint32_t _init_l_IO_AccessRight_flags___closed__6() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__5;
x_3 = x_1 | x_2;
return x_3;
}
}
uint32_t _init_l_IO_AccessRight_flags___closed__7() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 2;
x_2 = 1;
x_3 = x_1 | x_2;
return x_3;
}
}
uint32_t _init_l_IO_AccessRight_flags___closed__8() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__7;
x_3 = x_1 | x_2;
return x_3;
}
}
uint32_t _init_l_IO_AccessRight_flags___closed__9() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__1;
x_3 = x_1 | x_2;
return x_3;
}
}
uint32_t _init_l_IO_AccessRight_flags___closed__10() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__3;
x_3 = x_1 | x_2;
return x_3;
}
}
uint32_t _init_l_IO_AccessRight_flags___closed__11() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 2;
x_2 = 0;
x_3 = x_1 | x_2;
return x_3;
}
}
uint32_t _init_l_IO_AccessRight_flags___closed__12() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__11;
x_3 = x_1 | x_2;
return x_3;
}
}
uint32_t _init_l_IO_AccessRight_flags___closed__13() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__7;
x_3 = x_1 | x_2;
return x_3;
}
}
uint32_t l_IO_AccessRight_flags(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, 0);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, 1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, 2);
if (x_4 == 0)
{
uint32_t x_5; 
x_5 = l_IO_AccessRight_flags___closed__2;
return x_5;
}
else
{
uint32_t x_6; 
x_6 = l_IO_AccessRight_flags___closed__4;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, 2);
if (x_7 == 0)
{
uint32_t x_8; 
x_8 = l_IO_AccessRight_flags___closed__6;
return x_8;
}
else
{
uint32_t x_9; 
x_9 = l_IO_AccessRight_flags___closed__8;
return x_9;
}
}
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, 1);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_1, 2);
if (x_11 == 0)
{
uint32_t x_12; 
x_12 = l_IO_AccessRight_flags___closed__9;
return x_12;
}
else
{
uint32_t x_13; 
x_13 = l_IO_AccessRight_flags___closed__10;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_1, 2);
if (x_14 == 0)
{
uint32_t x_15; 
x_15 = l_IO_AccessRight_flags___closed__12;
return x_15;
}
else
{
uint32_t x_16; 
x_16 = l_IO_AccessRight_flags___closed__13;
return x_16;
}
}
}
}
}
lean_object* l_IO_AccessRight_flags___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_IO_AccessRight_flags(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
uint32_t l_IO_FileRight_flags(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint32_t x_5; uint32_t x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; lean_object* x_10; uint32_t x_11; uint32_t x_12; uint32_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_IO_AccessRight_flags(x_2);
x_4 = 3;
x_5 = 6;
x_6 = x_3 << x_5;
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_IO_AccessRight_flags(x_7);
x_9 = x_8 << x_4;
x_10 = lean_ctor_get(x_1, 2);
x_11 = l_IO_AccessRight_flags(x_10);
x_12 = x_9 | x_11;
x_13 = x_6 | x_12;
return x_13;
}
}
lean_object* l_IO_FileRight_flags___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_IO_FileRight_flags(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
lean_object* l_IO_Prim_setAccessRights___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_chmod(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_IO_setAccessRights(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = l_IO_FileRight_flags(x_2);
x_5 = lean_chmod(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_IO_setAccessRights___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_setAccessRights(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
lean_object* l_IO_Prim_Ref_ptrEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_ref_ptr_eq(x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
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
return x_3;
}
}
lean_object* l_IO_Ref_ptrEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_IO_Prim_Ref_ptrEq___boxed), 4, 3);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_IO_Ref_ptrEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Ref_ptrEq___rarg), 4, 0);
return x_3;
}
}
lean_object* l_IO_Ref_ptrEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Ref_ptrEq(x_1, x_2);
lean_dec(x_2);
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
lean_object* l___private_Init_System_IO_1__putStr___at_Lean_HasRepr_hasEval___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_put_str(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_print___at_Lean_HasRepr_hasEval___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_put_str(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_println___at_Lean_HasRepr_hasEval___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_HasRepr_hasEval___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = l_IO_println___at_Lean_HasRepr_hasEval___spec__1(x_5, x_4);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_HasRepr_hasEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HasRepr_hasEval___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_System_IO_1__putStr___at_Lean_HasRepr_hasEval___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_System_IO_1__putStr___at_Lean_HasRepr_hasEval___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_print___at_Lean_HasRepr_hasEval___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print___at_Lean_HasRepr_hasEval___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_println___at_Lean_HasRepr_hasEval___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_println___at_Lean_HasRepr_hasEval___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_HasRepr_hasEval___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_HasRepr_hasEval___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_Unit_hasEval___rarg(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Unit_HasRepr___closed__1;
x_4 = l_IO_println___at_Lean_HasRepr_hasEval___spec__1(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
lean_object* l_Lean_Unit_hasEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Unit_hasEval___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Unit_hasEval___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Unit_hasEval___rarg(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Unit_hasEval___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Unit_hasEval(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IO_HasEval___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_apply_3(x_1, x_6, x_9, x_7);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_IO_HasEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IO_HasEval___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_IO_HasEval___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_IO_HasEval___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* initialize_Init_Control_EState(lean_object*);
lean_object* initialize_Init_Data_String_Basic(lean_object*);
lean_object* initialize_Init_Data_ByteArray(lean_object*);
lean_object* initialize_Init_System_IOError(lean_object*);
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
res = initialize_Init_Data_ByteArray(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IOError(lean_io_mk_world());
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
l_IO_Prim_fopenFlags___closed__1 = _init_l_IO_Prim_fopenFlags___closed__1();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__1);
l_IO_Prim_fopenFlags___closed__2 = _init_l_IO_Prim_fopenFlags___closed__2();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__2);
l_IO_Prim_fopenFlags___closed__3 = _init_l_IO_Prim_fopenFlags___closed__3();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__3);
l_IO_Prim_fopenFlags___closed__4 = _init_l_IO_Prim_fopenFlags___closed__4();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__4);
l_IO_Prim_fopenFlags___closed__5 = _init_l_IO_Prim_fopenFlags___closed__5();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__5);
l_IO_Prim_fopenFlags___closed__6 = _init_l_IO_Prim_fopenFlags___closed__6();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__6);
l_IO_Prim_fopenFlags___closed__7 = _init_l_IO_Prim_fopenFlags___closed__7();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__7);
l_IO_Prim_fopenFlags___closed__8 = _init_l_IO_Prim_fopenFlags___closed__8();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__8);
l_IO_Prim_fopenFlags___closed__9 = _init_l_IO_Prim_fopenFlags___closed__9();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__9);
l_IO_Prim_fopenFlags___closed__10 = _init_l_IO_Prim_fopenFlags___closed__10();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__10);
l_IO_Prim_fopenFlags___closed__11 = _init_l_IO_Prim_fopenFlags___closed__11();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__11);
l_IO_Prim_fopenFlags___closed__12 = _init_l_IO_Prim_fopenFlags___closed__12();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__12);
l_IO_Prim_fopenFlags___closed__13 = _init_l_IO_Prim_fopenFlags___closed__13();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__13);
l_IO_Prim_fopenFlags___closed__14 = _init_l_IO_Prim_fopenFlags___closed__14();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__14);
l_IO_println___rarg___closed__1 = _init_l_IO_println___rarg___closed__1();
lean_mark_persistent(l_IO_println___rarg___closed__1);
l_IO_appPath___rarg___closed__1 = _init_l_IO_appPath___rarg___closed__1();
lean_mark_persistent(l_IO_appPath___rarg___closed__1);
l_IO_AccessRight_flags___closed__1 = _init_l_IO_AccessRight_flags___closed__1();
l_IO_AccessRight_flags___closed__2 = _init_l_IO_AccessRight_flags___closed__2();
l_IO_AccessRight_flags___closed__3 = _init_l_IO_AccessRight_flags___closed__3();
l_IO_AccessRight_flags___closed__4 = _init_l_IO_AccessRight_flags___closed__4();
l_IO_AccessRight_flags___closed__5 = _init_l_IO_AccessRight_flags___closed__5();
l_IO_AccessRight_flags___closed__6 = _init_l_IO_AccessRight_flags___closed__6();
l_IO_AccessRight_flags___closed__7 = _init_l_IO_AccessRight_flags___closed__7();
l_IO_AccessRight_flags___closed__8 = _init_l_IO_AccessRight_flags___closed__8();
l_IO_AccessRight_flags___closed__9 = _init_l_IO_AccessRight_flags___closed__9();
l_IO_AccessRight_flags___closed__10 = _init_l_IO_AccessRight_flags___closed__10();
l_IO_AccessRight_flags___closed__11 = _init_l_IO_AccessRight_flags___closed__11();
l_IO_AccessRight_flags___closed__12 = _init_l_IO_AccessRight_flags___closed__12();
l_IO_AccessRight_flags___closed__13 = _init_l_IO_AccessRight_flags___closed__13();
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
