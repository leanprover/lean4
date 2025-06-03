// Lean compiler output
// Module: Lean.Server.FileWorker.SetupFile
// Imports: Init.System.IO Lean.Server.Utils Lean.Util.FileSetupInfo Lean.Util.LakePath Lean.LoadDynlib Lean.Server.ServerTask
#include <lean/lean.h>
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
lean_object* l_Lean_Server_ServerTask_IO_asTask___rarg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_determineLakePath(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___closed__1;
lean_object* l_IO_ofExcept___at_IO_Process_output___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_setupFile___lambda__1___closed__3;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Server_FileWorker_setupFile___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_31_(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_setupFile___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_setupFile___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___lambda__1___closed__1;
static lean_object* l_Lean_Server_FileWorker_setupFile___lambda__1___closed__7;
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___closed__1;
static lean_object* l_Lean_Server_FileWorker_setupFile___lambda__1___closed__4;
static lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_setupFile___lambda__1___closed__6;
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(lean_object*);
lean_object* lean_get_prefix(lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofError(lean_object*, lean_object*);
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
lean_object* l_Lean_Json_Parser_any(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Server_FileWorker_setupFile___lambda__1___closed__5;
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1(size_t, size_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__2;
lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_load_dynlib(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__1;
static lean_object* l_Lean_Server_FileWorker_setupFile___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_setupFile___spec__1(size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Options_empty;
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__3;
static lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_setupFile___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realPathNormalized(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___lambda__1(lean_object*);
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_io_prim_handle_get_line(x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___closed__1;
x_13 = lean_string_dec_eq(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_free_object(x_8);
lean_inc(x_2);
lean_inc(x_10);
x_14 = lean_apply_2(x_2, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_string_append(x_5, x_10);
lean_dec(x_10);
x_5 = x_16;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_2);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___closed__1;
x_25 = lean_string_dec_eq(x_22, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_inc(x_2);
lean_inc(x_22);
x_26 = lean_apply_2(x_2, x_22, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_string_append(x_5, x_22);
lean_dec(x_22);
x_5 = x_28;
x_6 = x_27;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_2);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_32 = x_26;
} else {
 lean_dec_ref(x_26);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_22);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_23);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_5);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___closed__1;
x_11 = l_Lean_Name_toString(x_8, x_9, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 2;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_2);
lean_ctor_set_uint8(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_box(0);
x_8 = lean_array_mk(x_1);
x_9 = l_Lean_Server_FileWorker_runLakeSetupFile___lambda__1___closed__1;
x_10 = 1;
x_11 = 0;
lean_inc(x_4);
lean_inc(x_2);
x_12 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_4);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 4, x_8);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_11);
lean_inc(x_12);
x_13 = lean_io_process_spawn(x_12, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___closed__1;
lean_inc(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed), 6, 5);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_14);
lean_closure_set(x_17, 4, x_16);
x_18 = l_Lean_Server_ServerTask_IO_asTask___rarg(x_17, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
x_22 = l_IO_FS_Handle_readToEnd(x_21, x_20);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_string_utf8_byte_size(x_23);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_23, x_25, x_26);
x_28 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_23, x_27, x_25);
x_29 = lean_string_utf8_extract(x_23, x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
x_30 = lean_task_get_own(x_19);
x_31 = l_IO_ofExcept___at_IO_Process_output___spec__1(x_30, x_24);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_io_process_child_wait(x_9, x_14, x_33);
lean_dec(x_14);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint32_t x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_32);
x_38 = lean_unbox_uint32(x_36);
lean_dec(x_36);
lean_ctor_set_uint32(x_37, sizeof(void*)*3, x_38);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint32_t x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_41, 0, x_12);
lean_ctor_set(x_41, 1, x_29);
lean_ctor_set(x_41, 2, x_32);
x_42 = lean_unbox_uint32(x_39);
lean_dec(x_39);
lean_ctor_set_uint32(x_41, sizeof(void*)*3, x_42);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_12);
x_44 = !lean_is_exclusive(x_34);
if (x_44 == 0)
{
return x_34;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_34, 0);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_34);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_12);
x_48 = !lean_is_exclusive(x_31);
if (x_48 == 0)
{
return x_31;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_31, 0);
x_50 = lean_ctor_get(x_31, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_31);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_12);
x_52 = !lean_is_exclusive(x_22);
if (x_52 == 0)
{
return x_22;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_22, 0);
x_54 = lean_ctor_get(x_22, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_22);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_13);
if (x_56 == 0)
{
return x_13;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("setup-file", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--no-build", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--no-cache", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__1;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_array_mk(x_10);
x_12 = lean_array_size(x_4);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1(x_12, x_13, x_4);
x_15 = l_Array_append___rarg(x_11, x_14);
lean_dec(x_14);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_17 = lean_box(x_16);
if (lean_obj_tag(x_17) == 2)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__2;
x_19 = lean_array_push(x_15, x_18);
x_20 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__3;
x_21 = lean_array_push(x_19, x_20);
x_22 = lean_box(0);
x_23 = l_Lean_Server_FileWorker_runLakeSetupFile___lambda__1(x_7, x_2, x_5, x_21, x_22, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = l_Lean_Server_FileWorker_runLakeSetupFile___lambda__1(x_7, x_2, x_5, x_15, x_24, x_6);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_runLakeSetupFile___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_Options_empty;
x_3 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Options_empty;
x_3 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l_Lean_Options_empty;
x_5 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1;
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_setupFile___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = l_Lean_realPathNormalized(x_7, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_9, x_2, x_11);
x_2 = x_14;
x_3 = x_15;
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_setupFile___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_load_dynlib(x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` failed:\n", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nstderr:\n", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid output from `", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`:\n", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_2, x_3, x_4, x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint32_t x_18; uint32_t x_19; uint8_t x_20; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_to_list(x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Server_FileWorker_setupFile___lambda__1___closed__1;
x_17 = l_String_intercalate(x_16, x_15);
x_18 = lean_ctor_get_uint32(x_9, sizeof(void*)*3);
x_19 = 0;
x_20 = lean_uint32_dec_eq(x_18, x_19);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 2;
x_22 = lean_uint32_dec_eq(x_18, x_21);
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 3;
x_24 = lean_uint32_dec_eq(x_18, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = l_Lean_Server_FileWorker_setupFile___lambda__1___closed__2;
x_26 = lean_string_append(x_25, x_17);
lean_dec(x_17);
x_27 = l_Lean_Server_FileWorker_setupFile___lambda__1___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
x_30 = lean_string_append(x_28, x_29);
lean_dec(x_29);
x_31 = l_Lean_Server_FileWorker_setupFile___lambda__1___closed__4;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_ctor_get(x_9, 2);
lean_inc(x_33);
lean_dec(x_9);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___closed__1;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_36, x_10);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_17);
lean_dec(x_9);
x_38 = l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(x_10);
return x_38;
}
}
else
{
lean_object* x_39; 
lean_dec(x_17);
lean_dec(x_9);
x_39 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_10);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
x_41 = l_Lean_Server_FileWorker_setupFile___lambda__1___closed__5;
lean_inc(x_40);
x_42 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_41, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_42);
x_43 = l_Lean_Server_FileWorker_setupFile___lambda__1___closed__6;
x_44 = lean_string_append(x_43, x_17);
lean_dec(x_17);
x_45 = l_Lean_Server_FileWorker_setupFile___lambda__1___closed__7;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_string_append(x_46, x_40);
lean_dec(x_40);
x_48 = l_Lean_Server_FileWorker_setupFile___lambda__1___closed__4;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_ctor_get(x_9, 2);
lean_inc(x_50);
lean_dec(x_9);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_52 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_53, x_10);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_42, 0);
lean_inc(x_59);
lean_dec(x_42);
x_60 = l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_31_(x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_60);
x_61 = l_Lean_Server_FileWorker_setupFile___lambda__1___closed__6;
x_62 = lean_string_append(x_61, x_17);
lean_dec(x_17);
x_63 = l_Lean_Server_FileWorker_setupFile___lambda__1___closed__7;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_40);
lean_dec(x_40);
x_66 = l_Lean_Server_FileWorker_setupFile___lambda__1___closed__4;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_ctor_get(x_9, 2);
lean_inc(x_68);
lean_dec(x_9);
x_69 = lean_string_append(x_67, x_68);
lean_dec(x_68);
x_70 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___closed__1;
x_71 = lean_string_append(x_69, x_70);
x_72 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_71, x_10);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
return x_72;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_72);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_40);
lean_dec(x_17);
lean_dec(x_9);
x_77 = lean_ctor_get(x_60, 0);
lean_inc(x_77);
lean_dec(x_60);
x_78 = lean_get_prefix(x_10);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = l_Lean_initSearchPath(x_79, x_82, x_80);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_ctor_get(x_81, 2);
lean_inc(x_85);
x_86 = lean_array_get_size(x_85);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_dec_lt(x_87, x_86);
if (x_88 == 0)
{
lean_object* x_89; size_t x_90; size_t x_91; lean_object* x_92; 
lean_dec(x_86);
lean_dec(x_85);
x_89 = lean_ctor_get(x_81, 3);
lean_inc(x_89);
lean_dec(x_81);
x_90 = lean_array_size(x_89);
x_91 = 0;
x_92 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_setupFile___spec__1(x_90, x_91, x_89, x_84);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_77, 1);
lean_inc(x_95);
lean_dec(x_77);
x_96 = l_Lean_LeanOptions_toOptions(x_95);
x_97 = l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(x_96, x_93, x_94);
return x_97;
}
else
{
uint8_t x_98; 
lean_dec(x_77);
x_98 = !lean_is_exclusive(x_92);
if (x_98 == 0)
{
return x_92;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_92, 0);
x_100 = lean_ctor_get(x_92, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_92);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
x_102 = lean_nat_dec_le(x_86, x_86);
if (x_102 == 0)
{
lean_object* x_103; size_t x_104; size_t x_105; lean_object* x_106; 
lean_dec(x_86);
lean_dec(x_85);
x_103 = lean_ctor_get(x_81, 3);
lean_inc(x_103);
lean_dec(x_81);
x_104 = lean_array_size(x_103);
x_105 = 0;
x_106 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_setupFile___spec__1(x_104, x_105, x_103, x_84);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_77, 1);
lean_inc(x_109);
lean_dec(x_77);
x_110 = l_Lean_LeanOptions_toOptions(x_109);
x_111 = l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(x_110, x_107, x_108);
return x_111;
}
else
{
uint8_t x_112; 
lean_dec(x_77);
x_112 = !lean_is_exclusive(x_106);
if (x_112 == 0)
{
return x_106;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_106, 0);
x_114 = lean_ctor_get(x_106, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_106);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
size_t x_116; size_t x_117; lean_object* x_118; lean_object* x_119; 
x_116 = 0;
x_117 = lean_usize_of_nat(x_86);
lean_dec(x_86);
x_118 = lean_box(0);
x_119 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_setupFile___spec__2(x_85, x_116, x_117, x_118, x_84);
lean_dec(x_85);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; size_t x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_ctor_get(x_81, 3);
lean_inc(x_121);
lean_dec(x_81);
x_122 = lean_array_size(x_121);
x_123 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_setupFile___spec__1(x_122, x_116, x_121, x_120);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_77, 1);
lean_inc(x_126);
lean_dec(x_77);
x_127 = l_Lean_LeanOptions_toOptions(x_126);
x_128 = l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(x_127, x_124, x_125);
return x_128;
}
else
{
uint8_t x_129; 
lean_dec(x_77);
x_129 = !lean_is_exclusive(x_123);
if (x_129 == 0)
{
return x_123;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_123, 0);
x_131 = lean_ctor_get(x_123, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_123);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_81);
lean_dec(x_77);
x_133 = !lean_is_exclusive(x_119);
if (x_133 == 0)
{
return x_119;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_119, 0);
x_135 = lean_ctor_get(x_119, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_119);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_81);
lean_dec(x_77);
x_137 = !lean_is_exclusive(x_83);
if (x_137 == 0)
{
return x_83;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_83, 0);
x_139 = lean_ctor_get(x_83, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_83);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_77);
x_141 = !lean_is_exclusive(x_78);
if (x_141 == 0)
{
return x_78;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_78, 0);
x_143 = lean_ctor_get(x_78, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_78);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
}
}
}
else
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_8);
if (x_145 == 0)
{
return x_8;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_8, 0);
x_147 = lean_ctor_get(x_8, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_8);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = l_System_Uri_fileUriToPath_x3f(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Lean_determineLakePath(x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_System_FilePath_pathExists(x_14, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = l_Lean_Server_FileWorker_setupFile___lambda__1(x_1, x_14, x_12, x_2, x_3, x_26, x_25);
lean_dec(x_1);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_setupFile___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_setupFile___spec__1(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_setupFile___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_setupFile___spec__2(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_setupFile___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FileSetupInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_LakePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LoadDynlib(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_ServerTask(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_SetupFile(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FileSetupInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_LakePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LoadDynlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_ServerTask(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___closed__1 = _init_l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_runLakeSetupFile___spec__1___closed__1);
l_Lean_Server_FileWorker_runLakeSetupFile___lambda__1___closed__1 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___lambda__1___closed__1);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__1 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__1);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__2 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__2);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__3 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__3);
l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1 = _init_l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1);
l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__2 = _init_l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__2);
l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___closed__1 = _init_l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___closed__1);
l_Lean_Server_FileWorker_setupFile___lambda__1___closed__1 = _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___lambda__1___closed__1);
l_Lean_Server_FileWorker_setupFile___lambda__1___closed__2 = _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___lambda__1___closed__2);
l_Lean_Server_FileWorker_setupFile___lambda__1___closed__3 = _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___lambda__1___closed__3);
l_Lean_Server_FileWorker_setupFile___lambda__1___closed__4 = _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___lambda__1___closed__4);
l_Lean_Server_FileWorker_setupFile___lambda__1___closed__5 = _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___lambda__1___closed__5);
l_Lean_Server_FileWorker_setupFile___lambda__1___closed__6 = _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___lambda__1___closed__6);
l_Lean_Server_FileWorker_setupFile___lambda__1___closed__7 = _init_l_Lean_Server_FileWorker_setupFile___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___lambda__1___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
