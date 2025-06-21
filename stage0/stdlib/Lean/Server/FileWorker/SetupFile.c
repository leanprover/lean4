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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_determineLakePath(lean_object*);
static lean_object* l_Lean_Server_FileWorker_setupFile___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__0;
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_setupFile___closed__5;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_setupFile___closed__4;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_31_(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_runLakeSetupFile___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(lean_object*);
lean_object* lean_get_prefix(lean_object*);
lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_setupFile___closed__3;
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__5;
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__2;
lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__6;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_load_dynlib(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__1;
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___closed__0;
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__3;
static lean_object* l_Lean_Server_FileWorker_setupFile___closed__0;
static lean_object* l_Lean_Server_FileWorker_setupFile___closed__1;
static lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0(size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_realPathNormalized(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_io_prim_handle_get_line(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0;
x_11 = lean_string_dec_eq(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_6);
lean_inc(x_1);
lean_inc(x_8);
x_12 = lean_apply_2(x_1, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_3 = x_14;
x_4 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0;
x_23 = lean_string_dec_eq(x_20, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_inc(x_1);
lean_inc(x_20);
x_24 = lean_apply_2(x_1, x_20, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_string_append(x_3, x_20);
lean_dec(x_20);
x_3 = x_26;
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_1);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_30 = x_24;
} else {
 lean_dec_ref(x_24);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_20);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_4, x_3, x_8);
lean_inc(x_1);
x_10 = l_Lean_Name_toString(x_7, x_5, x_1);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_9, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_runLakeSetupFile___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_1 = lean_box(0);
x_2 = lean_box(2);
x_3 = lean_alloc_ctor(0, 0, 3);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, 0, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 1, x_5);
x_6 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 2, x_6);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("setup-file", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__2;
x_2 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--no-build", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__6() {
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
lean_object* x_7; lean_object* x_8; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_70 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_runLakeSetupFile___lam__0___boxed), 1, 0);
x_71 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__4;
x_72 = lean_array_push(x_71, x_3);
x_73 = lean_array_size(x_4);
x_74 = 0;
x_75 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0(x_70, x_73, x_74, x_4);
x_76 = l_Array_append___redArg(x_72, x_75);
lean_dec(x_75);
x_77 = lean_box(x_69);
if (lean_obj_tag(x_77) == 2)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__5;
x_79 = lean_array_push(x_76, x_78);
x_80 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__6;
x_81 = lean_array_push(x_79, x_80);
x_7 = x_81;
x_8 = x_6;
goto block_68;
}
else
{
lean_dec(x_77);
x_7 = x_76;
x_8 = x_6;
goto block_68;
}
block_68:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_9 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__0;
x_10 = lean_box(0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__1;
x_13 = lean_box(1);
x_14 = lean_box(0);
lean_inc(x_7);
lean_inc(x_2);
x_15 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_7);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_12);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_16);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 1, x_17);
lean_inc(x_15);
x_18 = lean_io_process_spawn(x_15, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0;
lean_inc(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed), 6, 5);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_7);
lean_closure_set(x_22, 3, x_19);
lean_closure_set(x_22, 4, x_21);
x_23 = l_Lean_Server_ServerTask_IO_asTask___redArg(x_22, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
x_27 = l_IO_FS_Handle_readToEnd(x_26, x_25);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_task_get_own(x_24);
x_31 = l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(x_30, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_io_process_child_wait(x_9, x_19, x_33);
lean_dec(x_19);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint32_t x_42; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_string_utf8_byte_size(x_28);
x_38 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_28, x_37, x_11);
x_39 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_28, x_38, x_37);
x_40 = lean_string_utf8_extract(x_28, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_28);
x_41 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_32);
x_42 = lean_unbox_uint32(x_36);
lean_dec(x_36);
lean_ctor_set_uint32(x_41, sizeof(void*)*3, x_42);
lean_ctor_set(x_34, 0, x_41);
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint32_t x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_string_utf8_byte_size(x_28);
x_46 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_28, x_45, x_11);
x_47 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_28, x_46, x_45);
x_48 = lean_string_utf8_extract(x_28, x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_28);
x_49 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_49, 0, x_15);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_32);
x_50 = lean_unbox_uint32(x_43);
lean_dec(x_43);
lean_ctor_set_uint32(x_49, sizeof(void*)*3, x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_15);
x_52 = !lean_is_exclusive(x_34);
if (x_52 == 0)
{
return x_34;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_34, 0);
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_34);
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
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_15);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_15);
x_60 = !lean_is_exclusive(x_27);
if (x_60 == 0)
{
return x_27;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_27, 0);
x_62 = lean_ctor_get(x_27, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_27);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_18);
if (x_64 == 0)
{
return x_18;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_18, 0);
x_66 = lean_ctor_get(x_18, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_18);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_runLakeSetupFile___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
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
static lean_object* _init_l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0;
x_2 = lean_box(0);
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0;
x_2 = lean_box(0);
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___closed__0;
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
x_4 = lean_box(0);
x_5 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = l_Lean_realPathNormalized(x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_12, x_2, x_9);
x_2 = x_14;
x_3 = x_15;
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
lean_dec(x_7);
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
return x_8;
}
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid output from `", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`:\n", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nstderr:\n", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` failed:\n", 10, 10);
return x_1;
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
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_determineLakePath(x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_System_FilePath_pathExists(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_10, x_8, x_2, x_3, x_18);
lean_dec(x_1);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint32_t x_42; uint8_t x_43; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get_uint32(x_21, sizeof(void*)*3);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 2);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 2);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l_Lean_Server_FileWorker_setupFile___closed__0;
x_30 = lean_array_to_list(x_28);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_30);
lean_ctor_set(x_12, 0, x_27);
x_31 = l_String_intercalate(x_29, x_12);
x_42 = 0;
x_43 = lean_uint32_dec_eq(x_24, x_42);
if (x_43 == 0)
{
uint32_t x_44; uint8_t x_45; 
x_44 = 2;
x_45 = lean_uint32_dec_eq(x_24, x_44);
if (x_45 == 0)
{
uint32_t x_46; uint8_t x_47; 
x_46 = 3;
x_47 = lean_uint32_dec_eq(x_24, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = l_Lean_Server_FileWorker_setupFile___closed__4;
x_49 = lean_string_append(x_48, x_31);
lean_dec(x_31);
x_50 = l_Lean_Server_FileWorker_setupFile___closed__5;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_25);
lean_dec(x_25);
x_53 = l_Lean_Server_FileWorker_setupFile___closed__3;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_string_append(x_54, x_26);
lean_dec(x_26);
x_56 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_55, x_23);
return x_56;
}
else
{
lean_object* x_57; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
x_57 = l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(x_23);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
x_58 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_23);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_inc(x_25);
x_59 = l_Lean_Json_parse(x_25);
if (lean_obj_tag(x_59) == 0)
{
lean_dec(x_59);
goto block_41;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_31_(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_dec(x_61);
goto block_41;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_get_prefix(x_23);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 3);
lean_inc(x_70);
lean_dec(x_64);
x_84 = l_Lean_initSearchPath(x_65, x_68, x_66);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_array_get_size(x_69);
x_88 = lean_nat_dec_lt(x_86, x_87);
if (x_88 == 0)
{
lean_dec(x_87);
lean_dec(x_69);
x_71 = x_85;
goto block_83;
}
else
{
uint8_t x_89; 
x_89 = lean_nat_dec_le(x_87, x_87);
if (x_89 == 0)
{
lean_dec(x_87);
lean_dec(x_69);
x_71 = x_85;
goto block_83;
}
else
{
lean_object* x_90; size_t x_91; size_t x_92; lean_object* x_93; 
x_90 = lean_box(0);
x_91 = 0;
x_92 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_93 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1(x_69, x_91, x_92, x_90, x_85);
lean_dec(x_69);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_71 = x_94;
goto block_83;
}
else
{
uint8_t x_95; 
lean_dec(x_70);
lean_dec(x_67);
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
return x_93;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_93, 0);
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_93);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
block_83:
{
size_t x_72; size_t x_73; lean_object* x_74; 
x_72 = lean_array_size(x_70);
x_73 = 0;
x_74 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0(x_72, x_73, x_70, x_71);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_LeanOptions_toOptions(x_67);
x_78 = l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(x_77, x_75, x_76);
return x_78;
}
else
{
uint8_t x_79; 
lean_dec(x_67);
x_79 = !lean_is_exclusive(x_74);
if (x_79 == 0)
{
return x_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_74, 0);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_74);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_62);
x_99 = !lean_is_exclusive(x_63);
if (x_99 == 0)
{
return x_63;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_63, 0);
x_101 = lean_ctor_get(x_63, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_63);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
block_41:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = l_Lean_Server_FileWorker_setupFile___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lean_Server_FileWorker_setupFile___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_25);
lean_dec(x_25);
x_37 = l_Lean_Server_FileWorker_setupFile___closed__3;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_string_append(x_38, x_26);
lean_dec(x_26);
x_40 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_39, x_23);
return x_40;
}
}
else
{
uint8_t x_103; 
lean_free_object(x_12);
x_103 = !lean_is_exclusive(x_20);
if (x_103 == 0)
{
return x_20;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_20, 0);
x_105 = lean_ctor_get(x_20, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_20);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_12, 1);
lean_inc(x_107);
lean_dec(x_12);
x_108 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_10, x_8, x_2, x_3, x_107);
lean_dec(x_1);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint32_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint32_t x_131; uint8_t x_132; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_ctor_get_uint32(x_109, sizeof(void*)*3);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 2);
lean_inc(x_114);
lean_dec(x_109);
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_110, 2);
lean_inc(x_116);
lean_dec(x_110);
x_117 = l_Lean_Server_FileWorker_setupFile___closed__0;
x_118 = lean_array_to_list(x_116);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_String_intercalate(x_117, x_119);
x_131 = 0;
x_132 = lean_uint32_dec_eq(x_112, x_131);
if (x_132 == 0)
{
uint32_t x_133; uint8_t x_134; 
x_133 = 2;
x_134 = lean_uint32_dec_eq(x_112, x_133);
if (x_134 == 0)
{
uint32_t x_135; uint8_t x_136; 
x_135 = 3;
x_136 = lean_uint32_dec_eq(x_112, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_137 = l_Lean_Server_FileWorker_setupFile___closed__4;
x_138 = lean_string_append(x_137, x_120);
lean_dec(x_120);
x_139 = l_Lean_Server_FileWorker_setupFile___closed__5;
x_140 = lean_string_append(x_138, x_139);
x_141 = lean_string_append(x_140, x_113);
lean_dec(x_113);
x_142 = l_Lean_Server_FileWorker_setupFile___closed__3;
x_143 = lean_string_append(x_141, x_142);
x_144 = lean_string_append(x_143, x_114);
lean_dec(x_114);
x_145 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_144, x_111);
return x_145;
}
else
{
lean_object* x_146; 
lean_dec(x_120);
lean_dec(x_114);
lean_dec(x_113);
x_146 = l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(x_111);
return x_146;
}
}
else
{
lean_object* x_147; 
lean_dec(x_120);
lean_dec(x_114);
lean_dec(x_113);
x_147 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_111);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_inc(x_113);
x_148 = l_Lean_Json_parse(x_113);
if (lean_obj_tag(x_148) == 0)
{
lean_dec(x_148);
goto block_130;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec(x_148);
x_150 = l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_31_(x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_dec(x_150);
goto block_130;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_120);
lean_dec(x_114);
lean_dec(x_113);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_get_prefix(x_111);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec(x_152);
x_156 = lean_ctor_get(x_151, 1);
lean_inc(x_156);
lean_dec(x_151);
x_157 = lean_ctor_get(x_153, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_153, 2);
lean_inc(x_158);
x_159 = lean_ctor_get(x_153, 3);
lean_inc(x_159);
lean_dec(x_153);
x_173 = l_Lean_initSearchPath(x_154, x_157, x_155);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_unsigned_to_nat(0u);
x_176 = lean_array_get_size(x_158);
x_177 = lean_nat_dec_lt(x_175, x_176);
if (x_177 == 0)
{
lean_dec(x_176);
lean_dec(x_158);
x_160 = x_174;
goto block_172;
}
else
{
uint8_t x_178; 
x_178 = lean_nat_dec_le(x_176, x_176);
if (x_178 == 0)
{
lean_dec(x_176);
lean_dec(x_158);
x_160 = x_174;
goto block_172;
}
else
{
lean_object* x_179; size_t x_180; size_t x_181; lean_object* x_182; 
x_179 = lean_box(0);
x_180 = 0;
x_181 = lean_usize_of_nat(x_176);
lean_dec(x_176);
x_182 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1(x_158, x_180, x_181, x_179, x_174);
lean_dec(x_158);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_160 = x_183;
goto block_172;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_159);
lean_dec(x_156);
x_184 = lean_ctor_get(x_182, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_186 = x_182;
} else {
 lean_dec_ref(x_182);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
}
block_172:
{
size_t x_161; size_t x_162; lean_object* x_163; 
x_161 = lean_array_size(x_159);
x_162 = 0;
x_163 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0(x_161, x_162, x_159, x_160);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_LeanOptions_toOptions(x_156);
x_167 = l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(x_166, x_164, x_165);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_156);
x_168 = lean_ctor_get(x_163, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_163, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_170 = x_163;
} else {
 lean_dec_ref(x_163);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_151);
x_188 = lean_ctor_get(x_152, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_152, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_190 = x_152;
} else {
 lean_dec_ref(x_152);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
}
block_130:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_121 = l_Lean_Server_FileWorker_setupFile___closed__1;
x_122 = lean_string_append(x_121, x_120);
lean_dec(x_120);
x_123 = l_Lean_Server_FileWorker_setupFile___closed__2;
x_124 = lean_string_append(x_122, x_123);
x_125 = lean_string_append(x_124, x_113);
lean_dec(x_113);
x_126 = l_Lean_Server_FileWorker_setupFile___closed__3;
x_127 = lean_string_append(x_125, x_126);
x_128 = lean_string_append(x_127, x_114);
lean_dec(x_114);
x_129 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_128, x_111);
return x_129;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_108, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_108, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_194 = x_108;
} else {
 lean_dec_ref(x_108);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_9);
if (x_196 == 0)
{
return x_9;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_9, 0);
x_198 = lean_ctor_get(x_9, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_9);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1(x_1, x_6, x_7, x_4, x_5);
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
l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0 = _init_l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__0 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__0);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__1 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__1);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__2 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__2);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__3 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__3);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__4 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__4);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__5 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__5);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__6 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__6);
l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0 = _init_l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0);
l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1 = _init_l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__1);
l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___closed__0 = _init_l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___closed__0);
l_Lean_Server_FileWorker_setupFile___closed__0 = _init_l_Lean_Server_FileWorker_setupFile___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___closed__0);
l_Lean_Server_FileWorker_setupFile___closed__1 = _init_l_Lean_Server_FileWorker_setupFile___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___closed__1);
l_Lean_Server_FileWorker_setupFile___closed__2 = _init_l_Lean_Server_FileWorker_setupFile___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___closed__2);
l_Lean_Server_FileWorker_setupFile___closed__3 = _init_l_Lean_Server_FileWorker_setupFile___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___closed__3);
l_Lean_Server_FileWorker_setupFile___closed__4 = _init_l_Lean_Server_FileWorker_setupFile___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___closed__4);
l_Lean_Server_FileWorker_setupFile___closed__5 = _init_l_Lean_Server_FileWorker_setupFile___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
