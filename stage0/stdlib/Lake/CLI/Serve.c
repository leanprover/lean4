// Lean compiler output
// Module: Lake.CLI.Serve
// Imports: Init Lake.Load Lake.Build Lake.Util.MainM Lean.Util.FileSetupInfo
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
static lean_object* l_Lake_setupFile___lambda__2___closed__1;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__6(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_Log_toString(lean_object*);
lean_object* l_Lake_Workspace_leanSrcPath(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_baseVars(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___lambda__1___closed__1;
LEAN_EXPORT uint32_t l_Lake_noConfigFileCode;
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__7(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_setupFile___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lake_serve___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___lambda__2___closed__2;
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__2;
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_invalidConfigEnvVar;
lean_object* l_Lake_Workspace_findModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_loadWorkspace(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__2;
lean_object* lean_get_stderr(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_setupFile___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_buildImportsAndDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__4(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___lambda__2___closed__3;
static lean_object* l_Lake_serve___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1___boxed__const__1;
lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_invalidConfigEnvVar___closed__1;
lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_124_(lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_MainM_instMonadLiftLogIO___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_IO_eprint___at_IO_eprintln___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_configFileExists(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_LeanOptions_fromOptions_x3f___spec__1(lean_object*, lean_object*, lean_object*);
static uint32_t _init_l_Lake_noConfigFileCode() {
_start:
{
uint32_t x_1; 
x_1 = 2;
return x_1;
}
}
static lean_object* _init_l_Lake_invalidConfigEnvVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LAKE_INVALID_CONFIG", 19);
return x_1;
}
}
static lean_object* _init_l_Lake_invalidConfigEnvVar() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_invalidConfigEnvVar___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_setupFile___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = l_Lean_RBNode_insert___at_Lean_LeanOptions_fromOptions_x3f___spec__1(x_4, x_7, x_8);
x_2 = x_10;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
x_9 = lean_get_stderr(x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lake_logToStream(x_8, x_10, x_1, x_11);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_13;
x_6 = x_14;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__4(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
x_9 = lean_get_stderr(x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lake_logToStream(x_8, x_10, x_1, x_11);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_13;
x_6 = x_14;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_String_toName(x_4);
lean_inc(x_1);
x_7 = l_Lake_Workspace_findModule_x3f(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_push(x_2, x_9);
x_2 = x_10;
x_3 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__6(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
x_9 = lean_get_stderr(x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lake_logToStream(x_8, x_10, x_1, x_11);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_13;
x_6 = x_14;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__7(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
x_9 = lean_get_stderr(x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lake_logToStream(x_8, x_10, x_1, x_11);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_13;
x_6 = x_14;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
}
static lean_object* _init_l_Lake_setupFile___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_setupFile___lambda__1___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___lambda__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_2);
x_43 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_124_(x_42);
x_44 = l_Lean_Json_compress(x_43);
x_45 = l_IO_println___at_Lean_instEval___spec__1(x_44, x_3);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lake_setupFile___lambda__1___closed__1;
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_4 = x_49;
x_5 = x_47;
goto block_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec(x_45);
x_52 = lean_io_error_to_string(x_50);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = l_Lake_setupFile___lambda__1___closed__1;
x_56 = lean_array_push(x_55, x_54);
x_57 = l_Lake_setupFile___lambda__1___closed__2;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_4 = x_58;
x_5 = x_51;
goto block_41;
}
block_41:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = lean_box(0);
x_17 = l_Array_foldlMUnsafe_fold___at_Lake_MainM_instMonadLiftLogIO___spec__1(x_7, x_14, x_15, x_16, x_5);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_6);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_array_get_size(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
x_26 = l_Lake_setupFile___lambda__1___boxed__const__1;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_23, x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
lean_dec(x_22);
x_29 = l_Lake_setupFile___lambda__1___boxed__const__1;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
return x_30;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_33 = lean_box(0);
x_34 = l_Array_foldlMUnsafe_fold___at_Lake_MainM_instMonadLiftLogIO___spec__1(x_22, x_31, x_32, x_33, x_5);
lean_dec(x_22);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = l_Lake_setupFile___lambda__1___boxed__const__1;
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = l_Lake_setupFile___lambda__1___boxed__const__1;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
}
}
}
static lean_object* _init_l_Lake_setupFile___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("build failed", 12);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_setupFile___lambda__2___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_setupFile___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___lambda__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = 0;
x_137 = l_Lake_setupFile___lambda__1___closed__1;
x_138 = l_Lake_loadWorkspace(x_1, x_136, x_137, x_8);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = lean_array_get_size(x_142);
x_144 = lean_unsigned_to_nat(0u);
x_145 = lean_nat_dec_lt(x_144, x_143);
if (x_145 == 0)
{
lean_dec(x_143);
lean_dec(x_142);
x_9 = x_141;
x_10 = x_140;
goto block_135;
}
else
{
uint8_t x_146; 
x_146 = lean_nat_dec_le(x_143, x_143);
if (x_146 == 0)
{
lean_dec(x_143);
lean_dec(x_142);
x_9 = x_141;
x_10 = x_140;
goto block_135;
}
else
{
size_t x_147; size_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = 0;
x_148 = lean_usize_of_nat(x_143);
lean_dec(x_143);
x_149 = lean_box(0);
x_150 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__6(x_6, x_142, x_147, x_148, x_149, x_140);
lean_dec(x_142);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_9 = x_141;
x_10 = x_151;
goto block_135;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_138);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_153 = lean_ctor_get(x_138, 1);
x_154 = lean_ctor_get(x_138, 0);
lean_dec(x_154);
x_155 = lean_ctor_get(x_139, 1);
lean_inc(x_155);
lean_dec(x_139);
x_156 = lean_array_get_size(x_155);
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_nat_dec_lt(x_157, x_156);
if (x_158 == 0)
{
lean_object* x_159; 
lean_dec(x_156);
lean_dec(x_155);
x_159 = l_Lake_setupFile___lambda__2___boxed__const__1;
lean_ctor_set_tag(x_138, 1);
lean_ctor_set(x_138, 0, x_159);
return x_138;
}
else
{
uint8_t x_160; 
x_160 = lean_nat_dec_le(x_156, x_156);
if (x_160 == 0)
{
lean_object* x_161; 
lean_dec(x_156);
lean_dec(x_155);
x_161 = l_Lake_setupFile___lambda__2___boxed__const__1;
lean_ctor_set_tag(x_138, 1);
lean_ctor_set(x_138, 0, x_161);
return x_138;
}
else
{
size_t x_162; size_t x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
lean_free_object(x_138);
x_162 = 0;
x_163 = lean_usize_of_nat(x_156);
lean_dec(x_156);
x_164 = lean_box(0);
x_165 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__7(x_6, x_155, x_162, x_163, x_164, x_153);
lean_dec(x_155);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_165, 0);
lean_dec(x_167);
x_168 = l_Lake_setupFile___lambda__2___boxed__const__1;
lean_ctor_set_tag(x_165, 1);
lean_ctor_set(x_165, 0, x_168);
return x_165;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_165, 1);
lean_inc(x_169);
lean_dec(x_165);
x_170 = l_Lake_setupFile___lambda__2___boxed__const__1;
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_172 = lean_ctor_get(x_138, 1);
lean_inc(x_172);
lean_dec(x_138);
x_173 = lean_ctor_get(x_139, 1);
lean_inc(x_173);
lean_dec(x_139);
x_174 = lean_array_get_size(x_173);
x_175 = lean_unsigned_to_nat(0u);
x_176 = lean_nat_dec_lt(x_175, x_174);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_174);
lean_dec(x_173);
x_177 = l_Lake_setupFile___lambda__2___boxed__const__1;
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_172);
return x_178;
}
else
{
uint8_t x_179; 
x_179 = lean_nat_dec_le(x_174, x_174);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_174);
lean_dec(x_173);
x_180 = l_Lake_setupFile___lambda__2___boxed__const__1;
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_172);
return x_181;
}
else
{
size_t x_182; size_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_182 = 0;
x_183 = lean_usize_of_nat(x_174);
lean_dec(x_174);
x_184 = lean_box(0);
x_185 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__7(x_6, x_173, x_182, x_183, x_184, x_172);
lean_dec(x_173);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_187 = x_185;
} else {
 lean_dec_ref(x_185);
 x_187 = lean_box(0);
}
x_188 = l_Lake_setupFile___lambda__2___boxed__const__1;
if (lean_is_scalar(x_187)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_187;
 lean_ctor_set_tag(x_189, 1);
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_186);
return x_189;
}
}
}
}
block_135:
{
lean_object* x_11; lean_object* x_12; lean_object* x_73; lean_object* x_74; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_121; 
x_106 = l_Lake_setupFile___lambda__1___closed__1;
lean_inc(x_9);
x_107 = l_List_foldl___at_Lake_setupFile___spec__5(x_9, x_106, x_4);
x_108 = lean_alloc_closure((void*)(l_Lake_buildImportsAndDeps), 7, 1);
lean_closure_set(x_108, 0, x_107);
lean_inc(x_9);
x_121 = l_Lake_Workspace_runFetchM___rarg(x_9, x_108, x_5, x_10);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_io_wait(x_122, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_109 = x_129;
x_110 = x_127;
goto block_120;
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_125);
x_130 = lean_ctor_get(x_124, 1);
lean_inc(x_130);
lean_dec(x_124);
x_131 = l_Lake_setupFile___lambda__2___closed__3;
x_109 = x_131;
x_110 = x_130;
goto block_120;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_121, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_121, 1);
lean_inc(x_133);
lean_dec(x_121);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_132);
x_109 = x_134;
x_110 = x_133;
goto block_120;
}
block_72:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_53; lean_object* x_54; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_inc(x_9);
x_13 = l_Lake_Workspace_leanPath(x_9);
lean_inc(x_9);
x_14 = l_Lake_Workspace_leanSrcPath(x_9);
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_11);
x_67 = l_Lean_searchModuleNameOfFileName(x_2, x_14, x_12);
lean_dec(x_14);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lake_setupFile___lambda__1___closed__1;
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_53 = x_71;
x_54 = x_69;
goto block_66;
block_52:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = l_Lake_setupFile___lambda__1(x_15, x_18, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lake_Workspace_findModule_x3f(x_20, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lake_setupFile___lambda__1(x_15, x_22, x_17);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 4);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Array_append___rarg(x_29, x_30);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = l_Array_append___rarg(x_31, x_34);
x_36 = lean_ctor_get(x_33, 4);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Array_append___rarg(x_35, x_36);
x_38 = lean_array_get_size(x_37);
x_39 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_40 = 0;
x_41 = l_Array_mapMUnsafe_map___at_Lake_setupFile___spec__1(x_39, x_40, x_37);
x_42 = lean_box(0);
x_43 = lean_array_get_size(x_41);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_lt(x_44, x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_41);
x_46 = l_Lake_setupFile___lambda__1(x_15, x_42, x_17);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_43, x_43);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_43);
lean_dec(x_41);
x_48 = l_Lake_setupFile___lambda__1(x_15, x_42, x_17);
return x_48;
}
else
{
size_t x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_50 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(x_41, x_40, x_49, x_42);
lean_dec(x_41);
x_51 = l_Lake_setupFile___lambda__1(x_15, x_50, x_17);
return x_51;
}
}
}
}
}
block_66:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_array_get_size(x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_lt(x_58, x_57);
if (x_59 == 0)
{
lean_dec(x_57);
lean_dec(x_56);
x_16 = x_55;
x_17 = x_54;
goto block_52;
}
else
{
uint8_t x_60; 
x_60 = lean_nat_dec_le(x_57, x_57);
if (x_60 == 0)
{
lean_dec(x_57);
lean_dec(x_56);
x_16 = x_55;
x_17 = x_54;
goto block_52;
}
else
{
size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = 0;
x_62 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_63 = lean_box(0);
x_64 = l_Array_foldlMUnsafe_fold___at_Lake_MainM_instMonadLiftLogIO___spec__1(x_56, x_61, x_62, x_63, x_54);
lean_dec(x_56);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_16 = x_55;
x_17 = x_65;
goto block_52;
}
}
}
}
block_105:
{
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_array_get_size(x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_lt(x_78, x_77);
if (x_79 == 0)
{
lean_dec(x_77);
lean_dec(x_76);
x_11 = x_75;
x_12 = x_74;
goto block_72;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_77, x_77);
if (x_80 == 0)
{
lean_dec(x_77);
lean_dec(x_76);
x_11 = x_75;
x_12 = x_74;
goto block_72;
}
else
{
size_t x_81; size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = 0;
x_82 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_83 = lean_box(0);
x_84 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(x_6, x_76, x_81, x_82, x_83, x_74);
lean_dec(x_76);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_11 = x_75;
x_12 = x_85;
goto block_72;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_9);
lean_dec(x_2);
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
x_87 = lean_array_get_size(x_86);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_dec_lt(x_88, x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_87);
lean_dec(x_86);
x_90 = l_Lake_setupFile___lambda__2___boxed__const__1;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_74);
return x_91;
}
else
{
uint8_t x_92; 
x_92 = lean_nat_dec_le(x_87, x_87);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_87);
lean_dec(x_86);
x_93 = l_Lake_setupFile___lambda__2___boxed__const__1;
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_74);
return x_94;
}
else
{
size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_95 = 0;
x_96 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_97 = lean_box(0);
x_98 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__4(x_6, x_86, x_95, x_96, x_97, x_74);
lean_dec(x_86);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
x_101 = l_Lake_setupFile___lambda__2___boxed__const__1;
lean_ctor_set_tag(x_98, 1);
lean_ctor_set(x_98, 0, x_101);
return x_98;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_dec(x_98);
x_103 = l_Lake_setupFile___lambda__2___boxed__const__1;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
}
}
block_120:
{
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_io_error_to_string(x_111);
x_113 = 3;
x_114 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_113);
x_115 = lean_array_push(x_106, x_114);
x_116 = l_Lake_setupFile___lambda__1___closed__2;
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_73 = x_117;
x_74 = x_110;
goto block_105;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_109, 0);
lean_inc(x_118);
lean_dec(x_109);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_106);
x_73 = x_119;
x_74 = x_110;
goto block_105;
}
}
}
}
}
static lean_object* _init_l_Lake_setupFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Invalid Lake configuration.  Please restart the server after fixing the Lake configuration file.", 96);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = l_Lake_noConfigFileCode;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_29; lean_object* x_46; lean_object* x_47; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 2);
lean_inc(x_79);
x_80 = l_System_FilePath_join(x_78, x_79);
x_81 = lean_ctor_get(x_1, 3);
lean_inc(x_81);
x_82 = l_System_FilePath_join(x_80, x_81);
x_83 = l_Lake_configFileExists(x_82, x_6);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
uint8_t x_86; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_83, 0);
lean_dec(x_87);
x_88 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_83, 1);
lean_ctor_set(x_83, 0, x_88);
return x_83;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_90 = l_Lake_setupFile___boxed__const__2;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_83, 1);
lean_inc(x_92);
lean_dec(x_83);
x_93 = l_Lake_invalidConfigEnvVar;
x_94 = lean_io_getenv(x_93, x_92);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_box(0);
x_98 = l_Lake_setupFile___lambda__2(x_1, x_2, x_5, x_3, x_4, x_5, x_97, x_96);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_dec(x_94);
x_100 = lean_ctor_get(x_95, 0);
lean_inc(x_100);
lean_dec(x_95);
x_101 = l_IO_eprint___at_IO_eprintln___spec__1(x_100, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lake_setupFile___lambda__1___closed__1;
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
x_46 = x_105;
x_47 = x_103;
goto block_77;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_dec(x_101);
x_108 = lean_io_error_to_string(x_106);
x_109 = 3;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
x_111 = l_Lake_setupFile___lambda__1___closed__1;
x_112 = lean_array_push(x_111, x_110);
x_113 = l_Lake_setupFile___lambda__1___closed__2;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_46 = x_114;
x_47 = x_107;
goto block_77;
}
}
}
block_28:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
x_13 = l_Lake_setupFile___boxed__const__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_10, x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
x_16 = l_Lake_setupFile___boxed__const__1;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = l_Array_foldlMUnsafe_fold___at_Lake_MainM_instMonadLiftLogIO___spec__1(x_9, x_18, x_19, x_20, x_8);
lean_dec(x_9);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lake_setupFile___boxed__const__1;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
}
block_45:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lake_setupFile___closed__1;
x_31 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_30, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lake_setupFile___lambda__1___closed__1;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_7 = x_35;
x_8 = x_33;
goto block_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_io_error_to_string(x_36);
x_39 = 3;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = l_Lake_setupFile___lambda__1___closed__1;
x_42 = lean_array_push(x_41, x_40);
x_43 = l_Lake_setupFile___lambda__1___closed__2;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_7 = x_44;
x_8 = x_37;
goto block_28;
}
}
block_77:
{
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_array_get_size(x_48);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_lt(x_50, x_49);
if (x_51 == 0)
{
lean_dec(x_49);
lean_dec(x_48);
x_29 = x_47;
goto block_45;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_49, x_49);
if (x_52 == 0)
{
lean_dec(x_49);
lean_dec(x_48);
x_29 = x_47;
goto block_45;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = 0;
x_54 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_55 = lean_box(0);
x_56 = l_Array_foldlMUnsafe_fold___at_Lake_MainM_instMonadLiftLogIO___spec__1(x_48, x_53, x_54, x_55, x_47);
lean_dec(x_48);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_29 = x_57;
goto block_45;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_46, 1);
lean_inc(x_58);
lean_dec(x_46);
x_59 = lean_array_get_size(x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_lt(x_60, x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_59);
lean_dec(x_58);
x_62 = l_Lake_setupFile___boxed__const__1;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_47);
return x_63;
}
else
{
uint8_t x_64; 
x_64 = lean_nat_dec_le(x_59, x_59);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_59);
lean_dec(x_58);
x_65 = l_Lake_setupFile___boxed__const__1;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_47);
return x_66;
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = 0;
x_68 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_69 = lean_box(0);
x_70 = l_Array_foldlMUnsafe_fold___at_Lake_MainM_instMonadLiftLogIO___spec__1(x_58, x_67, x_68, x_69, x_47);
lean_dec(x_58);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
x_73 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 0, x_73);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
x_75 = l_Lake_setupFile___boxed__const__1;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_setupFile___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_setupFile___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(x_7, x_2, x_8, x_9, x_5, x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__4(x_7, x_2, x_8, x_9, x_5, x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__6(x_7, x_2, x_8, x_9, x_5, x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__7(x_7, x_2, x_8, x_9, x_5, x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lake_setupFile___lambda__2(x_1, x_2, x_9, x_4, x_5, x_10, x_7, x_8);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lake_setupFile(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_get_stderr(x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = l_Lake_logToStream(x_7, x_9, x_11, x_10);
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
x_5 = x_14;
goto _start;
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
static lean_object* _init_l_Lake_serve___lambda__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_serve___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_serve___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--server", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_serve___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_serve___lambda__1___closed__2;
x_2 = l_Lake_serve___lambda__1___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_8, 7);
x_10 = l_Lake_serve___lambda__1___closed__4;
x_11 = l_Array_append___rarg(x_10, x_6);
x_12 = l_Array_append___rarg(x_11, x_2);
x_13 = lean_box(0);
x_14 = l_Lake_serve___lambda__1___closed__1;
x_15 = 0;
lean_inc(x_9);
x_16 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_5);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_15);
x_17 = lean_io_process_spawn(x_16, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_io_process_child_wait(x_14, x_18, x_19);
lean_dec(x_18);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lake_serve___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("warning: package configuration has errors, falling back to plain `lean --server`", 80);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_serve(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = 0;
x_171 = l_Lake_setupFile___lambda__1___closed__1;
lean_inc(x_1);
x_172 = l_Lake_loadWorkspace(x_1, x_170, x_171, x_3);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec(x_173);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_175);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
x_4 = x_178;
x_5 = x_174;
goto block_169;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
lean_dec(x_172);
x_180 = lean_ctor_get(x_173, 1);
lean_inc(x_180);
lean_dec(x_173);
x_181 = lean_box(0);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
x_4 = x_182;
x_5 = x_179;
goto block_169;
}
block_169:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_dec(x_9);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lake_serve___closed__1;
x_13 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_12, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = l_Lake_Env_baseVars(x_15);
x_17 = l_Lake_Log_toString(x_8);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_4, 0, x_19);
x_20 = lean_array_push(x_16, x_4);
x_21 = l_Lake_setupFile___lambda__1___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lake_serve___lambda__1(x_1, x_2, x_22, x_14);
lean_dec(x_1);
return x_23;
}
else
{
uint8_t x_24; 
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
lean_dec(x_7);
lean_inc(x_28);
x_29 = l_Lake_Workspace_augmentedEnvVars(x_28);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 6);
lean_inc(x_32);
lean_dec(x_31);
lean_ctor_set(x_4, 1, x_32);
lean_ctor_set(x_4, 0, x_29);
x_33 = l_Lake_serve___lambda__1(x_1, x_2, x_4, x_5);
lean_dec(x_1);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_9, x_9);
if (x_34 == 0)
{
lean_dec(x_9);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lake_serve___closed__1;
x_36 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_35, x_5);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = l_Lake_Env_baseVars(x_38);
x_40 = l_Lake_Log_toString(x_8);
lean_dec(x_8);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_4, 1, x_41);
lean_ctor_set(x_4, 0, x_42);
x_43 = lean_array_push(x_39, x_4);
x_44 = l_Lake_setupFile___lambda__1___closed__1;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lake_serve___lambda__1(x_1, x_2, x_45, x_37);
lean_dec(x_1);
return x_46;
}
else
{
uint8_t x_47; 
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_36);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_8);
x_51 = lean_ctor_get(x_7, 0);
lean_inc(x_51);
lean_dec(x_7);
lean_inc(x_51);
x_52 = l_Lake_Workspace_augmentedEnvVars(x_51);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_53, 2);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 6);
lean_inc(x_55);
lean_dec(x_54);
lean_ctor_set(x_4, 1, x_55);
lean_ctor_set(x_4, 0, x_52);
x_56 = l_Lake_serve___lambda__1(x_1, x_2, x_4, x_5);
lean_dec(x_1);
return x_56;
}
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_59 = lean_box(0);
x_60 = l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(x_8, x_57, x_58, x_59, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lake_serve___closed__1;
x_63 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_62, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
x_66 = l_Lake_Env_baseVars(x_65);
x_67 = l_Lake_Log_toString(x_8);
lean_dec(x_8);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_4, 1, x_68);
lean_ctor_set(x_4, 0, x_69);
x_70 = lean_array_push(x_66, x_4);
x_71 = l_Lake_setupFile___lambda__1___closed__1;
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lake_serve___lambda__1(x_1, x_2, x_72, x_64);
lean_dec(x_1);
return x_73;
}
else
{
uint8_t x_74; 
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_63);
if (x_74 == 0)
{
return x_63;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_63, 0);
x_76 = lean_ctor_get(x_63, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_63);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_8);
x_78 = lean_ctor_get(x_60, 1);
lean_inc(x_78);
lean_dec(x_60);
x_79 = lean_ctor_get(x_7, 0);
lean_inc(x_79);
lean_dec(x_7);
lean_inc(x_79);
x_80 = l_Lake_Workspace_augmentedEnvVars(x_79);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 2);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get(x_82, 6);
lean_inc(x_83);
lean_dec(x_82);
lean_ctor_set(x_4, 1, x_83);
lean_ctor_set(x_4, 0, x_80);
x_84 = l_Lake_serve___lambda__1(x_1, x_2, x_4, x_78);
lean_dec(x_1);
return x_84;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_4, 0);
x_86 = lean_ctor_get(x_4, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_4);
x_87 = lean_array_get_size(x_86);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_dec_lt(x_88, x_87);
if (x_89 == 0)
{
lean_dec(x_87);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = l_Lake_serve___closed__1;
x_91 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_90, x_5);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_ctor_get(x_1, 0);
lean_inc(x_93);
x_94 = l_Lake_Env_baseVars(x_93);
x_95 = l_Lake_Log_toString(x_86);
lean_dec(x_86);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l_Lake_invalidConfigEnvVar;
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_array_push(x_94, x_98);
x_100 = l_Lake_setupFile___lambda__1___closed__1;
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lake_serve___lambda__1(x_1, x_2, x_101, x_92);
lean_dec(x_1);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_86);
lean_dec(x_2);
lean_dec(x_1);
x_103 = lean_ctor_get(x_91, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_91, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_105 = x_91;
} else {
 lean_dec_ref(x_91);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_86);
x_107 = lean_ctor_get(x_85, 0);
lean_inc(x_107);
lean_dec(x_85);
lean_inc(x_107);
x_108 = l_Lake_Workspace_augmentedEnvVars(x_107);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_109, 2);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_ctor_get(x_110, 6);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lake_serve___lambda__1(x_1, x_2, x_112, x_5);
lean_dec(x_1);
return x_113;
}
}
else
{
uint8_t x_114; 
x_114 = lean_nat_dec_le(x_87, x_87);
if (x_114 == 0)
{
lean_dec(x_87);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = l_Lake_serve___closed__1;
x_116 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_115, x_5);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_ctor_get(x_1, 0);
lean_inc(x_118);
x_119 = l_Lake_Env_baseVars(x_118);
x_120 = l_Lake_Log_toString(x_86);
lean_dec(x_86);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = l_Lake_invalidConfigEnvVar;
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_array_push(x_119, x_123);
x_125 = l_Lake_setupFile___lambda__1___closed__1;
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lake_serve___lambda__1(x_1, x_2, x_126, x_117);
lean_dec(x_1);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_86);
lean_dec(x_2);
lean_dec(x_1);
x_128 = lean_ctor_get(x_116, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_116, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_130 = x_116;
} else {
 lean_dec_ref(x_116);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_86);
x_132 = lean_ctor_get(x_85, 0);
lean_inc(x_132);
lean_dec(x_85);
lean_inc(x_132);
x_133 = l_Lake_Workspace_augmentedEnvVars(x_132);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_134, 2);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_ctor_get(x_135, 6);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lake_serve___lambda__1(x_1, x_2, x_137, x_5);
lean_dec(x_1);
return x_138;
}
}
else
{
size_t x_139; size_t x_140; lean_object* x_141; lean_object* x_142; 
x_139 = 0;
x_140 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_141 = lean_box(0);
x_142 = l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(x_86, x_139, x_140, x_141, x_5);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = l_Lake_serve___closed__1;
x_145 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_144, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_ctor_get(x_1, 0);
lean_inc(x_147);
x_148 = l_Lake_Env_baseVars(x_147);
x_149 = l_Lake_Log_toString(x_86);
lean_dec(x_86);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = l_Lake_invalidConfigEnvVar;
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = lean_array_push(x_148, x_152);
x_154 = l_Lake_setupFile___lambda__1___closed__1;
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lake_serve___lambda__1(x_1, x_2, x_155, x_146);
lean_dec(x_1);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_86);
lean_dec(x_2);
lean_dec(x_1);
x_157 = lean_ctor_get(x_145, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_145, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_159 = x_145;
} else {
 lean_dec_ref(x_145);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_86);
x_161 = lean_ctor_get(x_142, 1);
lean_inc(x_161);
lean_dec(x_142);
x_162 = lean_ctor_get(x_85, 0);
lean_inc(x_162);
lean_dec(x_85);
lean_inc(x_162);
x_163 = l_Lake_Workspace_augmentedEnvVars(x_162);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_164, 2);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_ctor_get(x_165, 6);
lean_inc(x_166);
lean_dec(x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lake_serve___lambda__1(x_1, x_2, x_167, x_161);
lean_dec(x_1);
return x_168;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_serve___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_MainM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FileSetupInfo(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Serve(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_MainM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FileSetupInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_noConfigFileCode = _init_l_Lake_noConfigFileCode();
l_Lake_invalidConfigEnvVar___closed__1 = _init_l_Lake_invalidConfigEnvVar___closed__1();
lean_mark_persistent(l_Lake_invalidConfigEnvVar___closed__1);
l_Lake_invalidConfigEnvVar = _init_l_Lake_invalidConfigEnvVar();
lean_mark_persistent(l_Lake_invalidConfigEnvVar);
l_Lake_setupFile___lambda__1___closed__1 = _init_l_Lake_setupFile___lambda__1___closed__1();
lean_mark_persistent(l_Lake_setupFile___lambda__1___closed__1);
l_Lake_setupFile___lambda__1___closed__2 = _init_l_Lake_setupFile___lambda__1___closed__2();
lean_mark_persistent(l_Lake_setupFile___lambda__1___closed__2);
l_Lake_setupFile___lambda__1___boxed__const__1 = _init_l_Lake_setupFile___lambda__1___boxed__const__1();
lean_mark_persistent(l_Lake_setupFile___lambda__1___boxed__const__1);
l_Lake_setupFile___lambda__2___closed__1 = _init_l_Lake_setupFile___lambda__2___closed__1();
lean_mark_persistent(l_Lake_setupFile___lambda__2___closed__1);
l_Lake_setupFile___lambda__2___closed__2 = _init_l_Lake_setupFile___lambda__2___closed__2();
lean_mark_persistent(l_Lake_setupFile___lambda__2___closed__2);
l_Lake_setupFile___lambda__2___closed__3 = _init_l_Lake_setupFile___lambda__2___closed__3();
lean_mark_persistent(l_Lake_setupFile___lambda__2___closed__3);
l_Lake_setupFile___lambda__2___boxed__const__1 = _init_l_Lake_setupFile___lambda__2___boxed__const__1();
lean_mark_persistent(l_Lake_setupFile___lambda__2___boxed__const__1);
l_Lake_setupFile___closed__1 = _init_l_Lake_setupFile___closed__1();
lean_mark_persistent(l_Lake_setupFile___closed__1);
l_Lake_setupFile___boxed__const__1 = _init_l_Lake_setupFile___boxed__const__1();
lean_mark_persistent(l_Lake_setupFile___boxed__const__1);
l_Lake_setupFile___boxed__const__2 = _init_l_Lake_setupFile___boxed__const__2();
lean_mark_persistent(l_Lake_setupFile___boxed__const__2);
l_Lake_serve___lambda__1___closed__1 = _init_l_Lake_serve___lambda__1___closed__1();
lean_mark_persistent(l_Lake_serve___lambda__1___closed__1);
l_Lake_serve___lambda__1___closed__2 = _init_l_Lake_serve___lambda__1___closed__2();
lean_mark_persistent(l_Lake_serve___lambda__1___closed__2);
l_Lake_serve___lambda__1___closed__3 = _init_l_Lake_serve___lambda__1___closed__3();
lean_mark_persistent(l_Lake_serve___lambda__1___closed__3);
l_Lake_serve___lambda__1___closed__4 = _init_l_Lake_serve___lambda__1___closed__4();
lean_mark_persistent(l_Lake_serve___lambda__1___closed__4);
l_Lake_serve___closed__1 = _init_l_Lake_serve___closed__1();
lean_mark_persistent(l_Lake_serve___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
