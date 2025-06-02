// Lean compiler output
// Module: Lake.CLI.Serve
// Imports: Lake.Load Lake.Build Lake.Util.MainM Lean.Util.FileSetupInfo
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
static lean_object* l_Lake_setupFile___closed__5;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_Log_toString(lean_object*);
static lean_object* l_Lake_setupFile___closed__9;
static lean_object* l_Lake_setupFile___closed__4;
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanSrcPath(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_Job_renew___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Env_leanSrcPath(lean_object*);
extern lean_object* l_Lake_Module_depsFacet;
lean_object* l_Lake_Env_baseVars(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT uint32_t l_Lake_noConfigFileCode;
LEAN_EXPORT uint8_t l_Lake_setupFile___lambda__1(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
static lean_object* l_Lake_setupFile___closed__3;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_resolvePath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___at_Lake_setupFile___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__1;
lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l___private_Lake_Config_LeanConfig_0__Lake_ordBuildType____x40_Lake_Config_LeanConfig___hyg_266_(uint8_t, uint8_t);
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__2;
lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_invalidConfigEnvVar;
lean_object* l_Lake_Workspace_findModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanPath(lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lake_BuildType_leanOptions(uint8_t);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_buildImportsAndDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___rarg(lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__3;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lake_ensureJob___at_Lake_Module_recBuildDeps___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___closed__2;
static lean_object* l_Lake_setupFile___closed__7;
lean_object* l_IO_println___at_Lean_Environment_displayStats___spec__3(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__1;
static lean_object* l_Lake_invalidConfigEnvVar___closed__1;
static lean_object* l_Lake_setupFile___closed__8;
lean_object* l_String_toName(lean_object*);
lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LoggerIO_captureLog___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___at_Lake_setupFile___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_leanPath(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_setupFile___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___closed__6;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_IO_eprint___at_IO_eprintln___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lake_realConfigFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1___boxed(lean_object*);
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
x_1 = lean_mk_string_unchecked("LAKE_INVALID_CONFIG", 19, 19);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_Lake_Workspace_leanPath(x_1);
x_4 = l_Lake_Workspace_leanSrcPath(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_array_size(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1(x_6, x_7, x_5);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_array_size(x_9);
x_11 = l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1(x_10, x_7, x_9);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
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
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___at_Lake_setupFile___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = l_Lake_ensureJob___at_Lake_Module_recBuildDeps___spec__17(x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_17 = lean_ctor_get(x_12, 2);
lean_dec(x_17);
lean_ctor_set(x_12, 2, x_1);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_3);
x_18 = lean_ctor_get(x_7, 3);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_st_ref_take(x_18, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_12);
x_22 = l_Lake_Job_toOpaque___rarg(x_12);
x_23 = lean_array_push(x_20, x_22);
x_24 = lean_st_ref_set(x_18, x_23, x_21);
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = l_Lake_Job_renew___rarg(x_12);
lean_ctor_set(x_11, 0, x_27);
lean_ctor_set(x_24, 0, x_11);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Lake_Job_renew___rarg(x_12);
lean_ctor_set(x_11, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_1);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_3);
x_34 = lean_ctor_get(x_7, 3);
lean_inc(x_34);
lean_dec(x_7);
x_35 = lean_st_ref_take(x_34, x_13);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_33);
x_38 = l_Lake_Job_toOpaque___rarg(x_33);
x_39 = lean_array_push(x_36, x_38);
x_40 = lean_st_ref_set(x_34, x_39, x_37);
lean_dec(x_34);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = l_Lake_Job_renew___rarg(x_33);
lean_ctor_set(x_11, 0, x_43);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_11);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_dec(x_11);
x_46 = lean_ctor_get(x_12, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_48 = x_12;
} else {
 lean_dec_ref(x_12);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 3, 1);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_1);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_3);
x_50 = lean_ctor_get(x_7, 3);
lean_inc(x_50);
lean_dec(x_7);
x_51 = lean_st_ref_take(x_50, x_13);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_49);
x_54 = l_Lake_Job_toOpaque___rarg(x_49);
x_55 = lean_array_push(x_52, x_54);
x_56 = lean_st_ref_set(x_50, x_55, x_53);
lean_dec(x_50);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = l_Lake_Job_renew___rarg(x_49);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_45);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_7);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_10);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_10, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_11);
if (x_64 == 0)
{
return x_10;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_11, 0);
x_66 = lean_ctor_get(x_11, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_11);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_10, 0, x_67);
return x_10;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_10, 1);
lean_inc(x_68);
lean_dec(x_10);
x_69 = lean_ctor_get(x_11, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_11, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_71 = x_11;
} else {
 lean_dec_ref(x_11);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_7);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_10);
if (x_74 == 0)
{
return x_10;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_10, 0);
x_76 = lean_ctor_get(x_10, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_10);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_4, x_7, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Lake_setupFile___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_logToStream(x_4, x_1, x_2, x_3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_setupFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to load workspace", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_setupFile___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_setupFile___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_setupFile___closed__4;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("setup (", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to configure the Lake workspace. Please restart the server after fixing the error above.", 95, 95);
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
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_22; uint8_t x_23; 
x_22 = l_Lake_resolvePath(x_2, x_5);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_285 = lean_ctor_get(x_1, 6);
lean_inc(x_285);
x_286 = l_Lake_realConfigFile(x_285, x_25);
x_287 = !lean_is_exclusive(x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_288 = lean_ctor_get(x_286, 0);
x_289 = lean_ctor_get(x_286, 1);
x_290 = lean_string_utf8_byte_size(x_288);
x_291 = lean_unsigned_to_nat(0u);
x_292 = lean_nat_dec_eq(x_290, x_291);
lean_dec(x_290);
if (x_292 == 0)
{
uint8_t x_293; 
lean_free_object(x_286);
x_293 = lean_string_dec_eq(x_288, x_24);
lean_dec(x_288);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_free_object(x_22);
x_294 = l_Lake_invalidConfigEnvVar;
x_295 = lean_io_getenv(x_294, x_289);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; uint8_t x_298; uint8_t x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_299 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
x_300 = lean_box(1);
x_301 = l_Lake_OutStream_get(x_300, x_297);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
lean_inc(x_302);
x_304 = l_Lake_AnsiMode_isEnabled(x_302, x_299, x_303);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_box(x_298);
x_308 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__2___boxed), 5, 3);
lean_closure_set(x_308, 0, x_302);
lean_closure_set(x_308, 1, x_307);
lean_closure_set(x_308, 2, x_305);
x_309 = l_Lake_loadWorkspace(x_1, x_308, x_306);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_310);
x_26 = x_312;
x_27 = x_311;
goto block_284;
}
else
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_309, 1);
lean_inc(x_313);
lean_dec(x_309);
x_314 = lean_box(0);
x_26 = x_314;
x_27 = x_313;
goto block_284;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_315 = lean_ctor_get(x_295, 1);
lean_inc(x_315);
lean_dec(x_295);
x_316 = lean_ctor_get(x_296, 0);
lean_inc(x_316);
lean_dec(x_296);
x_317 = l_IO_eprint___at_IO_eprintln___spec__1(x_316, x_315);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
lean_dec(x_317);
x_319 = l_Lake_setupFile___closed__9;
x_320 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_319, x_318);
if (lean_obj_tag(x_320) == 0)
{
uint8_t x_321; 
x_321 = !lean_is_exclusive(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_320, 0);
lean_dec(x_322);
x_323 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_320, 1);
lean_ctor_set(x_320, 0, x_323);
return x_320;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_320, 1);
lean_inc(x_324);
lean_dec(x_320);
x_325 = l_Lake_setupFile___boxed__const__1;
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; uint8_t x_334; lean_object* x_335; uint8_t x_336; 
x_327 = lean_ctor_get(x_320, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_320, 1);
lean_inc(x_328);
lean_dec(x_320);
x_329 = lean_io_error_to_string(x_327);
x_330 = 3;
x_331 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set_uint8(x_331, sizeof(void*)*1, x_330);
x_332 = lean_box(1);
x_333 = 1;
x_334 = 0;
x_335 = l_Lake_OutStream_logEntry(x_332, x_331, x_333, x_334, x_328);
lean_dec(x_331);
x_336 = !lean_is_exclusive(x_335);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_335, 0);
lean_dec(x_337);
x_338 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_335, 1);
lean_ctor_set(x_335, 0, x_338);
return x_335;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_335, 1);
lean_inc(x_339);
lean_dec(x_335);
x_340 = l_Lake_setupFile___boxed__const__1;
x_341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_339);
return x_341;
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; uint8_t x_349; lean_object* x_350; uint8_t x_351; 
x_342 = lean_ctor_get(x_317, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_317, 1);
lean_inc(x_343);
lean_dec(x_317);
x_344 = lean_io_error_to_string(x_342);
x_345 = 3;
x_346 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set_uint8(x_346, sizeof(void*)*1, x_345);
x_347 = lean_box(1);
x_348 = 1;
x_349 = 0;
x_350 = l_Lake_OutStream_logEntry(x_347, x_346, x_348, x_349, x_343);
lean_dec(x_346);
x_351 = !lean_is_exclusive(x_350);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; 
x_352 = lean_ctor_get(x_350, 0);
lean_dec(x_352);
x_353 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_350, 1);
lean_ctor_set(x_350, 0, x_353);
return x_350;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_350, 1);
lean_inc(x_354);
lean_dec(x_350);
x_355 = l_Lake_setupFile___boxed__const__1;
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_354);
return x_356;
}
}
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
x_357 = lean_ctor_get(x_1, 0);
lean_inc(x_357);
lean_dec(x_1);
x_358 = l_Lake_Env_leanPath(x_357);
x_359 = l_Lake_Env_leanSrcPath(x_357);
x_360 = lean_box(0);
x_361 = lean_ctor_get(x_357, 0);
lean_inc(x_361);
lean_dec(x_357);
x_362 = lean_ctor_get(x_361, 4);
lean_inc(x_362);
lean_dec(x_361);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec(x_362);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 1, x_360);
lean_ctor_set(x_22, 0, x_363);
x_364 = lean_array_mk(x_22);
x_365 = l_Lake_setupFile___closed__3;
x_366 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_366, 0, x_358);
lean_ctor_set(x_366, 1, x_359);
lean_ctor_set(x_366, 2, x_365);
lean_ctor_set(x_366, 3, x_364);
x_367 = lean_box(0);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
x_369 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_368);
x_370 = l_Lean_Json_compress(x_369);
x_371 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_370, x_289);
if (lean_obj_tag(x_371) == 0)
{
uint8_t x_372; 
x_372 = !lean_is_exclusive(x_371);
if (x_372 == 0)
{
return x_371;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_371, 0);
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
lean_inc(x_373);
lean_dec(x_371);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
return x_375;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_383; lean_object* x_384; uint8_t x_385; 
x_376 = lean_ctor_get(x_371, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_371, 1);
lean_inc(x_377);
lean_dec(x_371);
x_378 = lean_io_error_to_string(x_376);
x_379 = 3;
x_380 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set_uint8(x_380, sizeof(void*)*1, x_379);
x_381 = lean_box(1);
x_382 = 1;
x_383 = 0;
x_384 = l_Lake_OutStream_logEntry(x_381, x_380, x_382, x_383, x_377);
lean_dec(x_380);
x_385 = !lean_is_exclusive(x_384);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; 
x_386 = lean_ctor_get(x_384, 0);
lean_dec(x_386);
x_387 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_384, 1);
lean_ctor_set(x_384, 0, x_387);
return x_384;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_384, 1);
lean_inc(x_388);
lean_dec(x_384);
x_389 = l_Lake_setupFile___boxed__const__1;
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_388);
return x_390;
}
}
}
}
else
{
lean_object* x_391; 
lean_dec(x_288);
lean_free_object(x_22);
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_391 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_286, 1);
lean_ctor_set(x_286, 0, x_391);
return x_286;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; 
x_392 = lean_ctor_get(x_286, 0);
x_393 = lean_ctor_get(x_286, 1);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_286);
x_394 = lean_string_utf8_byte_size(x_392);
x_395 = lean_unsigned_to_nat(0u);
x_396 = lean_nat_dec_eq(x_394, x_395);
lean_dec(x_394);
if (x_396 == 0)
{
uint8_t x_397; 
x_397 = lean_string_dec_eq(x_392, x_24);
lean_dec(x_392);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_free_object(x_22);
x_398 = l_Lake_invalidConfigEnvVar;
x_399 = lean_io_getenv(x_398, x_393);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; uint8_t x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
lean_dec(x_399);
x_402 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_403 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
x_404 = lean_box(1);
x_405 = l_Lake_OutStream_get(x_404, x_401);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
lean_inc(x_406);
x_408 = l_Lake_AnsiMode_isEnabled(x_406, x_403, x_407);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_box(x_402);
x_412 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__2___boxed), 5, 3);
lean_closure_set(x_412, 0, x_406);
lean_closure_set(x_412, 1, x_411);
lean_closure_set(x_412, 2, x_409);
x_413 = l_Lake_loadWorkspace(x_1, x_412, x_410);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_416, 0, x_414);
x_26 = x_416;
x_27 = x_415;
goto block_284;
}
else
{
lean_object* x_417; lean_object* x_418; 
x_417 = lean_ctor_get(x_413, 1);
lean_inc(x_417);
lean_dec(x_413);
x_418 = lean_box(0);
x_26 = x_418;
x_27 = x_417;
goto block_284;
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_419 = lean_ctor_get(x_399, 1);
lean_inc(x_419);
lean_dec(x_399);
x_420 = lean_ctor_get(x_400, 0);
lean_inc(x_420);
lean_dec(x_400);
x_421 = l_IO_eprint___at_IO_eprintln___spec__1(x_420, x_419);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
lean_dec(x_421);
x_423 = l_Lake_setupFile___closed__9;
x_424 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_423, x_422);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_426 = x_424;
} else {
 lean_dec_ref(x_424);
 x_426 = lean_box(0);
}
x_427 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_426)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_426;
 lean_ctor_set_tag(x_428, 1);
}
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_425);
return x_428;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; uint8_t x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_429 = lean_ctor_get(x_424, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_424, 1);
lean_inc(x_430);
lean_dec(x_424);
x_431 = lean_io_error_to_string(x_429);
x_432 = 3;
x_433 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*1, x_432);
x_434 = lean_box(1);
x_435 = 1;
x_436 = 0;
x_437 = l_Lake_OutStream_logEntry(x_434, x_433, x_435, x_436, x_430);
lean_dec(x_433);
x_438 = lean_ctor_get(x_437, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_439 = x_437;
} else {
 lean_dec_ref(x_437);
 x_439 = lean_box(0);
}
x_440 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_439;
 lean_ctor_set_tag(x_441, 1);
}
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_438);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; uint8_t x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_442 = lean_ctor_get(x_421, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_421, 1);
lean_inc(x_443);
lean_dec(x_421);
x_444 = lean_io_error_to_string(x_442);
x_445 = 3;
x_446 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set_uint8(x_446, sizeof(void*)*1, x_445);
x_447 = lean_box(1);
x_448 = 1;
x_449 = 0;
x_450 = l_Lake_OutStream_logEntry(x_447, x_446, x_448, x_449, x_443);
lean_dec(x_446);
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_452 = x_450;
} else {
 lean_dec_ref(x_450);
 x_452 = lean_box(0);
}
x_453 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_452)) {
 x_454 = lean_alloc_ctor(1, 2, 0);
} else {
 x_454 = x_452;
 lean_ctor_set_tag(x_454, 1);
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_451);
return x_454;
}
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
x_455 = lean_ctor_get(x_1, 0);
lean_inc(x_455);
lean_dec(x_1);
x_456 = l_Lake_Env_leanPath(x_455);
x_457 = l_Lake_Env_leanSrcPath(x_455);
x_458 = lean_box(0);
x_459 = lean_ctor_get(x_455, 0);
lean_inc(x_459);
lean_dec(x_455);
x_460 = lean_ctor_get(x_459, 4);
lean_inc(x_460);
lean_dec(x_459);
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
lean_dec(x_460);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 1, x_458);
lean_ctor_set(x_22, 0, x_461);
x_462 = lean_array_mk(x_22);
x_463 = l_Lake_setupFile___closed__3;
x_464 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_464, 0, x_456);
lean_ctor_set(x_464, 1, x_457);
lean_ctor_set(x_464, 2, x_463);
lean_ctor_set(x_464, 3, x_462);
x_465 = lean_box(0);
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
x_467 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_466);
x_468 = l_Lean_Json_compress(x_467);
x_469 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_468, x_393);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_472 = x_469;
} else {
 lean_dec_ref(x_469);
 x_472 = lean_box(0);
}
if (lean_is_scalar(x_472)) {
 x_473 = lean_alloc_ctor(0, 2, 0);
} else {
 x_473 = x_472;
}
lean_ctor_set(x_473, 0, x_470);
lean_ctor_set(x_473, 1, x_471);
return x_473;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; uint8_t x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_474 = lean_ctor_get(x_469, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_469, 1);
lean_inc(x_475);
lean_dec(x_469);
x_476 = lean_io_error_to_string(x_474);
x_477 = 3;
x_478 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set_uint8(x_478, sizeof(void*)*1, x_477);
x_479 = lean_box(1);
x_480 = 1;
x_481 = 0;
x_482 = l_Lake_OutStream_logEntry(x_479, x_478, x_480, x_481, x_475);
lean_dec(x_478);
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_484 = x_482;
} else {
 lean_dec_ref(x_482);
 x_484 = lean_box(0);
}
x_485 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_484)) {
 x_486 = lean_alloc_ctor(1, 2, 0);
} else {
 x_486 = x_484;
 lean_ctor_set_tag(x_486, 1);
}
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_483);
return x_486;
}
}
}
else
{
lean_object* x_487; lean_object* x_488; 
lean_dec(x_392);
lean_free_object(x_22);
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_487 = l_Lake_setupFile___boxed__const__2;
x_488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_393);
return x_488;
}
}
block_284:
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_box(1);
x_29 = l_Lake_setupFile___closed__2;
x_30 = 1;
x_31 = 0;
x_32 = l_Lake_OutStream_logEntry(x_28, x_29, x_30, x_31, x_27);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = l_Lake_setupFile___boxed__const__1;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_26, 0);
lean_inc(x_39);
lean_dec(x_26);
lean_inc(x_24);
x_40 = l_Lake_Workspace_findModuleBySrc_x3f(x_24, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = l_Lake_setupFile___closed__3;
x_42 = l_List_foldl___at_Lake_setupFile___spec__1(x_39, x_41, x_3);
x_43 = lean_alloc_closure((void*)(l_Lake_buildImportsAndDeps), 8, 2);
lean_closure_set(x_43, 0, x_24);
lean_closure_set(x_43, 1, x_42);
lean_inc(x_39);
x_44 = l_Lake_Workspace_runFetchM___rarg(x_39, x_43, x_4, x_27);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_io_wait(x_47, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
lean_dec(x_53);
x_54 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_39, x_52);
lean_dec(x_39);
x_55 = lean_box(0);
lean_ctor_set(x_49, 1, x_55);
lean_ctor_set(x_49, 0, x_54);
x_56 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_49);
x_57 = l_Lean_Json_compress(x_56);
x_58 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_57, x_50);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_io_error_to_string(x_63);
x_66 = 3;
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
x_68 = lean_box(1);
x_69 = 1;
x_70 = 0;
x_71 = l_Lake_OutStream_logEntry(x_68, x_67, x_69, x_70, x_64);
lean_dec(x_67);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
x_74 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = l_Lake_setupFile___boxed__const__1;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_49, 0);
lean_inc(x_78);
lean_dec(x_49);
x_79 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_39, x_78);
lean_dec(x_39);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_81);
x_83 = l_Lean_Json_compress(x_82);
x_84 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_83, x_50);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_dec(x_84);
x_91 = lean_io_error_to_string(x_89);
x_92 = 3;
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_92);
x_94 = lean_box(1);
x_95 = 1;
x_96 = 0;
x_97 = l_Lake_OutStream_logEntry(x_94, x_93, x_95, x_96, x_90);
lean_dec(x_93);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_99;
 lean_ctor_set_tag(x_101, 1);
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_49);
lean_dec(x_39);
x_102 = lean_ctor_get(x_48, 1);
lean_inc(x_102);
lean_dec(x_48);
x_103 = l_Lake_setupFile___closed__5;
x_6 = x_103;
x_7 = x_102;
goto block_21;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_39);
x_104 = lean_ctor_get(x_44, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_44, 1);
lean_inc(x_105);
lean_dec(x_44);
x_6 = x_104;
x_7 = x_105;
goto block_21;
}
}
else
{
uint8_t x_106; 
lean_dec(x_24);
lean_dec(x_3);
x_106 = !lean_is_exclusive(x_40);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_107 = lean_ctor_get(x_40, 0);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
x_109 = 1;
x_110 = l_Lake_setupFile___closed__6;
x_111 = l_Lean_Name_toString(x_108, x_109, x_110);
x_112 = l_Lake_setupFile___closed__7;
x_113 = lean_string_append(x_112, x_111);
lean_dec(x_111);
x_114 = l_Lake_setupFile___closed__8;
x_115 = lean_string_append(x_113, x_114);
x_116 = lean_ctor_get(x_107, 2);
lean_inc(x_116);
lean_ctor_set_tag(x_40, 0);
lean_ctor_set(x_40, 0, x_116);
x_117 = l_Lake_Module_keyword;
x_118 = l_Lake_Module_depsFacet;
lean_inc(x_107);
x_119 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_119, 0, x_40);
lean_ctor_set(x_119, 1, x_117);
lean_ctor_set(x_119, 2, x_107);
lean_ctor_set(x_119, 3, x_118);
x_120 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_120, 0, x_119);
lean_closure_set(x_120, 1, lean_box(0));
x_121 = 0;
x_122 = lean_box(x_121);
x_123 = lean_alloc_closure((void*)(l_Lake_withRegisterJob___at_Lake_setupFile___spec__2___boxed), 9, 3);
lean_closure_set(x_123, 0, x_115);
lean_closure_set(x_123, 1, x_120);
lean_closure_set(x_123, 2, x_122);
lean_inc(x_39);
x_124 = l_Lake_Workspace_runFetchM___rarg(x_39, x_123, x_4, x_27);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_io_wait(x_127, x_126);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_174; lean_object* x_183; 
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
x_133 = lean_box(0);
x_134 = lean_ctor_get(x_107, 0);
lean_inc(x_134);
lean_dec(x_107);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_135, 3);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_ctor_get_uint8(x_137, sizeof(void*)*13);
x_139 = lean_ctor_get(x_134, 2);
lean_inc(x_139);
lean_dec(x_134);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_ctor_get_uint8(x_140, sizeof(void*)*13);
x_142 = l___private_Lake_Config_LeanConfig_0__Lake_ordBuildType____x40_Lake_Config_LeanConfig___hyg_266_(x_138, x_141);
x_143 = lean_ctor_get(x_137, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_137, 4);
lean_inc(x_144);
lean_dec(x_137);
x_145 = l_Array_append___rarg(x_143, x_144);
lean_dec(x_144);
x_146 = lean_ctor_get(x_140, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_140, 4);
lean_inc(x_147);
lean_dec(x_140);
x_148 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_39, x_131);
lean_dec(x_39);
x_183 = lean_box(x_142);
if (lean_obj_tag(x_183) == 2)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = l_Lake_BuildType_leanOptions(x_141);
x_185 = l_Array_append___rarg(x_184, x_145);
lean_dec(x_145);
x_186 = l_Array_append___rarg(x_185, x_146);
lean_dec(x_146);
x_187 = l_Array_append___rarg(x_186, x_147);
lean_dec(x_147);
x_174 = x_187;
goto block_182;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_183);
x_188 = l_Lake_BuildType_leanOptions(x_138);
x_189 = l_Array_append___rarg(x_188, x_145);
lean_dec(x_145);
x_190 = l_Array_append___rarg(x_189, x_146);
lean_dec(x_146);
x_191 = l_Array_append___rarg(x_190, x_147);
lean_dec(x_147);
x_174 = x_191;
goto block_182;
}
block_173:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
if (lean_is_scalar(x_132)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_132;
}
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_150);
x_152 = l_Lean_Json_compress(x_151);
x_153 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_152, x_130);
if (lean_obj_tag(x_153) == 0)
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
return x_153;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_153);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; uint8_t x_165; lean_object* x_166; uint8_t x_167; 
x_158 = lean_ctor_get(x_153, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_153, 1);
lean_inc(x_159);
lean_dec(x_153);
x_160 = lean_io_error_to_string(x_158);
x_161 = 3;
x_162 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set_uint8(x_162, sizeof(void*)*1, x_161);
x_163 = lean_box(1);
x_164 = 1;
x_165 = 0;
x_166 = l_Lake_OutStream_logEntry(x_163, x_162, x_164, x_165, x_159);
lean_dec(x_162);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_166, 0);
lean_dec(x_168);
x_169 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_166, 1);
lean_ctor_set(x_166, 0, x_169);
return x_166;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_166, 1);
lean_inc(x_170);
lean_dec(x_166);
x_171 = l_Lake_setupFile___boxed__const__1;
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
block_182:
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_175 = lean_array_get_size(x_174);
x_176 = lean_unsigned_to_nat(0u);
x_177 = lean_nat_dec_lt(x_176, x_175);
if (x_177 == 0)
{
lean_dec(x_175);
lean_dec(x_174);
x_149 = x_133;
goto block_173;
}
else
{
uint8_t x_178; 
x_178 = lean_nat_dec_le(x_175, x_175);
if (x_178 == 0)
{
lean_dec(x_175);
lean_dec(x_174);
x_149 = x_133;
goto block_173;
}
else
{
size_t x_179; size_t x_180; lean_object* x_181; 
x_179 = 0;
x_180 = lean_usize_of_nat(x_175);
lean_dec(x_175);
x_181 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(x_174, x_179, x_180, x_133);
lean_dec(x_174);
x_149 = x_181;
goto block_173;
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_129);
lean_dec(x_107);
lean_dec(x_39);
x_192 = lean_ctor_get(x_128, 1);
lean_inc(x_192);
lean_dec(x_128);
x_193 = l_Lake_setupFile___closed__5;
x_6 = x_193;
x_7 = x_192;
goto block_21;
}
}
else
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_107);
lean_dec(x_39);
x_194 = lean_ctor_get(x_124, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_124, 1);
lean_inc(x_195);
lean_dec(x_124);
x_6 = x_194;
x_7 = x_195;
goto block_21;
}
}
else
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_196 = lean_ctor_get(x_40, 0);
lean_inc(x_196);
lean_dec(x_40);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
x_198 = 1;
x_199 = l_Lake_setupFile___closed__6;
x_200 = l_Lean_Name_toString(x_197, x_198, x_199);
x_201 = l_Lake_setupFile___closed__7;
x_202 = lean_string_append(x_201, x_200);
lean_dec(x_200);
x_203 = l_Lake_setupFile___closed__8;
x_204 = lean_string_append(x_202, x_203);
x_205 = lean_ctor_get(x_196, 2);
lean_inc(x_205);
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_207 = l_Lake_Module_keyword;
x_208 = l_Lake_Module_depsFacet;
lean_inc(x_196);
x_209 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
lean_ctor_set(x_209, 2, x_196);
lean_ctor_set(x_209, 3, x_208);
x_210 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_210, 0, x_209);
lean_closure_set(x_210, 1, lean_box(0));
x_211 = 0;
x_212 = lean_box(x_211);
x_213 = lean_alloc_closure((void*)(l_Lake_withRegisterJob___at_Lake_setupFile___spec__2___boxed), 9, 3);
lean_closure_set(x_213, 0, x_204);
lean_closure_set(x_213, 1, x_210);
lean_closure_set(x_213, 2, x_212);
lean_inc(x_39);
x_214 = l_Lake_Workspace_runFetchM___rarg(x_39, x_213, x_4, x_27);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_io_wait(x_217, x_216);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_262; lean_object* x_271; 
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_222 = x_219;
} else {
 lean_dec_ref(x_219);
 x_222 = lean_box(0);
}
x_223 = lean_box(0);
x_224 = lean_ctor_get(x_196, 0);
lean_inc(x_224);
lean_dec(x_196);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_225, 3);
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_228 = lean_ctor_get_uint8(x_227, sizeof(void*)*13);
x_229 = lean_ctor_get(x_224, 2);
lean_inc(x_229);
lean_dec(x_224);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
lean_dec(x_229);
x_231 = lean_ctor_get_uint8(x_230, sizeof(void*)*13);
x_232 = l___private_Lake_Config_LeanConfig_0__Lake_ordBuildType____x40_Lake_Config_LeanConfig___hyg_266_(x_228, x_231);
x_233 = lean_ctor_get(x_227, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_227, 4);
lean_inc(x_234);
lean_dec(x_227);
x_235 = l_Array_append___rarg(x_233, x_234);
lean_dec(x_234);
x_236 = lean_ctor_get(x_230, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_230, 4);
lean_inc(x_237);
lean_dec(x_230);
x_238 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_39, x_221);
lean_dec(x_39);
x_271 = lean_box(x_232);
if (lean_obj_tag(x_271) == 2)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = l_Lake_BuildType_leanOptions(x_231);
x_273 = l_Array_append___rarg(x_272, x_235);
lean_dec(x_235);
x_274 = l_Array_append___rarg(x_273, x_236);
lean_dec(x_236);
x_275 = l_Array_append___rarg(x_274, x_237);
lean_dec(x_237);
x_262 = x_275;
goto block_270;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_271);
x_276 = l_Lake_BuildType_leanOptions(x_228);
x_277 = l_Array_append___rarg(x_276, x_235);
lean_dec(x_235);
x_278 = l_Array_append___rarg(x_277, x_236);
lean_dec(x_236);
x_279 = l_Array_append___rarg(x_278, x_237);
lean_dec(x_237);
x_262 = x_279;
goto block_270;
}
block_261:
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
if (lean_is_scalar(x_222)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_222;
}
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_240);
x_242 = l_Lean_Json_compress(x_241);
x_243 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_242, x_220);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_248 = lean_ctor_get(x_243, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_243, 1);
lean_inc(x_249);
lean_dec(x_243);
x_250 = lean_io_error_to_string(x_248);
x_251 = 3;
x_252 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set_uint8(x_252, sizeof(void*)*1, x_251);
x_253 = lean_box(1);
x_254 = 1;
x_255 = 0;
x_256 = l_Lake_OutStream_logEntry(x_253, x_252, x_254, x_255, x_249);
lean_dec(x_252);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_258 = x_256;
} else {
 lean_dec_ref(x_256);
 x_258 = lean_box(0);
}
x_259 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_258)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_258;
 lean_ctor_set_tag(x_260, 1);
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_257);
return x_260;
}
}
block_270:
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_array_get_size(x_262);
x_264 = lean_unsigned_to_nat(0u);
x_265 = lean_nat_dec_lt(x_264, x_263);
if (x_265 == 0)
{
lean_dec(x_263);
lean_dec(x_262);
x_239 = x_223;
goto block_261;
}
else
{
uint8_t x_266; 
x_266 = lean_nat_dec_le(x_263, x_263);
if (x_266 == 0)
{
lean_dec(x_263);
lean_dec(x_262);
x_239 = x_223;
goto block_261;
}
else
{
size_t x_267; size_t x_268; lean_object* x_269; 
x_267 = 0;
x_268 = lean_usize_of_nat(x_263);
lean_dec(x_263);
x_269 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(x_262, x_267, x_268, x_223);
lean_dec(x_262);
x_239 = x_269;
goto block_261;
}
}
}
}
else
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_219);
lean_dec(x_196);
lean_dec(x_39);
x_280 = lean_ctor_get(x_218, 1);
lean_inc(x_280);
lean_dec(x_218);
x_281 = l_Lake_setupFile___closed__5;
x_6 = x_281;
x_7 = x_280;
goto block_21;
}
}
else
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_196);
lean_dec(x_39);
x_282 = lean_ctor_get(x_214, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_214, 1);
lean_inc(x_283);
lean_dec(x_214);
x_6 = x_282;
x_7 = x_283;
goto block_21;
}
}
}
}
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; uint8_t x_640; 
x_489 = lean_ctor_get(x_22, 0);
x_490 = lean_ctor_get(x_22, 1);
lean_inc(x_490);
lean_inc(x_489);
lean_dec(x_22);
x_633 = lean_ctor_get(x_1, 6);
lean_inc(x_633);
x_634 = l_Lake_realConfigFile(x_633, x_490);
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_637 = x_634;
} else {
 lean_dec_ref(x_634);
 x_637 = lean_box(0);
}
x_638 = lean_string_utf8_byte_size(x_635);
x_639 = lean_unsigned_to_nat(0u);
x_640 = lean_nat_dec_eq(x_638, x_639);
lean_dec(x_638);
if (x_640 == 0)
{
uint8_t x_641; 
lean_dec(x_637);
x_641 = lean_string_dec_eq(x_635, x_489);
lean_dec(x_635);
if (x_641 == 0)
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_642 = l_Lake_invalidConfigEnvVar;
x_643 = lean_io_getenv(x_642, x_636);
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; uint8_t x_646; uint8_t x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_645);
lean_dec(x_643);
x_646 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_647 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
x_648 = lean_box(1);
x_649 = l_Lake_OutStream_get(x_648, x_645);
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
lean_dec(x_649);
lean_inc(x_650);
x_652 = l_Lake_AnsiMode_isEnabled(x_650, x_647, x_651);
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
lean_dec(x_652);
x_655 = lean_box(x_646);
x_656 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__2___boxed), 5, 3);
lean_closure_set(x_656, 0, x_650);
lean_closure_set(x_656, 1, x_655);
lean_closure_set(x_656, 2, x_653);
x_657 = l_Lake_loadWorkspace(x_1, x_656, x_654);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
lean_dec(x_657);
x_660 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_660, 0, x_658);
x_491 = x_660;
x_492 = x_659;
goto block_632;
}
else
{
lean_object* x_661; lean_object* x_662; 
x_661 = lean_ctor_get(x_657, 1);
lean_inc(x_661);
lean_dec(x_657);
x_662 = lean_box(0);
x_491 = x_662;
x_492 = x_661;
goto block_632;
}
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
lean_dec(x_489);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_663 = lean_ctor_get(x_643, 1);
lean_inc(x_663);
lean_dec(x_643);
x_664 = lean_ctor_get(x_644, 0);
lean_inc(x_664);
lean_dec(x_644);
x_665 = l_IO_eprint___at_IO_eprintln___spec__1(x_664, x_663);
if (lean_obj_tag(x_665) == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_666 = lean_ctor_get(x_665, 1);
lean_inc(x_666);
lean_dec(x_665);
x_667 = l_Lake_setupFile___closed__9;
x_668 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_667, x_666);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_669 = lean_ctor_get(x_668, 1);
lean_inc(x_669);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_670 = x_668;
} else {
 lean_dec_ref(x_668);
 x_670 = lean_box(0);
}
x_671 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_670)) {
 x_672 = lean_alloc_ctor(1, 2, 0);
} else {
 x_672 = x_670;
 lean_ctor_set_tag(x_672, 1);
}
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_669);
return x_672;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; lean_object* x_677; lean_object* x_678; uint8_t x_679; uint8_t x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_673 = lean_ctor_get(x_668, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_668, 1);
lean_inc(x_674);
lean_dec(x_668);
x_675 = lean_io_error_to_string(x_673);
x_676 = 3;
x_677 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_677, 0, x_675);
lean_ctor_set_uint8(x_677, sizeof(void*)*1, x_676);
x_678 = lean_box(1);
x_679 = 1;
x_680 = 0;
x_681 = l_Lake_OutStream_logEntry(x_678, x_677, x_679, x_680, x_674);
lean_dec(x_677);
x_682 = lean_ctor_get(x_681, 1);
lean_inc(x_682);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_683 = x_681;
} else {
 lean_dec_ref(x_681);
 x_683 = lean_box(0);
}
x_684 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_683)) {
 x_685 = lean_alloc_ctor(1, 2, 0);
} else {
 x_685 = x_683;
 lean_ctor_set_tag(x_685, 1);
}
lean_ctor_set(x_685, 0, x_684);
lean_ctor_set(x_685, 1, x_682);
return x_685;
}
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; uint8_t x_689; lean_object* x_690; lean_object* x_691; uint8_t x_692; uint8_t x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_686 = lean_ctor_get(x_665, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_665, 1);
lean_inc(x_687);
lean_dec(x_665);
x_688 = lean_io_error_to_string(x_686);
x_689 = 3;
x_690 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_690, 0, x_688);
lean_ctor_set_uint8(x_690, sizeof(void*)*1, x_689);
x_691 = lean_box(1);
x_692 = 1;
x_693 = 0;
x_694 = l_Lake_OutStream_logEntry(x_691, x_690, x_692, x_693, x_687);
lean_dec(x_690);
x_695 = lean_ctor_get(x_694, 1);
lean_inc(x_695);
if (lean_is_exclusive(x_694)) {
 lean_ctor_release(x_694, 0);
 lean_ctor_release(x_694, 1);
 x_696 = x_694;
} else {
 lean_dec_ref(x_694);
 x_696 = lean_box(0);
}
x_697 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_696)) {
 x_698 = lean_alloc_ctor(1, 2, 0);
} else {
 x_698 = x_696;
 lean_ctor_set_tag(x_698, 1);
}
lean_ctor_set(x_698, 0, x_697);
lean_ctor_set(x_698, 1, x_695);
return x_698;
}
}
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
lean_dec(x_489);
lean_dec(x_4);
lean_dec(x_3);
x_699 = lean_ctor_get(x_1, 0);
lean_inc(x_699);
lean_dec(x_1);
x_700 = l_Lake_Env_leanPath(x_699);
x_701 = l_Lake_Env_leanSrcPath(x_699);
x_702 = lean_box(0);
x_703 = lean_ctor_get(x_699, 0);
lean_inc(x_703);
lean_dec(x_699);
x_704 = lean_ctor_get(x_703, 4);
lean_inc(x_704);
lean_dec(x_703);
x_705 = lean_ctor_get(x_704, 0);
lean_inc(x_705);
lean_dec(x_704);
x_706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_702);
x_707 = lean_array_mk(x_706);
x_708 = l_Lake_setupFile___closed__3;
x_709 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_709, 0, x_700);
lean_ctor_set(x_709, 1, x_701);
lean_ctor_set(x_709, 2, x_708);
lean_ctor_set(x_709, 3, x_707);
x_710 = lean_box(0);
x_711 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
x_712 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_711);
x_713 = l_Lean_Json_compress(x_712);
x_714 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_713, x_636);
if (lean_obj_tag(x_714) == 0)
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_715 = lean_ctor_get(x_714, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_714, 1);
lean_inc(x_716);
if (lean_is_exclusive(x_714)) {
 lean_ctor_release(x_714, 0);
 lean_ctor_release(x_714, 1);
 x_717 = x_714;
} else {
 lean_dec_ref(x_714);
 x_717 = lean_box(0);
}
if (lean_is_scalar(x_717)) {
 x_718 = lean_alloc_ctor(0, 2, 0);
} else {
 x_718 = x_717;
}
lean_ctor_set(x_718, 0, x_715);
lean_ctor_set(x_718, 1, x_716);
return x_718;
}
else
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; uint8_t x_722; lean_object* x_723; lean_object* x_724; uint8_t x_725; uint8_t x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_719 = lean_ctor_get(x_714, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_714, 1);
lean_inc(x_720);
lean_dec(x_714);
x_721 = lean_io_error_to_string(x_719);
x_722 = 3;
x_723 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_723, 0, x_721);
lean_ctor_set_uint8(x_723, sizeof(void*)*1, x_722);
x_724 = lean_box(1);
x_725 = 1;
x_726 = 0;
x_727 = l_Lake_OutStream_logEntry(x_724, x_723, x_725, x_726, x_720);
lean_dec(x_723);
x_728 = lean_ctor_get(x_727, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_729 = x_727;
} else {
 lean_dec_ref(x_727);
 x_729 = lean_box(0);
}
x_730 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_729)) {
 x_731 = lean_alloc_ctor(1, 2, 0);
} else {
 x_731 = x_729;
 lean_ctor_set_tag(x_731, 1);
}
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_728);
return x_731;
}
}
}
else
{
lean_object* x_732; lean_object* x_733; 
lean_dec(x_635);
lean_dec(x_489);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_732 = l_Lake_setupFile___boxed__const__2;
if (lean_is_scalar(x_637)) {
 x_733 = lean_alloc_ctor(1, 2, 0);
} else {
 x_733 = x_637;
 lean_ctor_set_tag(x_733, 1);
}
lean_ctor_set(x_733, 0, x_732);
lean_ctor_set(x_733, 1, x_636);
return x_733;
}
block_632:
{
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_493; lean_object* x_494; uint8_t x_495; uint8_t x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_489);
lean_dec(x_4);
lean_dec(x_3);
x_493 = lean_box(1);
x_494 = l_Lake_setupFile___closed__2;
x_495 = 1;
x_496 = 0;
x_497 = l_Lake_OutStream_logEntry(x_493, x_494, x_495, x_496, x_492);
x_498 = lean_ctor_get(x_497, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_499 = x_497;
} else {
 lean_dec_ref(x_497);
 x_499 = lean_box(0);
}
x_500 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_499)) {
 x_501 = lean_alloc_ctor(1, 2, 0);
} else {
 x_501 = x_499;
 lean_ctor_set_tag(x_501, 1);
}
lean_ctor_set(x_501, 0, x_500);
lean_ctor_set(x_501, 1, x_498);
return x_501;
}
else
{
lean_object* x_502; lean_object* x_503; 
x_502 = lean_ctor_get(x_491, 0);
lean_inc(x_502);
lean_dec(x_491);
lean_inc(x_489);
x_503 = l_Lake_Workspace_findModuleBySrc_x3f(x_489, x_502);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_504 = l_Lake_setupFile___closed__3;
x_505 = l_List_foldl___at_Lake_setupFile___spec__1(x_502, x_504, x_3);
x_506 = lean_alloc_closure((void*)(l_Lake_buildImportsAndDeps), 8, 2);
lean_closure_set(x_506, 0, x_489);
lean_closure_set(x_506, 1, x_505);
lean_inc(x_502);
x_507 = l_Lake_Workspace_runFetchM___rarg(x_502, x_506, x_4, x_492);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
lean_dec(x_507);
x_510 = lean_ctor_get(x_508, 0);
lean_inc(x_510);
lean_dec(x_508);
x_511 = lean_io_wait(x_510, x_509);
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
x_514 = lean_ctor_get(x_512, 0);
lean_inc(x_514);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 x_515 = x_512;
} else {
 lean_dec_ref(x_512);
 x_515 = lean_box(0);
}
x_516 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_502, x_514);
lean_dec(x_502);
x_517 = lean_box(0);
if (lean_is_scalar(x_515)) {
 x_518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_518 = x_515;
}
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
x_519 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_518);
x_520 = l_Lean_Json_compress(x_519);
x_521 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_520, x_513);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 x_524 = x_521;
} else {
 lean_dec_ref(x_521);
 x_524 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(0, 2, 0);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_522);
lean_ctor_set(x_525, 1, x_523);
return x_525;
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; uint8_t x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; uint8_t x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_526 = lean_ctor_get(x_521, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_521, 1);
lean_inc(x_527);
lean_dec(x_521);
x_528 = lean_io_error_to_string(x_526);
x_529 = 3;
x_530 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_530, 0, x_528);
lean_ctor_set_uint8(x_530, sizeof(void*)*1, x_529);
x_531 = lean_box(1);
x_532 = 1;
x_533 = 0;
x_534 = l_Lake_OutStream_logEntry(x_531, x_530, x_532, x_533, x_527);
lean_dec(x_530);
x_535 = lean_ctor_get(x_534, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_536 = x_534;
} else {
 lean_dec_ref(x_534);
 x_536 = lean_box(0);
}
x_537 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_536)) {
 x_538 = lean_alloc_ctor(1, 2, 0);
} else {
 x_538 = x_536;
 lean_ctor_set_tag(x_538, 1);
}
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_535);
return x_538;
}
}
else
{
lean_object* x_539; lean_object* x_540; 
lean_dec(x_512);
lean_dec(x_502);
x_539 = lean_ctor_get(x_511, 1);
lean_inc(x_539);
lean_dec(x_511);
x_540 = l_Lake_setupFile___closed__5;
x_6 = x_540;
x_7 = x_539;
goto block_21;
}
}
else
{
lean_object* x_541; lean_object* x_542; 
lean_dec(x_502);
x_541 = lean_ctor_get(x_507, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_507, 1);
lean_inc(x_542);
lean_dec(x_507);
x_6 = x_541;
x_7 = x_542;
goto block_21;
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_489);
lean_dec(x_3);
x_543 = lean_ctor_get(x_503, 0);
lean_inc(x_543);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 x_544 = x_503;
} else {
 lean_dec_ref(x_503);
 x_544 = lean_box(0);
}
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
x_546 = 1;
x_547 = l_Lake_setupFile___closed__6;
x_548 = l_Lean_Name_toString(x_545, x_546, x_547);
x_549 = l_Lake_setupFile___closed__7;
x_550 = lean_string_append(x_549, x_548);
lean_dec(x_548);
x_551 = l_Lake_setupFile___closed__8;
x_552 = lean_string_append(x_550, x_551);
x_553 = lean_ctor_get(x_543, 2);
lean_inc(x_553);
if (lean_is_scalar(x_544)) {
 x_554 = lean_alloc_ctor(0, 1, 0);
} else {
 x_554 = x_544;
 lean_ctor_set_tag(x_554, 0);
}
lean_ctor_set(x_554, 0, x_553);
x_555 = l_Lake_Module_keyword;
x_556 = l_Lake_Module_depsFacet;
lean_inc(x_543);
x_557 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_557, 0, x_554);
lean_ctor_set(x_557, 1, x_555);
lean_ctor_set(x_557, 2, x_543);
lean_ctor_set(x_557, 3, x_556);
x_558 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_558, 0, x_557);
lean_closure_set(x_558, 1, lean_box(0));
x_559 = 0;
x_560 = lean_box(x_559);
x_561 = lean_alloc_closure((void*)(l_Lake_withRegisterJob___at_Lake_setupFile___spec__2___boxed), 9, 3);
lean_closure_set(x_561, 0, x_552);
lean_closure_set(x_561, 1, x_558);
lean_closure_set(x_561, 2, x_560);
lean_inc(x_502);
x_562 = l_Lake_Workspace_runFetchM___rarg(x_502, x_561, x_4, x_492);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_562, 1);
lean_inc(x_564);
lean_dec(x_562);
x_565 = lean_ctor_get(x_563, 0);
lean_inc(x_565);
lean_dec(x_563);
x_566 = lean_io_wait(x_565, x_564);
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; lean_object* x_578; uint8_t x_579; uint8_t x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_610; lean_object* x_619; 
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
x_569 = lean_ctor_get(x_567, 0);
lean_inc(x_569);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 x_570 = x_567;
} else {
 lean_dec_ref(x_567);
 x_570 = lean_box(0);
}
x_571 = lean_box(0);
x_572 = lean_ctor_get(x_543, 0);
lean_inc(x_572);
lean_dec(x_543);
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_573, 3);
lean_inc(x_574);
lean_dec(x_573);
x_575 = lean_ctor_get(x_574, 1);
lean_inc(x_575);
lean_dec(x_574);
x_576 = lean_ctor_get_uint8(x_575, sizeof(void*)*13);
x_577 = lean_ctor_get(x_572, 2);
lean_inc(x_577);
lean_dec(x_572);
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
lean_dec(x_577);
x_579 = lean_ctor_get_uint8(x_578, sizeof(void*)*13);
x_580 = l___private_Lake_Config_LeanConfig_0__Lake_ordBuildType____x40_Lake_Config_LeanConfig___hyg_266_(x_576, x_579);
x_581 = lean_ctor_get(x_575, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_575, 4);
lean_inc(x_582);
lean_dec(x_575);
x_583 = l_Array_append___rarg(x_581, x_582);
lean_dec(x_582);
x_584 = lean_ctor_get(x_578, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_578, 4);
lean_inc(x_585);
lean_dec(x_578);
x_586 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_502, x_569);
lean_dec(x_502);
x_619 = lean_box(x_580);
if (lean_obj_tag(x_619) == 2)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_620 = l_Lake_BuildType_leanOptions(x_579);
x_621 = l_Array_append___rarg(x_620, x_583);
lean_dec(x_583);
x_622 = l_Array_append___rarg(x_621, x_584);
lean_dec(x_584);
x_623 = l_Array_append___rarg(x_622, x_585);
lean_dec(x_585);
x_610 = x_623;
goto block_618;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
lean_dec(x_619);
x_624 = l_Lake_BuildType_leanOptions(x_576);
x_625 = l_Array_append___rarg(x_624, x_583);
lean_dec(x_583);
x_626 = l_Array_append___rarg(x_625, x_584);
lean_dec(x_584);
x_627 = l_Array_append___rarg(x_626, x_585);
lean_dec(x_585);
x_610 = x_627;
goto block_618;
}
block_609:
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
if (lean_is_scalar(x_570)) {
 x_588 = lean_alloc_ctor(0, 2, 0);
} else {
 x_588 = x_570;
}
lean_ctor_set(x_588, 0, x_586);
lean_ctor_set(x_588, 1, x_587);
x_589 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_588);
x_590 = l_Lean_Json_compress(x_589);
x_591 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_590, x_568);
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_591, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 lean_ctor_release(x_591, 1);
 x_594 = x_591;
} else {
 lean_dec_ref(x_591);
 x_594 = lean_box(0);
}
if (lean_is_scalar(x_594)) {
 x_595 = lean_alloc_ctor(0, 2, 0);
} else {
 x_595 = x_594;
}
lean_ctor_set(x_595, 0, x_592);
lean_ctor_set(x_595, 1, x_593);
return x_595;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; uint8_t x_599; lean_object* x_600; lean_object* x_601; uint8_t x_602; uint8_t x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_596 = lean_ctor_get(x_591, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_591, 1);
lean_inc(x_597);
lean_dec(x_591);
x_598 = lean_io_error_to_string(x_596);
x_599 = 3;
x_600 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set_uint8(x_600, sizeof(void*)*1, x_599);
x_601 = lean_box(1);
x_602 = 1;
x_603 = 0;
x_604 = l_Lake_OutStream_logEntry(x_601, x_600, x_602, x_603, x_597);
lean_dec(x_600);
x_605 = lean_ctor_get(x_604, 1);
lean_inc(x_605);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_606 = x_604;
} else {
 lean_dec_ref(x_604);
 x_606 = lean_box(0);
}
x_607 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_606)) {
 x_608 = lean_alloc_ctor(1, 2, 0);
} else {
 x_608 = x_606;
 lean_ctor_set_tag(x_608, 1);
}
lean_ctor_set(x_608, 0, x_607);
lean_ctor_set(x_608, 1, x_605);
return x_608;
}
}
block_618:
{
lean_object* x_611; lean_object* x_612; uint8_t x_613; 
x_611 = lean_array_get_size(x_610);
x_612 = lean_unsigned_to_nat(0u);
x_613 = lean_nat_dec_lt(x_612, x_611);
if (x_613 == 0)
{
lean_dec(x_611);
lean_dec(x_610);
x_587 = x_571;
goto block_609;
}
else
{
uint8_t x_614; 
x_614 = lean_nat_dec_le(x_611, x_611);
if (x_614 == 0)
{
lean_dec(x_611);
lean_dec(x_610);
x_587 = x_571;
goto block_609;
}
else
{
size_t x_615; size_t x_616; lean_object* x_617; 
x_615 = 0;
x_616 = lean_usize_of_nat(x_611);
lean_dec(x_611);
x_617 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(x_610, x_615, x_616, x_571);
lean_dec(x_610);
x_587 = x_617;
goto block_609;
}
}
}
}
else
{
lean_object* x_628; lean_object* x_629; 
lean_dec(x_567);
lean_dec(x_543);
lean_dec(x_502);
x_628 = lean_ctor_get(x_566, 1);
lean_inc(x_628);
lean_dec(x_566);
x_629 = l_Lake_setupFile___closed__5;
x_6 = x_629;
x_7 = x_628;
goto block_21;
}
}
else
{
lean_object* x_630; lean_object* x_631; 
lean_dec(x_543);
lean_dec(x_502);
x_630 = lean_ctor_get(x_562, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_562, 1);
lean_inc(x_631);
lean_dec(x_562);
x_6 = x_630;
x_7 = x_631;
goto block_21;
}
}
}
}
}
block_21:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_io_error_to_string(x_6);
x_9 = 3;
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
x_11 = lean_box(1);
x_12 = 1;
x_13 = 0;
x_14 = l_Lake_OutStream_logEntry(x_11, x_10, x_12, x_13, x_7);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lake_setupFile___boxed__const__1;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at_Lake_setupFile___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___at_Lake_setupFile___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_withRegisterJob___at_Lake_setupFile___spec__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_setupFile___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lake_setupFile___lambda__2(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_box(1);
x_9 = 1;
x_10 = 0;
x_11 = l_Lake_OutStream_logEntry(x_8, x_7, x_9, x_10, x_5);
lean_dec(x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_5);
return x_17;
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--server", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_serve___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_serve___lambda__1___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_serve___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_serve___lambda__1___closed__3;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_8, 7);
x_10 = l_Lake_serve___lambda__1___closed__4;
x_11 = l_Array_append___rarg(x_10, x_6);
x_12 = l_Array_append___rarg(x_11, x_2);
x_13 = lean_box(0);
x_14 = l_Lake_serve___lambda__1___closed__1;
x_15 = 1;
x_16 = 0;
lean_inc(x_5);
lean_inc(x_9);
x_17 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_5);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_16);
x_18 = lean_io_process_spawn(x_17, x_4);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_io_process_child_wait(x_14, x_19, x_20);
lean_dec(x_19);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lake_serve___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warning: package configuration has errors, falling back to plain `lean --server`", 80, 80);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_serve(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_loadWorkspace), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lake_LoggerIO_captureLog___rarg(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lake_serve___closed__1;
x_16 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_15, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = l_Lake_Env_baseVars(x_18);
x_20 = l_Lake_Log_toString(x_11);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_22);
x_23 = lean_array_push(x_19, x_7);
x_24 = l_Lake_setupFile___closed__3;
lean_ctor_set(x_5, 1, x_24);
lean_ctor_set(x_5, 0, x_23);
x_25 = l_Lake_serve___lambda__1(x_1, x_2, x_5, x_17);
lean_dec(x_5);
lean_dec(x_1);
return x_25;
}
else
{
uint8_t x_26; 
lean_free_object(x_7);
lean_dec(x_11);
lean_free_object(x_5);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_free_object(x_5);
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
lean_dec(x_10);
lean_inc(x_30);
x_31 = l_Lake_Workspace_augmentedEnvVars(x_30);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 4);
lean_inc(x_34);
lean_dec(x_33);
lean_ctor_set(x_7, 1, x_34);
lean_ctor_set(x_7, 0, x_31);
x_35 = l_Lake_serve___lambda__1(x_1, x_2, x_7, x_9);
lean_dec(x_7);
lean_dec(x_1);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_12, x_12);
if (x_36 == 0)
{
lean_dec(x_12);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lake_serve___closed__1;
x_38 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_37, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = l_Lake_Env_baseVars(x_40);
x_42 = l_Lake_Log_toString(x_11);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_7, 1, x_43);
lean_ctor_set(x_7, 0, x_44);
x_45 = lean_array_push(x_41, x_7);
x_46 = l_Lake_setupFile___closed__3;
lean_ctor_set(x_5, 1, x_46);
lean_ctor_set(x_5, 0, x_45);
x_47 = l_Lake_serve___lambda__1(x_1, x_2, x_5, x_39);
lean_dec(x_5);
lean_dec(x_1);
return x_47;
}
else
{
uint8_t x_48; 
lean_free_object(x_7);
lean_dec(x_11);
lean_free_object(x_5);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_11);
lean_free_object(x_5);
x_52 = lean_ctor_get(x_10, 0);
lean_inc(x_52);
lean_dec(x_10);
lean_inc(x_52);
x_53 = l_Lake_Workspace_augmentedEnvVars(x_52);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_54, 3);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get(x_55, 4);
lean_inc(x_56);
lean_dec(x_55);
lean_ctor_set(x_7, 1, x_56);
lean_ctor_set(x_7, 0, x_53);
x_57 = l_Lake_serve___lambda__1(x_1, x_2, x_7, x_9);
lean_dec(x_7);
lean_dec(x_1);
return x_57;
}
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_5);
x_58 = 0;
x_59 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_60 = lean_box(0);
x_61 = l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(x_11, x_58, x_59, x_60, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_61, 1);
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = l_Lake_serve___closed__1;
x_66 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_65, x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = l_Lake_Env_baseVars(x_68);
x_70 = l_Lake_Log_toString(x_11);
lean_dec(x_11);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_7, 1, x_71);
lean_ctor_set(x_7, 0, x_72);
x_73 = lean_array_push(x_69, x_7);
x_74 = l_Lake_setupFile___closed__3;
lean_ctor_set(x_61, 1, x_74);
lean_ctor_set(x_61, 0, x_73);
x_75 = l_Lake_serve___lambda__1(x_1, x_2, x_61, x_67);
lean_dec(x_61);
lean_dec(x_1);
return x_75;
}
else
{
uint8_t x_76; 
lean_free_object(x_61);
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
return x_66;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_66, 0);
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_66);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_61, 1);
lean_inc(x_80);
lean_dec(x_61);
x_81 = l_Lake_serve___closed__1;
x_82 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_81, x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get(x_1, 0);
lean_inc(x_84);
x_85 = l_Lake_Env_baseVars(x_84);
x_86 = l_Lake_Log_toString(x_11);
lean_dec(x_11);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_7, 1, x_87);
lean_ctor_set(x_7, 0, x_88);
x_89 = lean_array_push(x_85, x_7);
x_90 = l_Lake_setupFile___closed__3;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lake_serve___lambda__1(x_1, x_2, x_91, x_83);
lean_dec(x_91);
lean_dec(x_1);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_1);
x_93 = lean_ctor_get(x_82, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_82, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_95 = x_82;
} else {
 lean_dec_ref(x_82);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_11);
x_97 = lean_ctor_get(x_61, 1);
lean_inc(x_97);
lean_dec(x_61);
x_98 = lean_ctor_get(x_10, 0);
lean_inc(x_98);
lean_dec(x_10);
lean_inc(x_98);
x_99 = l_Lake_Workspace_augmentedEnvVars(x_98);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_100, 3);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_ctor_get(x_101, 4);
lean_inc(x_102);
lean_dec(x_101);
lean_ctor_set(x_7, 1, x_102);
lean_ctor_set(x_7, 0, x_99);
x_103 = l_Lake_serve___lambda__1(x_1, x_2, x_7, x_97);
lean_dec(x_7);
lean_dec(x_1);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_104 = lean_ctor_get(x_5, 1);
x_105 = lean_ctor_get(x_7, 0);
x_106 = lean_ctor_get(x_7, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_7);
x_107 = lean_array_get_size(x_106);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_nat_dec_lt(x_108, x_107);
if (x_109 == 0)
{
lean_dec(x_107);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = l_Lake_serve___closed__1;
x_111 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_110, x_104);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_ctor_get(x_1, 0);
lean_inc(x_113);
x_114 = l_Lake_Env_baseVars(x_113);
x_115 = l_Lake_Log_toString(x_106);
lean_dec(x_106);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = l_Lake_invalidConfigEnvVar;
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_array_push(x_114, x_118);
x_120 = l_Lake_setupFile___closed__3;
lean_ctor_set(x_5, 1, x_120);
lean_ctor_set(x_5, 0, x_119);
x_121 = l_Lake_serve___lambda__1(x_1, x_2, x_5, x_112);
lean_dec(x_5);
lean_dec(x_1);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_106);
lean_free_object(x_5);
lean_dec(x_1);
x_122 = lean_ctor_get(x_111, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_111, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_124 = x_111;
} else {
 lean_dec_ref(x_111);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_106);
lean_free_object(x_5);
x_126 = lean_ctor_get(x_105, 0);
lean_inc(x_126);
lean_dec(x_105);
lean_inc(x_126);
x_127 = l_Lake_Workspace_augmentedEnvVars(x_126);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_128, 3);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_ctor_get(x_129, 4);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lake_serve___lambda__1(x_1, x_2, x_131, x_104);
lean_dec(x_131);
lean_dec(x_1);
return x_132;
}
}
else
{
uint8_t x_133; 
x_133 = lean_nat_dec_le(x_107, x_107);
if (x_133 == 0)
{
lean_dec(x_107);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = l_Lake_serve___closed__1;
x_135 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_134, x_104);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_ctor_get(x_1, 0);
lean_inc(x_137);
x_138 = l_Lake_Env_baseVars(x_137);
x_139 = l_Lake_Log_toString(x_106);
lean_dec(x_106);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = l_Lake_invalidConfigEnvVar;
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = lean_array_push(x_138, x_142);
x_144 = l_Lake_setupFile___closed__3;
lean_ctor_set(x_5, 1, x_144);
lean_ctor_set(x_5, 0, x_143);
x_145 = l_Lake_serve___lambda__1(x_1, x_2, x_5, x_136);
lean_dec(x_5);
lean_dec(x_1);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_106);
lean_free_object(x_5);
lean_dec(x_1);
x_146 = lean_ctor_get(x_135, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_135, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_148 = x_135;
} else {
 lean_dec_ref(x_135);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_106);
lean_free_object(x_5);
x_150 = lean_ctor_get(x_105, 0);
lean_inc(x_150);
lean_dec(x_105);
lean_inc(x_150);
x_151 = l_Lake_Workspace_augmentedEnvVars(x_150);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_152, 3);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_ctor_get(x_153, 4);
lean_inc(x_154);
lean_dec(x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_151);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lake_serve___lambda__1(x_1, x_2, x_155, x_104);
lean_dec(x_155);
lean_dec(x_1);
return x_156;
}
}
else
{
size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; 
lean_free_object(x_5);
x_157 = 0;
x_158 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_159 = lean_box(0);
x_160 = l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(x_106, x_157, x_158, x_159, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = l_Lake_serve___closed__1;
x_164 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_163, x_161);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_ctor_get(x_1, 0);
lean_inc(x_166);
x_167 = l_Lake_Env_baseVars(x_166);
x_168 = l_Lake_Log_toString(x_106);
lean_dec(x_106);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = l_Lake_invalidConfigEnvVar;
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = lean_array_push(x_167, x_171);
x_173 = l_Lake_setupFile___closed__3;
if (lean_is_scalar(x_162)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_162;
}
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = l_Lake_serve___lambda__1(x_1, x_2, x_174, x_165);
lean_dec(x_174);
lean_dec(x_1);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_162);
lean_dec(x_106);
lean_dec(x_1);
x_176 = lean_ctor_get(x_164, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_164, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_178 = x_164;
} else {
 lean_dec_ref(x_164);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_106);
x_180 = lean_ctor_get(x_160, 1);
lean_inc(x_180);
lean_dec(x_160);
x_181 = lean_ctor_get(x_105, 0);
lean_inc(x_181);
lean_dec(x_105);
lean_inc(x_181);
x_182 = l_Lake_Workspace_augmentedEnvVars(x_181);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_ctor_get(x_183, 3);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_ctor_get(x_184, 4);
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_185);
x_187 = l_Lake_serve___lambda__1(x_1, x_2, x_186, x_180);
lean_dec(x_186);
lean_dec(x_1);
return x_187;
}
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_188 = lean_ctor_get(x_5, 0);
x_189 = lean_ctor_get(x_5, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_5);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_192 = x_188;
} else {
 lean_dec_ref(x_188);
 x_192 = lean_box(0);
}
x_193 = lean_array_get_size(x_191);
x_194 = lean_unsigned_to_nat(0u);
x_195 = lean_nat_dec_lt(x_194, x_193);
if (x_195 == 0)
{
lean_dec(x_193);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = l_Lake_serve___closed__1;
x_197 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_196, x_189);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_ctor_get(x_1, 0);
lean_inc(x_199);
x_200 = l_Lake_Env_baseVars(x_199);
x_201 = l_Lake_Log_toString(x_191);
lean_dec(x_191);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_201);
x_203 = l_Lake_invalidConfigEnvVar;
if (lean_is_scalar(x_192)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_192;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = lean_array_push(x_200, x_204);
x_206 = l_Lake_setupFile___closed__3;
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = l_Lake_serve___lambda__1(x_1, x_2, x_207, x_198);
lean_dec(x_207);
lean_dec(x_1);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_1);
x_209 = lean_ctor_get(x_197, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_197, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_211 = x_197;
} else {
 lean_dec_ref(x_197);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_191);
x_213 = lean_ctor_get(x_190, 0);
lean_inc(x_213);
lean_dec(x_190);
lean_inc(x_213);
x_214 = l_Lake_Workspace_augmentedEnvVars(x_213);
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_215, 3);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_ctor_get(x_216, 4);
lean_inc(x_217);
lean_dec(x_216);
if (lean_is_scalar(x_192)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_192;
}
lean_ctor_set(x_218, 0, x_214);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lake_serve___lambda__1(x_1, x_2, x_218, x_189);
lean_dec(x_218);
lean_dec(x_1);
return x_219;
}
}
else
{
uint8_t x_220; 
x_220 = lean_nat_dec_le(x_193, x_193);
if (x_220 == 0)
{
lean_dec(x_193);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = l_Lake_serve___closed__1;
x_222 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_221, x_189);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_ctor_get(x_1, 0);
lean_inc(x_224);
x_225 = l_Lake_Env_baseVars(x_224);
x_226 = l_Lake_Log_toString(x_191);
lean_dec(x_191);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = l_Lake_invalidConfigEnvVar;
if (lean_is_scalar(x_192)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_192;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = lean_array_push(x_225, x_229);
x_231 = l_Lake_setupFile___closed__3;
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lake_serve___lambda__1(x_1, x_2, x_232, x_223);
lean_dec(x_232);
lean_dec(x_1);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_1);
x_234 = lean_ctor_get(x_222, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_222, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_236 = x_222;
} else {
 lean_dec_ref(x_222);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_191);
x_238 = lean_ctor_get(x_190, 0);
lean_inc(x_238);
lean_dec(x_190);
lean_inc(x_238);
x_239 = l_Lake_Workspace_augmentedEnvVars(x_238);
x_240 = lean_ctor_get(x_238, 0);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_ctor_get(x_240, 3);
lean_inc(x_241);
lean_dec(x_240);
x_242 = lean_ctor_get(x_241, 4);
lean_inc(x_242);
lean_dec(x_241);
if (lean_is_scalar(x_192)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_192;
}
lean_ctor_set(x_243, 0, x_239);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lake_serve___lambda__1(x_1, x_2, x_243, x_189);
lean_dec(x_243);
lean_dec(x_1);
return x_244;
}
}
else
{
size_t x_245; size_t x_246; lean_object* x_247; lean_object* x_248; 
x_245 = 0;
x_246 = lean_usize_of_nat(x_193);
lean_dec(x_193);
x_247 = lean_box(0);
x_248 = l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(x_191, x_245, x_246, x_247, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_250 = x_248;
} else {
 lean_dec_ref(x_248);
 x_250 = lean_box(0);
}
x_251 = l_Lake_serve___closed__1;
x_252 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_251, x_249);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_254 = lean_ctor_get(x_1, 0);
lean_inc(x_254);
x_255 = l_Lake_Env_baseVars(x_254);
x_256 = l_Lake_Log_toString(x_191);
lean_dec(x_191);
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_256);
x_258 = l_Lake_invalidConfigEnvVar;
if (lean_is_scalar(x_192)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_192;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
x_260 = lean_array_push(x_255, x_259);
x_261 = l_Lake_setupFile___closed__3;
if (lean_is_scalar(x_250)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_250;
}
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
x_263 = l_Lake_serve___lambda__1(x_1, x_2, x_262, x_253);
lean_dec(x_262);
lean_dec(x_1);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_250);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_1);
x_264 = lean_ctor_get(x_252, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_252, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_266 = x_252;
} else {
 lean_dec_ref(x_252);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_191);
x_268 = lean_ctor_get(x_248, 1);
lean_inc(x_268);
lean_dec(x_248);
x_269 = lean_ctor_get(x_190, 0);
lean_inc(x_269);
lean_dec(x_190);
lean_inc(x_269);
x_270 = l_Lake_Workspace_augmentedEnvVars(x_269);
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_ctor_get(x_271, 3);
lean_inc(x_272);
lean_dec(x_271);
x_273 = lean_ctor_get(x_272, 4);
lean_inc(x_273);
lean_dec(x_272);
if (lean_is_scalar(x_192)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_192;
}
lean_ctor_set(x_274, 0, x_270);
lean_ctor_set(x_274, 1, x_273);
x_275 = l_Lake_serve___lambda__1(x_1, x_2, x_274, x_268);
lean_dec(x_274);
lean_dec(x_1);
return x_275;
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_serve(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lake_Load(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_MainM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FileSetupInfo(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Serve(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
l_Lake_setupFile___closed__1 = _init_l_Lake_setupFile___closed__1();
lean_mark_persistent(l_Lake_setupFile___closed__1);
l_Lake_setupFile___closed__2 = _init_l_Lake_setupFile___closed__2();
lean_mark_persistent(l_Lake_setupFile___closed__2);
l_Lake_setupFile___closed__3 = _init_l_Lake_setupFile___closed__3();
lean_mark_persistent(l_Lake_setupFile___closed__3);
l_Lake_setupFile___closed__4 = _init_l_Lake_setupFile___closed__4();
lean_mark_persistent(l_Lake_setupFile___closed__4);
l_Lake_setupFile___closed__5 = _init_l_Lake_setupFile___closed__5();
lean_mark_persistent(l_Lake_setupFile___closed__5);
l_Lake_setupFile___closed__6 = _init_l_Lake_setupFile___closed__6();
lean_mark_persistent(l_Lake_setupFile___closed__6);
l_Lake_setupFile___closed__7 = _init_l_Lake_setupFile___closed__7();
lean_mark_persistent(l_Lake_setupFile___closed__7);
l_Lake_setupFile___closed__8 = _init_l_Lake_setupFile___closed__8();
lean_mark_persistent(l_Lake_setupFile___closed__8);
l_Lake_setupFile___closed__9 = _init_l_Lake_setupFile___closed__9();
lean_mark_persistent(l_Lake_setupFile___closed__9);
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
