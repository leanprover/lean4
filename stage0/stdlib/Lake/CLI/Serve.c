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
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___at_Lake_setupFile___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_Log_toString(lean_object*);
static lean_object* l_Lake_setupFile___closed__9;
static lean_object* l_Lake_setupFile___closed__4;
lean_object* l_Lake_Workspace_leanSrcPath(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Env_leanSrcPath(lean_object*);
lean_object* lean_module_name_of_file(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___at_Lake_setupFile___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_baseVars(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_append___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT uint32_t l_Lake_noConfigFileCode;
LEAN_EXPORT uint8_t l_Lake_setupFile___lambda__1(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
static lean_object* l_Lake_setupFile___closed__3;
extern lean_object* l_Lake_Module_setupFacet;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__1;
lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lake_mkModuleSetup___closed__2;
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__2;
lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_invalidConfigEnvVar;
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lake_BuildType_leanOptions(uint8_t);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
uint8_t l_Lake_ordBuildType____x40_Lake_Config_LeanConfig___hyg_267_(uint8_t, uint8_t);
static lean_object* l_Lake_serve___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkModuleSetup___closed__1;
lean_object* l_Lake_buildImportsAndDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___rarg(lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__3;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__4;
lean_object* l_Lake_ensureJob___at_Lake_Module_recFetchSetup___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___closed__2;
static lean_object* l_Lake_setupFile___closed__7;
lean_object* l_IO_println___at_Lean_Environment_displayStats___spec__3(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__1;
static lean_object* l_Lake_invalidConfigEnvVar___closed__1;
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
lean_object* l_Lean_parseImports_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkModuleSetup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___closed__8;
lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LoggerIO_captureLog___rarg(lean_object*, lean_object*);
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
lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_realConfigFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1___boxed(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recFetchSetup___spec__5(size_t, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lake_Workspace_leanPath(x_1);
x_4 = l_Lake_Workspace_leanSrcPath(x_1);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mkModuleSetup___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_mkModuleSetup___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_mkModuleSetup___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_mkModuleSetup(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_parseImports_x27(x_3, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
lean_dec(x_8);
lean_inc(x_10);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lake_buildImportsAndDeps), 8, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Lake_Workspace_runFetchM___rarg(x_1, x_12, x_5, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_io_wait(x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = lean_module_name_of_file(x_2, x_23, x_20);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_box(0);
x_28 = lean_array_size(x_21);
x_29 = 0;
x_30 = l_Array_mapMUnsafe_map___at_Lake_Module_recFetchSetup___spec__5(x_28, x_29, x_21);
x_31 = lean_array_size(x_22);
x_32 = l_Array_mapMUnsafe_map___at_Lake_Module_recFetchSetup___spec__5(x_31, x_29, x_22);
x_33 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_10);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_32);
lean_ctor_set(x_33, 5, x_4);
lean_ctor_set_uint8(x_33, sizeof(void*)*6, x_11);
lean_ctor_set(x_24, 0, x_33);
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_36 = lean_box(0);
x_37 = lean_array_size(x_21);
x_38 = 0;
x_39 = l_Array_mapMUnsafe_map___at_Lake_Module_recFetchSetup___spec__5(x_37, x_38, x_21);
x_40 = lean_array_size(x_22);
x_41 = l_Array_mapMUnsafe_map___at_Lake_Module_recFetchSetup___spec__5(x_40, x_38, x_22);
x_42 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_10);
lean_ctor_set(x_42, 2, x_36);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set(x_42, 5, x_4);
lean_ctor_set_uint8(x_42, sizeof(void*)*6, x_11);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_24);
if (x_44 == 0)
{
return x_24;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_24, 0);
x_46 = lean_ctor_get(x_24, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_24);
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
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_17);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_17, 0);
lean_dec(x_49);
x_50 = l_Lake_mkModuleSetup___closed__2;
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_50);
return x_17;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_dec(x_17);
x_52 = l_Lake_mkModuleSetup___closed__2;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_7);
if (x_58 == 0)
{
return x_7;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_7, 0);
x_60 = lean_ctor_get(x_7, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_7);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___at_Lake_setupFile___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = l_Lake_ensureJob___at_Lake_Module_recFetchSetup___spec__19(x_2, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":setup", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_LeanOptions_append___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to configure the Lake workspace. Please restart the server after fixing the error above.", 95, 95);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
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
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_21; uint8_t x_22; 
x_21 = l_Lake_resolvePath(x_2, x_4);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_312 = lean_ctor_get(x_1, 6);
lean_inc(x_312);
x_313 = l_Lake_realConfigFile(x_312, x_24);
x_314 = !lean_is_exclusive(x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_315 = lean_ctor_get(x_313, 0);
x_316 = lean_ctor_get(x_313, 1);
x_317 = lean_string_utf8_byte_size(x_315);
x_318 = lean_unsigned_to_nat(0u);
x_319 = lean_nat_dec_eq(x_317, x_318);
lean_dec(x_317);
if (x_319 == 0)
{
uint8_t x_320; 
lean_free_object(x_313);
x_320 = lean_string_dec_eq(x_315, x_23);
lean_dec(x_315);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_free_object(x_21);
x_321 = l_Lake_invalidConfigEnvVar;
x_322 = lean_io_getenv(x_321, x_316);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; uint8_t x_325; uint8_t x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_326 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
x_327 = lean_box(1);
x_328 = l_Lake_OutStream_get(x_327, x_324);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
lean_inc(x_329);
x_331 = l_Lake_AnsiMode_isEnabled(x_329, x_326, x_330);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = lean_box(x_325);
x_335 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__2___boxed), 5, 3);
lean_closure_set(x_335, 0, x_329);
lean_closure_set(x_335, 1, x_334);
lean_closure_set(x_335, 2, x_332);
x_336 = l_Lake_loadWorkspace(x_1, x_335, x_333);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_339, 0, x_337);
x_25 = x_339;
x_26 = x_338;
goto block_311;
}
else
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_336, 1);
lean_inc(x_340);
lean_dec(x_336);
x_341 = lean_box(0);
x_25 = x_341;
x_26 = x_340;
goto block_311;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_1);
x_342 = lean_ctor_get(x_322, 1);
lean_inc(x_342);
lean_dec(x_322);
x_343 = lean_ctor_get(x_323, 0);
lean_inc(x_343);
lean_dec(x_323);
x_344 = l_IO_eprint___at_IO_eprintln___spec__1(x_343, x_342);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
lean_dec(x_344);
x_346 = l_Lake_setupFile___closed__8;
x_347 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_346, x_345);
if (lean_obj_tag(x_347) == 0)
{
uint8_t x_348; 
x_348 = !lean_is_exclusive(x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_ctor_get(x_347, 0);
lean_dec(x_349);
x_350 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_347, 1);
lean_ctor_set(x_347, 0, x_350);
return x_347;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
lean_dec(x_347);
x_352 = l_Lake_setupFile___boxed__const__1;
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; uint8_t x_361; lean_object* x_362; uint8_t x_363; 
x_354 = lean_ctor_get(x_347, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_347, 1);
lean_inc(x_355);
lean_dec(x_347);
x_356 = lean_io_error_to_string(x_354);
x_357 = 3;
x_358 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*1, x_357);
x_359 = lean_box(1);
x_360 = 1;
x_361 = 0;
x_362 = l_Lake_OutStream_logEntry(x_359, x_358, x_360, x_361, x_355);
lean_dec(x_358);
x_363 = !lean_is_exclusive(x_362);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_362, 0);
lean_dec(x_364);
x_365 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_362, 1);
lean_ctor_set(x_362, 0, x_365);
return x_362;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_362, 1);
lean_inc(x_366);
lean_dec(x_362);
x_367 = l_Lake_setupFile___boxed__const__1;
x_368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; uint8_t x_376; lean_object* x_377; uint8_t x_378; 
x_369 = lean_ctor_get(x_344, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_344, 1);
lean_inc(x_370);
lean_dec(x_344);
x_371 = lean_io_error_to_string(x_369);
x_372 = 3;
x_373 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set_uint8(x_373, sizeof(void*)*1, x_372);
x_374 = lean_box(1);
x_375 = 1;
x_376 = 0;
x_377 = l_Lake_OutStream_logEntry(x_374, x_373, x_375, x_376, x_370);
lean_dec(x_373);
x_378 = !lean_is_exclusive(x_377);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_377, 0);
lean_dec(x_379);
x_380 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_377, 1);
lean_ctor_set(x_377, 0, x_380);
return x_377;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_377, 1);
lean_inc(x_381);
lean_dec(x_377);
x_382 = l_Lake_setupFile___boxed__const__1;
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_381);
return x_383;
}
}
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_23);
lean_dec(x_3);
x_384 = lean_ctor_get(x_1, 0);
lean_inc(x_384);
lean_dec(x_1);
x_385 = l_Lake_Env_leanPath(x_384);
x_386 = l_Lake_Env_leanSrcPath(x_384);
x_387 = lean_box(0);
x_388 = lean_ctor_get(x_384, 0);
lean_inc(x_388);
lean_dec(x_384);
x_389 = lean_ctor_get(x_388, 4);
lean_inc(x_389);
lean_dec(x_388);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
lean_dec(x_389);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_387);
lean_ctor_set(x_21, 0, x_390);
x_391 = lean_array_mk(x_21);
x_392 = l_Lake_setupFile___closed__9;
x_393 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_393, 0, x_385);
lean_ctor_set(x_393, 1, x_386);
lean_ctor_set(x_393, 2, x_392);
lean_ctor_set(x_393, 3, x_391);
x_394 = lean_box(0);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
x_396 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_395);
x_397 = l_Lean_Json_compress(x_396);
x_398 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_397, x_316);
if (lean_obj_tag(x_398) == 0)
{
uint8_t x_399; 
x_399 = !lean_is_exclusive(x_398);
if (x_399 == 0)
{
return x_398;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_398, 0);
x_401 = lean_ctor_get(x_398, 1);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_398);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
return x_402;
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; uint8_t x_410; lean_object* x_411; uint8_t x_412; 
x_403 = lean_ctor_get(x_398, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_398, 1);
lean_inc(x_404);
lean_dec(x_398);
x_405 = lean_io_error_to_string(x_403);
x_406 = 3;
x_407 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*1, x_406);
x_408 = lean_box(1);
x_409 = 1;
x_410 = 0;
x_411 = l_Lake_OutStream_logEntry(x_408, x_407, x_409, x_410, x_404);
lean_dec(x_407);
x_412 = !lean_is_exclusive(x_411);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_411, 0);
lean_dec(x_413);
x_414 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_411, 1);
lean_ctor_set(x_411, 0, x_414);
return x_411;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_411, 1);
lean_inc(x_415);
lean_dec(x_411);
x_416 = l_Lake_setupFile___boxed__const__1;
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
}
}
else
{
lean_object* x_418; 
lean_dec(x_315);
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_1);
x_418 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_313, 1);
lean_ctor_set(x_313, 0, x_418);
return x_313;
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_419 = lean_ctor_get(x_313, 0);
x_420 = lean_ctor_get(x_313, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_313);
x_421 = lean_string_utf8_byte_size(x_419);
x_422 = lean_unsigned_to_nat(0u);
x_423 = lean_nat_dec_eq(x_421, x_422);
lean_dec(x_421);
if (x_423 == 0)
{
uint8_t x_424; 
x_424 = lean_string_dec_eq(x_419, x_23);
lean_dec(x_419);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_free_object(x_21);
x_425 = l_Lake_invalidConfigEnvVar;
x_426 = lean_io_getenv(x_425, x_420);
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; uint8_t x_429; uint8_t x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_430 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
x_431 = lean_box(1);
x_432 = l_Lake_OutStream_get(x_431, x_428);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec(x_432);
lean_inc(x_433);
x_435 = l_Lake_AnsiMode_isEnabled(x_433, x_430, x_434);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
x_438 = lean_box(x_429);
x_439 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__2___boxed), 5, 3);
lean_closure_set(x_439, 0, x_433);
lean_closure_set(x_439, 1, x_438);
lean_closure_set(x_439, 2, x_436);
x_440 = l_Lake_loadWorkspace(x_1, x_439, x_437);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_443 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_443, 0, x_441);
x_25 = x_443;
x_26 = x_442;
goto block_311;
}
else
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_440, 1);
lean_inc(x_444);
lean_dec(x_440);
x_445 = lean_box(0);
x_25 = x_445;
x_26 = x_444;
goto block_311;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_1);
x_446 = lean_ctor_get(x_426, 1);
lean_inc(x_446);
lean_dec(x_426);
x_447 = lean_ctor_get(x_427, 0);
lean_inc(x_447);
lean_dec(x_427);
x_448 = l_IO_eprint___at_IO_eprintln___spec__1(x_447, x_446);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
lean_dec(x_448);
x_450 = l_Lake_setupFile___closed__8;
x_451 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_450, x_449);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_453 = x_451;
} else {
 lean_dec_ref(x_451);
 x_453 = lean_box(0);
}
x_454 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_453)) {
 x_455 = lean_alloc_ctor(1, 2, 0);
} else {
 x_455 = x_453;
 lean_ctor_set_tag(x_455, 1);
}
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_452);
return x_455;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; uint8_t x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_456 = lean_ctor_get(x_451, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_451, 1);
lean_inc(x_457);
lean_dec(x_451);
x_458 = lean_io_error_to_string(x_456);
x_459 = 3;
x_460 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set_uint8(x_460, sizeof(void*)*1, x_459);
x_461 = lean_box(1);
x_462 = 1;
x_463 = 0;
x_464 = l_Lake_OutStream_logEntry(x_461, x_460, x_462, x_463, x_457);
lean_dec(x_460);
x_465 = lean_ctor_get(x_464, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_466 = x_464;
} else {
 lean_dec_ref(x_464);
 x_466 = lean_box(0);
}
x_467 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_466)) {
 x_468 = lean_alloc_ctor(1, 2, 0);
} else {
 x_468 = x_466;
 lean_ctor_set_tag(x_468, 1);
}
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_465);
return x_468;
}
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; uint8_t x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_469 = lean_ctor_get(x_448, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_448, 1);
lean_inc(x_470);
lean_dec(x_448);
x_471 = lean_io_error_to_string(x_469);
x_472 = 3;
x_473 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set_uint8(x_473, sizeof(void*)*1, x_472);
x_474 = lean_box(1);
x_475 = 1;
x_476 = 0;
x_477 = l_Lake_OutStream_logEntry(x_474, x_473, x_475, x_476, x_470);
lean_dec(x_473);
x_478 = lean_ctor_get(x_477, 1);
lean_inc(x_478);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_479 = x_477;
} else {
 lean_dec_ref(x_477);
 x_479 = lean_box(0);
}
x_480 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_479)) {
 x_481 = lean_alloc_ctor(1, 2, 0);
} else {
 x_481 = x_479;
 lean_ctor_set_tag(x_481, 1);
}
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_478);
return x_481;
}
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_23);
lean_dec(x_3);
x_482 = lean_ctor_get(x_1, 0);
lean_inc(x_482);
lean_dec(x_1);
x_483 = l_Lake_Env_leanPath(x_482);
x_484 = l_Lake_Env_leanSrcPath(x_482);
x_485 = lean_box(0);
x_486 = lean_ctor_get(x_482, 0);
lean_inc(x_486);
lean_dec(x_482);
x_487 = lean_ctor_get(x_486, 4);
lean_inc(x_487);
lean_dec(x_486);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
lean_dec(x_487);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_485);
lean_ctor_set(x_21, 0, x_488);
x_489 = lean_array_mk(x_21);
x_490 = l_Lake_setupFile___closed__9;
x_491 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_491, 0, x_483);
lean_ctor_set(x_491, 1, x_484);
lean_ctor_set(x_491, 2, x_490);
lean_ctor_set(x_491, 3, x_489);
x_492 = lean_box(0);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_492);
x_494 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_493);
x_495 = l_Lean_Json_compress(x_494);
x_496 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_495, x_420);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_499 = x_496;
} else {
 lean_dec_ref(x_496);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; uint8_t x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_501 = lean_ctor_get(x_496, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_496, 1);
lean_inc(x_502);
lean_dec(x_496);
x_503 = lean_io_error_to_string(x_501);
x_504 = 3;
x_505 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set_uint8(x_505, sizeof(void*)*1, x_504);
x_506 = lean_box(1);
x_507 = 1;
x_508 = 0;
x_509 = l_Lake_OutStream_logEntry(x_506, x_505, x_507, x_508, x_502);
lean_dec(x_505);
x_510 = lean_ctor_get(x_509, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_511 = x_509;
} else {
 lean_dec_ref(x_509);
 x_511 = lean_box(0);
}
x_512 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_511)) {
 x_513 = lean_alloc_ctor(1, 2, 0);
} else {
 x_513 = x_511;
 lean_ctor_set_tag(x_513, 1);
}
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_510);
return x_513;
}
}
}
else
{
lean_object* x_514; lean_object* x_515; 
lean_dec(x_419);
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_1);
x_514 = l_Lake_setupFile___boxed__const__2;
x_515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_420);
return x_515;
}
}
block_311:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_23);
lean_dec(x_3);
x_27 = lean_box(1);
x_28 = l_Lake_setupFile___closed__2;
x_29 = 1;
x_30 = 0;
x_31 = l_Lake_OutStream_logEntry(x_27, x_28, x_29, x_30, x_26);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lake_setupFile___boxed__const__1;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
lean_inc(x_23);
x_39 = l_Lake_Workspace_findModuleBySrc_x3f(x_23, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = l_IO_FS_readFile(x_23, x_26);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 3);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = l_Lean_LeanOptions_ofArray(x_46);
lean_dec(x_46);
x_48 = lean_ctor_get(x_45, 4);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l_Lean_LeanOptions_appendArray(x_47, x_48);
lean_dec(x_48);
lean_inc(x_38);
x_50 = l_Lake_mkModuleSetup(x_38, x_23, x_41, x_49, x_3, x_42);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_38, x_52);
lean_dec(x_38);
x_55 = lean_ctor_get(x_52, 5);
lean_inc(x_55);
lean_dec(x_52);
lean_ctor_set(x_50, 1, x_55);
lean_ctor_set(x_50, 0, x_54);
x_56 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_50);
x_57 = l_Lean_Json_compress(x_56);
x_58 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_57, x_53);
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
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_50, 0);
x_79 = lean_ctor_get(x_50, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_50);
x_80 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_38, x_78);
lean_dec(x_38);
x_81 = lean_ctor_get(x_78, 5);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_82);
x_84 = l_Lean_Json_compress(x_83);
x_85 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_84, x_79);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_dec(x_85);
x_92 = lean_io_error_to_string(x_90);
x_93 = 3;
x_94 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_93);
x_95 = lean_box(1);
x_96 = 1;
x_97 = 0;
x_98 = l_Lake_OutStream_logEntry(x_95, x_94, x_96, x_97, x_91);
lean_dec(x_94);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_100;
 lean_ctor_set_tag(x_102, 1);
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_38);
x_103 = lean_ctor_get(x_50, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_50, 1);
lean_inc(x_104);
lean_dec(x_50);
x_105 = lean_io_error_to_string(x_103);
x_106 = 3;
x_107 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_106);
x_108 = lean_box(1);
x_109 = 1;
x_110 = 0;
x_111 = l_Lake_OutStream_logEntry(x_108, x_107, x_109, x_110, x_104);
lean_dec(x_107);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
lean_dec(x_113);
x_114 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_111, 1);
lean_ctor_set(x_111, 0, x_114);
return x_111;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_dec(x_111);
x_116 = l_Lake_setupFile___boxed__const__1;
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_3);
x_118 = lean_ctor_get(x_40, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_40, 1);
lean_inc(x_119);
lean_dec(x_40);
x_120 = lean_io_error_to_string(x_118);
x_121 = 3;
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_121);
x_123 = lean_box(1);
x_124 = 1;
x_125 = 0;
x_126 = l_Lake_OutStream_logEntry(x_123, x_122, x_124, x_125, x_119);
lean_dec(x_122);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_126, 0);
lean_dec(x_128);
x_129 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_126, 1);
lean_ctor_set(x_126, 0, x_129);
return x_126;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_126, 1);
lean_inc(x_130);
lean_dec(x_126);
x_131 = l_Lake_setupFile___boxed__const__1;
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_23);
x_133 = !lean_is_exclusive(x_39);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_134 = lean_ctor_get(x_39, 0);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
x_136 = 1;
x_137 = l_Lake_setupFile___closed__3;
x_138 = l_Lean_Name_toString(x_135, x_136, x_137);
x_139 = l_Lake_setupFile___closed__4;
x_140 = lean_string_append(x_139, x_138);
lean_dec(x_138);
x_141 = l_Lake_setupFile___closed__5;
x_142 = lean_string_append(x_140, x_141);
x_143 = lean_ctor_get(x_134, 2);
lean_inc(x_143);
lean_ctor_set_tag(x_39, 0);
lean_ctor_set(x_39, 0, x_143);
x_144 = l_Lake_Module_keyword;
x_145 = l_Lake_Module_setupFacet;
lean_inc(x_134);
x_146 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_146, 0, x_39);
lean_ctor_set(x_146, 1, x_144);
lean_ctor_set(x_146, 2, x_134);
lean_ctor_set(x_146, 3, x_145);
x_147 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_147, 0, x_146);
lean_closure_set(x_147, 1, lean_box(0));
x_148 = 0;
x_149 = lean_box(x_148);
x_150 = lean_alloc_closure((void*)(l_Lake_withRegisterJob___at_Lake_setupFile___spec__1___boxed), 9, 3);
lean_closure_set(x_150, 0, x_142);
lean_closure_set(x_150, 1, x_147);
lean_closure_set(x_150, 2, x_149);
lean_inc(x_38);
x_151 = l_Lake_Workspace_runFetchM___rarg(x_38, x_150, x_3, x_26);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_io_wait(x_154, x_153);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_38, x_158);
lean_dec(x_158);
lean_dec(x_38);
x_186 = lean_ctor_get(x_134, 0);
lean_inc(x_186);
lean_dec(x_134);
x_187 = lean_box(0);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_188, 3);
lean_inc(x_189);
lean_dec(x_188);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_191 = lean_ctor_get_uint8(x_190, sizeof(void*)*13);
x_192 = lean_ctor_get(x_186, 2);
lean_inc(x_192);
lean_dec(x_186);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_ctor_get_uint8(x_193, sizeof(void*)*13);
x_195 = l_Lake_ordBuildType____x40_Lake_Config_LeanConfig___hyg_267_(x_191, x_194);
x_196 = lean_ctor_get(x_190, 0);
lean_inc(x_196);
x_197 = l_Lean_LeanOptions_ofArray(x_196);
lean_dec(x_196);
x_198 = lean_ctor_get(x_190, 4);
lean_inc(x_198);
lean_dec(x_190);
x_199 = l_Lean_LeanOptions_appendArray(x_197, x_198);
lean_dec(x_198);
x_200 = lean_box(x_195);
if (lean_obj_tag(x_200) == 2)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_201 = lean_ctor_get(x_193, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_193, 4);
lean_inc(x_202);
lean_dec(x_193);
x_203 = l_Lake_BuildType_leanOptions(x_194);
x_204 = l_Lake_setupFile___closed__6;
x_205 = l_Lake_setupFile___closed__7;
x_206 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_204, x_205, x_187, x_203);
x_207 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_204, x_205, x_206, x_199);
x_208 = l_Lean_LeanOptions_appendArray(x_207, x_201);
lean_dec(x_201);
x_209 = l_Lean_LeanOptions_appendArray(x_208, x_202);
lean_dec(x_202);
x_161 = x_209;
goto block_185;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_200);
x_210 = lean_ctor_get(x_193, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_193, 4);
lean_inc(x_211);
lean_dec(x_193);
x_212 = l_Lake_BuildType_leanOptions(x_191);
x_213 = l_Lake_setupFile___closed__6;
x_214 = l_Lake_setupFile___closed__7;
x_215 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_213, x_214, x_187, x_212);
x_216 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_213, x_214, x_215, x_199);
x_217 = l_Lean_LeanOptions_appendArray(x_216, x_210);
lean_dec(x_210);
x_218 = l_Lean_LeanOptions_appendArray(x_217, x_211);
lean_dec(x_211);
x_161 = x_218;
goto block_185;
}
block_185:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
if (lean_is_scalar(x_159)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_159;
}
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_162);
x_164 = l_Lean_Json_compress(x_163);
x_165 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_164, x_157);
if (lean_obj_tag(x_165) == 0)
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
return x_165;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_165, 0);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_165);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_177; lean_object* x_178; uint8_t x_179; 
x_170 = lean_ctor_get(x_165, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_165, 1);
lean_inc(x_171);
lean_dec(x_165);
x_172 = lean_io_error_to_string(x_170);
x_173 = 3;
x_174 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_173);
x_175 = lean_box(1);
x_176 = 1;
x_177 = 0;
x_178 = l_Lake_OutStream_logEntry(x_175, x_174, x_176, x_177, x_171);
lean_dec(x_174);
x_179 = !lean_is_exclusive(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_178, 0);
lean_dec(x_180);
x_181 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_178, 1);
lean_ctor_set(x_178, 0, x_181);
return x_178;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_178, 1);
lean_inc(x_182);
lean_dec(x_178);
x_183 = l_Lake_setupFile___boxed__const__1;
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
}
}
else
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_156);
lean_dec(x_134);
lean_dec(x_38);
x_219 = lean_ctor_get(x_155, 1);
lean_inc(x_219);
lean_dec(x_155);
x_220 = l_Lake_mkModuleSetup___closed__2;
x_5 = x_220;
x_6 = x_219;
goto block_20;
}
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_134);
lean_dec(x_38);
x_221 = lean_ctor_get(x_151, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_151, 1);
lean_inc(x_222);
lean_dec(x_151);
x_5 = x_221;
x_6 = x_222;
goto block_20;
}
}
else
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_223 = lean_ctor_get(x_39, 0);
lean_inc(x_223);
lean_dec(x_39);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
x_225 = 1;
x_226 = l_Lake_setupFile___closed__3;
x_227 = l_Lean_Name_toString(x_224, x_225, x_226);
x_228 = l_Lake_setupFile___closed__4;
x_229 = lean_string_append(x_228, x_227);
lean_dec(x_227);
x_230 = l_Lake_setupFile___closed__5;
x_231 = lean_string_append(x_229, x_230);
x_232 = lean_ctor_get(x_223, 2);
lean_inc(x_232);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_232);
x_234 = l_Lake_Module_keyword;
x_235 = l_Lake_Module_setupFacet;
lean_inc(x_223);
x_236 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
lean_ctor_set(x_236, 2, x_223);
lean_ctor_set(x_236, 3, x_235);
x_237 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_237, 0, x_236);
lean_closure_set(x_237, 1, lean_box(0));
x_238 = 0;
x_239 = lean_box(x_238);
x_240 = lean_alloc_closure((void*)(l_Lake_withRegisterJob___at_Lake_setupFile___spec__1___boxed), 9, 3);
lean_closure_set(x_240, 0, x_231);
lean_closure_set(x_240, 1, x_237);
lean_closure_set(x_240, 2, x_239);
lean_inc(x_38);
x_241 = l_Lake_Workspace_runFetchM___rarg(x_38, x_240, x_3, x_26);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_ctor_get(x_242, 0);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_io_wait(x_244, x_243);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
x_250 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_38, x_248);
lean_dec(x_248);
lean_dec(x_38);
x_274 = lean_ctor_get(x_223, 0);
lean_inc(x_274);
lean_dec(x_223);
x_275 = lean_box(0);
x_276 = lean_ctor_get(x_274, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_276, 3);
lean_inc(x_277);
lean_dec(x_276);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
x_279 = lean_ctor_get_uint8(x_278, sizeof(void*)*13);
x_280 = lean_ctor_get(x_274, 2);
lean_inc(x_280);
lean_dec(x_274);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
lean_dec(x_280);
x_282 = lean_ctor_get_uint8(x_281, sizeof(void*)*13);
x_283 = l_Lake_ordBuildType____x40_Lake_Config_LeanConfig___hyg_267_(x_279, x_282);
x_284 = lean_ctor_get(x_278, 0);
lean_inc(x_284);
x_285 = l_Lean_LeanOptions_ofArray(x_284);
lean_dec(x_284);
x_286 = lean_ctor_get(x_278, 4);
lean_inc(x_286);
lean_dec(x_278);
x_287 = l_Lean_LeanOptions_appendArray(x_285, x_286);
lean_dec(x_286);
x_288 = lean_box(x_283);
if (lean_obj_tag(x_288) == 2)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_289 = lean_ctor_get(x_281, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_281, 4);
lean_inc(x_290);
lean_dec(x_281);
x_291 = l_Lake_BuildType_leanOptions(x_282);
x_292 = l_Lake_setupFile___closed__6;
x_293 = l_Lake_setupFile___closed__7;
x_294 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_292, x_293, x_275, x_291);
x_295 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_292, x_293, x_294, x_287);
x_296 = l_Lean_LeanOptions_appendArray(x_295, x_289);
lean_dec(x_289);
x_297 = l_Lean_LeanOptions_appendArray(x_296, x_290);
lean_dec(x_290);
x_251 = x_297;
goto block_273;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_288);
x_298 = lean_ctor_get(x_281, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_281, 4);
lean_inc(x_299);
lean_dec(x_281);
x_300 = l_Lake_BuildType_leanOptions(x_279);
x_301 = l_Lake_setupFile___closed__6;
x_302 = l_Lake_setupFile___closed__7;
x_303 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_301, x_302, x_275, x_300);
x_304 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_301, x_302, x_303, x_287);
x_305 = l_Lean_LeanOptions_appendArray(x_304, x_298);
lean_dec(x_298);
x_306 = l_Lean_LeanOptions_appendArray(x_305, x_299);
lean_dec(x_299);
x_251 = x_306;
goto block_273;
}
block_273:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
if (lean_is_scalar(x_249)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_249;
}
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_252);
x_254 = l_Lean_Json_compress(x_253);
x_255 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_254, x_247);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_258 = x_255;
} else {
 lean_dec_ref(x_255);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_260 = lean_ctor_get(x_255, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_255, 1);
lean_inc(x_261);
lean_dec(x_255);
x_262 = lean_io_error_to_string(x_260);
x_263 = 3;
x_264 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set_uint8(x_264, sizeof(void*)*1, x_263);
x_265 = lean_box(1);
x_266 = 1;
x_267 = 0;
x_268 = l_Lake_OutStream_logEntry(x_265, x_264, x_266, x_267, x_261);
lean_dec(x_264);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_270 = x_268;
} else {
 lean_dec_ref(x_268);
 x_270 = lean_box(0);
}
x_271 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_270)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_270;
 lean_ctor_set_tag(x_272, 1);
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_269);
return x_272;
}
}
}
else
{
lean_object* x_307; lean_object* x_308; 
lean_dec(x_246);
lean_dec(x_223);
lean_dec(x_38);
x_307 = lean_ctor_get(x_245, 1);
lean_inc(x_307);
lean_dec(x_245);
x_308 = l_Lake_mkModuleSetup___closed__2;
x_5 = x_308;
x_6 = x_307;
goto block_20;
}
}
else
{
lean_object* x_309; lean_object* x_310; 
lean_dec(x_223);
lean_dec(x_38);
x_309 = lean_ctor_get(x_241, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_241, 1);
lean_inc(x_310);
lean_dec(x_241);
x_5 = x_309;
x_6 = x_310;
goto block_20;
}
}
}
}
}
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; uint8_t x_691; 
x_516 = lean_ctor_get(x_21, 0);
x_517 = lean_ctor_get(x_21, 1);
lean_inc(x_517);
lean_inc(x_516);
lean_dec(x_21);
x_684 = lean_ctor_get(x_1, 6);
lean_inc(x_684);
x_685 = l_Lake_realConfigFile(x_684, x_517);
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_688 = x_685;
} else {
 lean_dec_ref(x_685);
 x_688 = lean_box(0);
}
x_689 = lean_string_utf8_byte_size(x_686);
x_690 = lean_unsigned_to_nat(0u);
x_691 = lean_nat_dec_eq(x_689, x_690);
lean_dec(x_689);
if (x_691 == 0)
{
uint8_t x_692; 
lean_dec(x_688);
x_692 = lean_string_dec_eq(x_686, x_516);
lean_dec(x_686);
if (x_692 == 0)
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_693 = l_Lake_invalidConfigEnvVar;
x_694 = lean_io_getenv(x_693, x_687);
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; uint8_t x_697; uint8_t x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_696 = lean_ctor_get(x_694, 1);
lean_inc(x_696);
lean_dec(x_694);
x_697 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_698 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
x_699 = lean_box(1);
x_700 = l_Lake_OutStream_get(x_699, x_696);
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
lean_dec(x_700);
lean_inc(x_701);
x_703 = l_Lake_AnsiMode_isEnabled(x_701, x_698, x_702);
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_703, 1);
lean_inc(x_705);
lean_dec(x_703);
x_706 = lean_box(x_697);
x_707 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__2___boxed), 5, 3);
lean_closure_set(x_707, 0, x_701);
lean_closure_set(x_707, 1, x_706);
lean_closure_set(x_707, 2, x_704);
x_708 = l_Lake_loadWorkspace(x_1, x_707, x_705);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_708, 1);
lean_inc(x_710);
lean_dec(x_708);
x_711 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_711, 0, x_709);
x_518 = x_711;
x_519 = x_710;
goto block_683;
}
else
{
lean_object* x_712; lean_object* x_713; 
x_712 = lean_ctor_get(x_708, 1);
lean_inc(x_712);
lean_dec(x_708);
x_713 = lean_box(0);
x_518 = x_713;
x_519 = x_712;
goto block_683;
}
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_dec(x_516);
lean_dec(x_3);
lean_dec(x_1);
x_714 = lean_ctor_get(x_694, 1);
lean_inc(x_714);
lean_dec(x_694);
x_715 = lean_ctor_get(x_695, 0);
lean_inc(x_715);
lean_dec(x_695);
x_716 = l_IO_eprint___at_IO_eprintln___spec__1(x_715, x_714);
if (lean_obj_tag(x_716) == 0)
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_716, 1);
lean_inc(x_717);
lean_dec(x_716);
x_718 = l_Lake_setupFile___closed__8;
x_719 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_718, x_717);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_720 = lean_ctor_get(x_719, 1);
lean_inc(x_720);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_721 = x_719;
} else {
 lean_dec_ref(x_719);
 x_721 = lean_box(0);
}
x_722 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_721)) {
 x_723 = lean_alloc_ctor(1, 2, 0);
} else {
 x_723 = x_721;
 lean_ctor_set_tag(x_723, 1);
}
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_720);
return x_723;
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; uint8_t x_727; lean_object* x_728; lean_object* x_729; uint8_t x_730; uint8_t x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_724 = lean_ctor_get(x_719, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_719, 1);
lean_inc(x_725);
lean_dec(x_719);
x_726 = lean_io_error_to_string(x_724);
x_727 = 3;
x_728 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_728, 0, x_726);
lean_ctor_set_uint8(x_728, sizeof(void*)*1, x_727);
x_729 = lean_box(1);
x_730 = 1;
x_731 = 0;
x_732 = l_Lake_OutStream_logEntry(x_729, x_728, x_730, x_731, x_725);
lean_dec(x_728);
x_733 = lean_ctor_get(x_732, 1);
lean_inc(x_733);
if (lean_is_exclusive(x_732)) {
 lean_ctor_release(x_732, 0);
 lean_ctor_release(x_732, 1);
 x_734 = x_732;
} else {
 lean_dec_ref(x_732);
 x_734 = lean_box(0);
}
x_735 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_734)) {
 x_736 = lean_alloc_ctor(1, 2, 0);
} else {
 x_736 = x_734;
 lean_ctor_set_tag(x_736, 1);
}
lean_ctor_set(x_736, 0, x_735);
lean_ctor_set(x_736, 1, x_733);
return x_736;
}
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; uint8_t x_740; lean_object* x_741; lean_object* x_742; uint8_t x_743; uint8_t x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_737 = lean_ctor_get(x_716, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_716, 1);
lean_inc(x_738);
lean_dec(x_716);
x_739 = lean_io_error_to_string(x_737);
x_740 = 3;
x_741 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_741, 0, x_739);
lean_ctor_set_uint8(x_741, sizeof(void*)*1, x_740);
x_742 = lean_box(1);
x_743 = 1;
x_744 = 0;
x_745 = l_Lake_OutStream_logEntry(x_742, x_741, x_743, x_744, x_738);
lean_dec(x_741);
x_746 = lean_ctor_get(x_745, 1);
lean_inc(x_746);
if (lean_is_exclusive(x_745)) {
 lean_ctor_release(x_745, 0);
 lean_ctor_release(x_745, 1);
 x_747 = x_745;
} else {
 lean_dec_ref(x_745);
 x_747 = lean_box(0);
}
x_748 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_747)) {
 x_749 = lean_alloc_ctor(1, 2, 0);
} else {
 x_749 = x_747;
 lean_ctor_set_tag(x_749, 1);
}
lean_ctor_set(x_749, 0, x_748);
lean_ctor_set(x_749, 1, x_746);
return x_749;
}
}
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
lean_dec(x_516);
lean_dec(x_3);
x_750 = lean_ctor_get(x_1, 0);
lean_inc(x_750);
lean_dec(x_1);
x_751 = l_Lake_Env_leanPath(x_750);
x_752 = l_Lake_Env_leanSrcPath(x_750);
x_753 = lean_box(0);
x_754 = lean_ctor_get(x_750, 0);
lean_inc(x_754);
lean_dec(x_750);
x_755 = lean_ctor_get(x_754, 4);
lean_inc(x_755);
lean_dec(x_754);
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
lean_dec(x_755);
x_757 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_757, 0, x_756);
lean_ctor_set(x_757, 1, x_753);
x_758 = lean_array_mk(x_757);
x_759 = l_Lake_setupFile___closed__9;
x_760 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_760, 0, x_751);
lean_ctor_set(x_760, 1, x_752);
lean_ctor_set(x_760, 2, x_759);
lean_ctor_set(x_760, 3, x_758);
x_761 = lean_box(0);
x_762 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_762, 0, x_760);
lean_ctor_set(x_762, 1, x_761);
x_763 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_762);
x_764 = l_Lean_Json_compress(x_763);
x_765 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_764, x_687);
if (lean_obj_tag(x_765) == 0)
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_766 = lean_ctor_get(x_765, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_765, 1);
lean_inc(x_767);
if (lean_is_exclusive(x_765)) {
 lean_ctor_release(x_765, 0);
 lean_ctor_release(x_765, 1);
 x_768 = x_765;
} else {
 lean_dec_ref(x_765);
 x_768 = lean_box(0);
}
if (lean_is_scalar(x_768)) {
 x_769 = lean_alloc_ctor(0, 2, 0);
} else {
 x_769 = x_768;
}
lean_ctor_set(x_769, 0, x_766);
lean_ctor_set(x_769, 1, x_767);
return x_769;
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; uint8_t x_773; lean_object* x_774; lean_object* x_775; uint8_t x_776; uint8_t x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_770 = lean_ctor_get(x_765, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_765, 1);
lean_inc(x_771);
lean_dec(x_765);
x_772 = lean_io_error_to_string(x_770);
x_773 = 3;
x_774 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_774, 0, x_772);
lean_ctor_set_uint8(x_774, sizeof(void*)*1, x_773);
x_775 = lean_box(1);
x_776 = 1;
x_777 = 0;
x_778 = l_Lake_OutStream_logEntry(x_775, x_774, x_776, x_777, x_771);
lean_dec(x_774);
x_779 = lean_ctor_get(x_778, 1);
lean_inc(x_779);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_780 = x_778;
} else {
 lean_dec_ref(x_778);
 x_780 = lean_box(0);
}
x_781 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_780)) {
 x_782 = lean_alloc_ctor(1, 2, 0);
} else {
 x_782 = x_780;
 lean_ctor_set_tag(x_782, 1);
}
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_779);
return x_782;
}
}
}
else
{
lean_object* x_783; lean_object* x_784; 
lean_dec(x_686);
lean_dec(x_516);
lean_dec(x_3);
lean_dec(x_1);
x_783 = l_Lake_setupFile___boxed__const__2;
if (lean_is_scalar(x_688)) {
 x_784 = lean_alloc_ctor(1, 2, 0);
} else {
 x_784 = x_688;
 lean_ctor_set_tag(x_784, 1);
}
lean_ctor_set(x_784, 0, x_783);
lean_ctor_set(x_784, 1, x_687);
return x_784;
}
block_683:
{
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_520; lean_object* x_521; uint8_t x_522; uint8_t x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_516);
lean_dec(x_3);
x_520 = lean_box(1);
x_521 = l_Lake_setupFile___closed__2;
x_522 = 1;
x_523 = 0;
x_524 = l_Lake_OutStream_logEntry(x_520, x_521, x_522, x_523, x_519);
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_526 = x_524;
} else {
 lean_dec_ref(x_524);
 x_526 = lean_box(0);
}
x_527 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_526)) {
 x_528 = lean_alloc_ctor(1, 2, 0);
} else {
 x_528 = x_526;
 lean_ctor_set_tag(x_528, 1);
}
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_525);
return x_528;
}
else
{
lean_object* x_529; lean_object* x_530; 
x_529 = lean_ctor_get(x_518, 0);
lean_inc(x_529);
lean_dec(x_518);
lean_inc(x_516);
x_530 = l_Lake_Workspace_findModuleBySrc_x3f(x_516, x_529);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; 
x_531 = l_IO_FS_readFile(x_516, x_519);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
lean_dec(x_531);
x_534 = lean_ctor_get(x_529, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_534, 3);
lean_inc(x_535);
lean_dec(x_534);
x_536 = lean_ctor_get(x_535, 1);
lean_inc(x_536);
lean_dec(x_535);
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = l_Lean_LeanOptions_ofArray(x_537);
lean_dec(x_537);
x_539 = lean_ctor_get(x_536, 4);
lean_inc(x_539);
lean_dec(x_536);
x_540 = l_Lean_LeanOptions_appendArray(x_538, x_539);
lean_dec(x_539);
lean_inc(x_529);
x_541 = l_Lake_mkModuleSetup(x_529, x_516, x_532, x_540, x_3, x_533);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_544 = x_541;
} else {
 lean_dec_ref(x_541);
 x_544 = lean_box(0);
}
x_545 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_529, x_542);
lean_dec(x_529);
x_546 = lean_ctor_get(x_542, 5);
lean_inc(x_546);
lean_dec(x_542);
if (lean_is_scalar(x_544)) {
 x_547 = lean_alloc_ctor(0, 2, 0);
} else {
 x_547 = x_544;
}
lean_ctor_set(x_547, 0, x_545);
lean_ctor_set(x_547, 1, x_546);
x_548 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_547);
x_549 = l_Lean_Json_compress(x_548);
x_550 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_549, x_543);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
if (lean_is_exclusive(x_550)) {
 lean_ctor_release(x_550, 0);
 lean_ctor_release(x_550, 1);
 x_553 = x_550;
} else {
 lean_dec_ref(x_550);
 x_553 = lean_box(0);
}
if (lean_is_scalar(x_553)) {
 x_554 = lean_alloc_ctor(0, 2, 0);
} else {
 x_554 = x_553;
}
lean_ctor_set(x_554, 0, x_551);
lean_ctor_set(x_554, 1, x_552);
return x_554;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; uint8_t x_558; lean_object* x_559; lean_object* x_560; uint8_t x_561; uint8_t x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_555 = lean_ctor_get(x_550, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_550, 1);
lean_inc(x_556);
lean_dec(x_550);
x_557 = lean_io_error_to_string(x_555);
x_558 = 3;
x_559 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_559, 0, x_557);
lean_ctor_set_uint8(x_559, sizeof(void*)*1, x_558);
x_560 = lean_box(1);
x_561 = 1;
x_562 = 0;
x_563 = l_Lake_OutStream_logEntry(x_560, x_559, x_561, x_562, x_556);
lean_dec(x_559);
x_564 = lean_ctor_get(x_563, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 lean_ctor_release(x_563, 1);
 x_565 = x_563;
} else {
 lean_dec_ref(x_563);
 x_565 = lean_box(0);
}
x_566 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_565)) {
 x_567 = lean_alloc_ctor(1, 2, 0);
} else {
 x_567 = x_565;
 lean_ctor_set_tag(x_567, 1);
}
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_564);
return x_567;
}
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; uint8_t x_571; lean_object* x_572; lean_object* x_573; uint8_t x_574; uint8_t x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_529);
x_568 = lean_ctor_get(x_541, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_541, 1);
lean_inc(x_569);
lean_dec(x_541);
x_570 = lean_io_error_to_string(x_568);
x_571 = 3;
x_572 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_572, 0, x_570);
lean_ctor_set_uint8(x_572, sizeof(void*)*1, x_571);
x_573 = lean_box(1);
x_574 = 1;
x_575 = 0;
x_576 = l_Lake_OutStream_logEntry(x_573, x_572, x_574, x_575, x_569);
lean_dec(x_572);
x_577 = lean_ctor_get(x_576, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_578 = x_576;
} else {
 lean_dec_ref(x_576);
 x_578 = lean_box(0);
}
x_579 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_578)) {
 x_580 = lean_alloc_ctor(1, 2, 0);
} else {
 x_580 = x_578;
 lean_ctor_set_tag(x_580, 1);
}
lean_ctor_set(x_580, 0, x_579);
lean_ctor_set(x_580, 1, x_577);
return x_580;
}
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; uint8_t x_584; lean_object* x_585; lean_object* x_586; uint8_t x_587; uint8_t x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
lean_dec(x_529);
lean_dec(x_516);
lean_dec(x_3);
x_581 = lean_ctor_get(x_531, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_531, 1);
lean_inc(x_582);
lean_dec(x_531);
x_583 = lean_io_error_to_string(x_581);
x_584 = 3;
x_585 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set_uint8(x_585, sizeof(void*)*1, x_584);
x_586 = lean_box(1);
x_587 = 1;
x_588 = 0;
x_589 = l_Lake_OutStream_logEntry(x_586, x_585, x_587, x_588, x_582);
lean_dec(x_585);
x_590 = lean_ctor_get(x_589, 1);
lean_inc(x_590);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 lean_ctor_release(x_589, 1);
 x_591 = x_589;
} else {
 lean_dec_ref(x_589);
 x_591 = lean_box(0);
}
x_592 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_591)) {
 x_593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_593 = x_591;
 lean_ctor_set_tag(x_593, 1);
}
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_590);
return x_593;
}
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; uint8_t x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_516);
x_594 = lean_ctor_get(x_530, 0);
lean_inc(x_594);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 x_595 = x_530;
} else {
 lean_dec_ref(x_530);
 x_595 = lean_box(0);
}
x_596 = lean_ctor_get(x_594, 1);
lean_inc(x_596);
x_597 = 1;
x_598 = l_Lake_setupFile___closed__3;
x_599 = l_Lean_Name_toString(x_596, x_597, x_598);
x_600 = l_Lake_setupFile___closed__4;
x_601 = lean_string_append(x_600, x_599);
lean_dec(x_599);
x_602 = l_Lake_setupFile___closed__5;
x_603 = lean_string_append(x_601, x_602);
x_604 = lean_ctor_get(x_594, 2);
lean_inc(x_604);
if (lean_is_scalar(x_595)) {
 x_605 = lean_alloc_ctor(0, 1, 0);
} else {
 x_605 = x_595;
 lean_ctor_set_tag(x_605, 0);
}
lean_ctor_set(x_605, 0, x_604);
x_606 = l_Lake_Module_keyword;
x_607 = l_Lake_Module_setupFacet;
lean_inc(x_594);
x_608 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_608, 0, x_605);
lean_ctor_set(x_608, 1, x_606);
lean_ctor_set(x_608, 2, x_594);
lean_ctor_set(x_608, 3, x_607);
x_609 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_609, 0, x_608);
lean_closure_set(x_609, 1, lean_box(0));
x_610 = 0;
x_611 = lean_box(x_610);
x_612 = lean_alloc_closure((void*)(l_Lake_withRegisterJob___at_Lake_setupFile___spec__1___boxed), 9, 3);
lean_closure_set(x_612, 0, x_603);
lean_closure_set(x_612, 1, x_609);
lean_closure_set(x_612, 2, x_611);
lean_inc(x_529);
x_613 = l_Lake_Workspace_runFetchM___rarg(x_529, x_612, x_3, x_519);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec(x_613);
x_616 = lean_ctor_get(x_614, 0);
lean_inc(x_616);
lean_dec(x_614);
x_617 = lean_io_wait(x_616, x_615);
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; uint8_t x_651; lean_object* x_652; lean_object* x_653; uint8_t x_654; uint8_t x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
x_620 = lean_ctor_get(x_618, 0);
lean_inc(x_620);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 lean_ctor_release(x_618, 1);
 x_621 = x_618;
} else {
 lean_dec_ref(x_618);
 x_621 = lean_box(0);
}
x_622 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_529, x_620);
lean_dec(x_620);
lean_dec(x_529);
x_646 = lean_ctor_get(x_594, 0);
lean_inc(x_646);
lean_dec(x_594);
x_647 = lean_box(0);
x_648 = lean_ctor_get(x_646, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_648, 3);
lean_inc(x_649);
lean_dec(x_648);
x_650 = lean_ctor_get(x_649, 1);
lean_inc(x_650);
lean_dec(x_649);
x_651 = lean_ctor_get_uint8(x_650, sizeof(void*)*13);
x_652 = lean_ctor_get(x_646, 2);
lean_inc(x_652);
lean_dec(x_646);
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
lean_dec(x_652);
x_654 = lean_ctor_get_uint8(x_653, sizeof(void*)*13);
x_655 = l_Lake_ordBuildType____x40_Lake_Config_LeanConfig___hyg_267_(x_651, x_654);
x_656 = lean_ctor_get(x_650, 0);
lean_inc(x_656);
x_657 = l_Lean_LeanOptions_ofArray(x_656);
lean_dec(x_656);
x_658 = lean_ctor_get(x_650, 4);
lean_inc(x_658);
lean_dec(x_650);
x_659 = l_Lean_LeanOptions_appendArray(x_657, x_658);
lean_dec(x_658);
x_660 = lean_box(x_655);
if (lean_obj_tag(x_660) == 2)
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_661 = lean_ctor_get(x_653, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_653, 4);
lean_inc(x_662);
lean_dec(x_653);
x_663 = l_Lake_BuildType_leanOptions(x_654);
x_664 = l_Lake_setupFile___closed__6;
x_665 = l_Lake_setupFile___closed__7;
x_666 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_664, x_665, x_647, x_663);
x_667 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_664, x_665, x_666, x_659);
x_668 = l_Lean_LeanOptions_appendArray(x_667, x_661);
lean_dec(x_661);
x_669 = l_Lean_LeanOptions_appendArray(x_668, x_662);
lean_dec(x_662);
x_623 = x_669;
goto block_645;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_660);
x_670 = lean_ctor_get(x_653, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_653, 4);
lean_inc(x_671);
lean_dec(x_653);
x_672 = l_Lake_BuildType_leanOptions(x_651);
x_673 = l_Lake_setupFile___closed__6;
x_674 = l_Lake_setupFile___closed__7;
x_675 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_673, x_674, x_647, x_672);
x_676 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_673, x_674, x_675, x_659);
x_677 = l_Lean_LeanOptions_appendArray(x_676, x_670);
lean_dec(x_670);
x_678 = l_Lean_LeanOptions_appendArray(x_677, x_671);
lean_dec(x_671);
x_623 = x_678;
goto block_645;
}
block_645:
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
if (lean_is_scalar(x_621)) {
 x_624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_624 = x_621;
}
lean_ctor_set(x_624, 0, x_622);
lean_ctor_set(x_624, 1, x_623);
x_625 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_624);
x_626 = l_Lean_Json_compress(x_625);
x_627 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_626, x_619);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_628 = lean_ctor_get(x_627, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_627, 1);
lean_inc(x_629);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 lean_ctor_release(x_627, 1);
 x_630 = x_627;
} else {
 lean_dec_ref(x_627);
 x_630 = lean_box(0);
}
if (lean_is_scalar(x_630)) {
 x_631 = lean_alloc_ctor(0, 2, 0);
} else {
 x_631 = x_630;
}
lean_ctor_set(x_631, 0, x_628);
lean_ctor_set(x_631, 1, x_629);
return x_631;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; uint8_t x_635; lean_object* x_636; lean_object* x_637; uint8_t x_638; uint8_t x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_632 = lean_ctor_get(x_627, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_627, 1);
lean_inc(x_633);
lean_dec(x_627);
x_634 = lean_io_error_to_string(x_632);
x_635 = 3;
x_636 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_636, 0, x_634);
lean_ctor_set_uint8(x_636, sizeof(void*)*1, x_635);
x_637 = lean_box(1);
x_638 = 1;
x_639 = 0;
x_640 = l_Lake_OutStream_logEntry(x_637, x_636, x_638, x_639, x_633);
lean_dec(x_636);
x_641 = lean_ctor_get(x_640, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 x_642 = x_640;
} else {
 lean_dec_ref(x_640);
 x_642 = lean_box(0);
}
x_643 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_642)) {
 x_644 = lean_alloc_ctor(1, 2, 0);
} else {
 x_644 = x_642;
 lean_ctor_set_tag(x_644, 1);
}
lean_ctor_set(x_644, 0, x_643);
lean_ctor_set(x_644, 1, x_641);
return x_644;
}
}
}
else
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_618);
lean_dec(x_594);
lean_dec(x_529);
x_679 = lean_ctor_get(x_617, 1);
lean_inc(x_679);
lean_dec(x_617);
x_680 = l_Lake_mkModuleSetup___closed__2;
x_5 = x_680;
x_6 = x_679;
goto block_20;
}
}
else
{
lean_object* x_681; lean_object* x_682; 
lean_dec(x_594);
lean_dec(x_529);
x_681 = lean_ctor_get(x_613, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_613, 1);
lean_inc(x_682);
lean_dec(x_613);
x_5 = x_681;
x_6 = x_682;
goto block_20;
}
}
}
}
}
block_20:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_io_error_to_string(x_5);
x_8 = 3;
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = lean_box(1);
x_11 = 1;
x_12 = 0;
x_13 = l_Lake_OutStream_logEntry(x_10, x_9, x_11, x_12, x_6);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lake_setupFile___boxed__const__1;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___at_Lake_setupFile___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_withRegisterJob___at_Lake_setupFile___spec__1(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
x_24 = l_Lake_setupFile___closed__9;
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
x_46 = l_Lake_setupFile___closed__9;
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
x_74 = l_Lake_setupFile___closed__9;
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
x_90 = l_Lake_setupFile___closed__9;
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
x_120 = l_Lake_setupFile___closed__9;
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
x_144 = l_Lake_setupFile___closed__9;
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
x_173 = l_Lake_setupFile___closed__9;
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
x_206 = l_Lake_setupFile___closed__9;
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
x_231 = l_Lake_setupFile___closed__9;
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
x_261 = l_Lake_setupFile___closed__9;
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
l_Lake_mkModuleSetup___closed__1 = _init_l_Lake_mkModuleSetup___closed__1();
lean_mark_persistent(l_Lake_mkModuleSetup___closed__1);
l_Lake_mkModuleSetup___closed__2 = _init_l_Lake_mkModuleSetup___closed__2();
lean_mark_persistent(l_Lake_mkModuleSetup___closed__2);
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
