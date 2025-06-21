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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lake_Module_recFetchSetup_spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_Log_toString(lean_object*);
static lean_object* l_Lake_setupFile___closed__4;
lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanSrcPath(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Env_leanSrcPath(lean_object*);
lean_object* lean_module_name_of_file(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_baseVars(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkModuleSetup___lam__0(lean_object*);
static lean_object* l_Lake_mkModuleSetup___closed__0;
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT uint32_t l_Lake_noConfigFileCode;
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
static lean_object* l_Lake_setupFile___closed__3;
extern lean_object* l_Lake_Module_setupFacet;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ensureJob___at___Lake_Module_recFetchSetup_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__1;
lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(lean_object*, lean_object*);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_invalidConfigEnvVar;
LEAN_EXPORT uint8_t l_Lake_setupFile___lam__1(uint8_t, lean_object*);
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lake_BuildType_leanOptions(uint8_t);
uint8_t l_Lake_ordBuildType____x40_Lake_Config_LeanConfig___hyg_267_(uint8_t, uint8_t);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
static lean_object* l_Lake_mkModuleSetup___closed__1;
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__0;
lean_object* l_Lake_buildImportsAndDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___closed__0;
lean_object* l_IO_println___at___Lean_Environment_displayStats_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__1;
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
lean_object* l_Lean_parseImports_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkModuleSetup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkModuleSetup___lam__0___boxed(lean_object*);
static lean_object* l_Lake_serve___closed__2;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
static lean_object* l_Lake_invalidConfigEnvVar___closed__0;
lean_object* l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object*, lean_object*);
lean_object* l_Lake_Env_leanPath(lean_object*);
static lean_object* l_Lake_setupFile___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lake_realConfigFile(lean_object*, lean_object*);
static uint32_t _init_l_Lake_noConfigFileCode() {
_start:
{
uint32_t x_1; 
x_1 = 2;
return x_1;
}
}
static lean_object* _init_l_Lake_invalidConfigEnvVar___closed__0() {
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
x_1 = l_Lake_invalidConfigEnvVar___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_ctor_get(x_2, 4);
x_5 = l_Lake_Workspace_leanPath(x_1);
x_6 = l_Lake_Workspace_leanSrcPath(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
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
LEAN_EXPORT lean_object* l_Lake_mkModuleSetup___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_mkModuleSetup___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_mkModuleSetup___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_mkModuleSetup___closed__0;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_mkModuleSetup(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_2);
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
x_13 = l_Lake_Workspace_runFetchM___redArg(x_1, x_12, x_5, x_9);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_closure((void*)(l_Lake_mkModuleSetup___lam__0___boxed), 1, 0);
x_28 = lean_box(0);
x_29 = lean_array_size(x_21);
x_30 = 0;
lean_inc(x_27);
x_31 = l_Array_mapMUnsafe_map___at___Lake_Module_recFetchSetup_spec__4(x_27, x_29, x_30, x_21);
x_32 = lean_array_size(x_22);
x_33 = l_Array_mapMUnsafe_map___at___Lake_Module_recFetchSetup_spec__4(x_27, x_32, x_30, x_22);
x_34 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_31);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_4);
lean_ctor_set_uint8(x_34, sizeof(void*)*6, x_11);
lean_ctor_set(x_24, 0, x_34);
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
x_37 = lean_alloc_closure((void*)(l_Lake_mkModuleSetup___lam__0___boxed), 1, 0);
x_38 = lean_box(0);
x_39 = lean_array_size(x_21);
x_40 = 0;
lean_inc(x_37);
x_41 = l_Array_mapMUnsafe_map___at___Lake_Module_recFetchSetup_spec__4(x_37, x_39, x_40, x_21);
x_42 = lean_array_size(x_22);
x_43 = l_Array_mapMUnsafe_map___at___Lake_Module_recFetchSetup_spec__4(x_37, x_42, x_40, x_22);
x_44 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_10);
lean_ctor_set(x_44, 2, x_38);
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_4);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_11);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_24);
if (x_46 == 0)
{
return x_24;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_24, 0);
x_48 = lean_ctor_get(x_24, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_24);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_17, 0);
lean_dec(x_51);
x_52 = l_Lake_mkModuleSetup___closed__1;
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_52);
return x_17;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_dec(x_17);
x_54 = l_Lake_mkModuleSetup___closed__1;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_10);
lean_dec(x_4);
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
else
{
uint8_t x_60; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_7);
if (x_60 == 0)
{
return x_7;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_7, 0);
x_62 = lean_ctor_get(x_7, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_7);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkModuleSetup___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_mkModuleSetup___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_logToStream(x_4, x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_setupFile___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_7);
x_10 = l_Lake_ensureJob___at___Lake_Module_recFetchSetup_spec__7(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
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
x_18 = lean_ctor_get(x_7, 3);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_st_ref_take(x_18, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_ctor_set(x_12, 2, x_2);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_3);
lean_inc(x_12);
x_22 = l_Lake_Job_toOpaque___redArg(x_12);
x_23 = lean_array_push(x_20, x_22);
x_24 = lean_st_ref_set(x_18, x_23, x_21);
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = l_Lake_Job_renew___redArg(x_12);
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
x_29 = l_Lake_Job_renew___redArg(x_12);
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
x_33 = lean_ctor_get(x_7, 3);
lean_inc(x_33);
lean_dec(x_7);
x_34 = lean_st_ref_take(x_33, x_13);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_2);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_3);
lean_inc(x_37);
x_38 = l_Lake_Job_toOpaque___redArg(x_37);
x_39 = lean_array_push(x_35, x_38);
x_40 = lean_st_ref_set(x_33, x_39, x_36);
lean_dec(x_33);
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
x_43 = l_Lake_Job_renew___redArg(x_37);
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
x_49 = lean_ctor_get(x_7, 3);
lean_inc(x_49);
lean_dec(x_7);
x_50 = lean_st_ref_take(x_49, x_13);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(0, 3, 1);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_47);
lean_ctor_set(x_53, 2, x_2);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_3);
lean_inc(x_53);
x_54 = l_Lake_Job_toOpaque___redArg(x_53);
x_55 = lean_array_push(x_51, x_54);
x_56 = lean_st_ref_set(x_49, x_55, x_52);
lean_dec(x_49);
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
x_59 = l_Lake_Job_renew___redArg(x_53);
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
}
static lean_object* _init_l_Lake_setupFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":setup", 6, 6);
return x_1;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_setupFile___closed__1;
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_setupFile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to configure the Lake workspace. Please restart the server after fixing the error above.", 95, 95);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
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
x_1 = 2;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_24; uint8_t x_25; 
x_24 = l_Lake_resolvePath(x_2, x_4);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 6);
lean_inc(x_29);
x_30 = l_Lake_realConfigFile(x_29, x_27);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = lean_string_utf8_byte_size(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_eq(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
uint8_t x_37; 
lean_free_object(x_30);
x_37 = lean_string_dec_eq(x_32, x_26);
lean_dec(x_32);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_28);
lean_free_object(x_24);
x_38 = l_Lake_invalidConfigEnvVar___closed__0;
x_39 = lean_io_getenv(x_38, x_33);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(1);
x_43 = l_Lake_OutStream_get(x_42, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_47 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
lean_inc(x_44);
x_48 = l_Lake_AnsiMode_isEnabled(x_44, x_47, x_45);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_box(x_46);
x_52 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_52, 0, x_44);
lean_closure_set(x_52, 1, x_51);
lean_closure_set(x_52, 2, x_49);
x_53 = l_Lake_loadWorkspace(x_1, x_52, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_26);
x_56 = l_Lake_Workspace_findModuleBySrc_x3f(x_26, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = l_IO_FS_readFile(x_26, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 3);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 4);
lean_inc(x_64);
lean_dec(x_60);
x_65 = l_Lean_LeanOptions_ofArray(x_63);
lean_dec(x_63);
x_66 = l_Lean_LeanOptions_appendArray(x_65, x_64);
lean_dec(x_64);
lean_inc(x_54);
x_67 = l_Lake_mkModuleSetup(x_54, x_26, x_61, x_66, x_3, x_62);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
x_71 = lean_ctor_get(x_69, 5);
lean_inc(x_71);
x_72 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_54, x_69);
lean_dec(x_69);
lean_dec(x_54);
lean_ctor_set(x_67, 1, x_71);
lean_ctor_set(x_67, 0, x_72);
x_73 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_67);
x_74 = l_Lean_Json_compress(x_73);
x_75 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_74, x_70);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; 
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_dec(x_75);
x_82 = lean_io_error_to_string(x_80);
x_83 = lean_box(1);
x_84 = lean_box(0);
x_85 = lean_box(3);
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_82);
x_87 = lean_unbox(x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_87);
x_88 = lean_unbox(x_83);
x_89 = lean_unbox(x_84);
x_90 = l_Lake_OutStream_logEntry(x_42, x_86, x_88, x_89, x_81);
lean_dec(x_86);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
x_93 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = l_Lake_setupFile___boxed__const__1;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_67, 0);
x_98 = lean_ctor_get(x_67, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_67);
x_99 = lean_ctor_get(x_97, 5);
lean_inc(x_99);
x_100 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_54, x_97);
lean_dec(x_97);
lean_dec(x_54);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_101);
x_103 = l_Lean_Json_compress(x_102);
x_104 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_103, x_98);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_109 = lean_ctor_get(x_104, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
lean_dec(x_104);
x_111 = lean_io_error_to_string(x_109);
x_112 = lean_box(1);
x_113 = lean_box(0);
x_114 = lean_box(3);
x_115 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_115, 0, x_111);
x_116 = lean_unbox(x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_116);
x_117 = lean_unbox(x_112);
x_118 = lean_unbox(x_113);
x_119 = l_Lake_OutStream_logEntry(x_42, x_115, x_117, x_118, x_110);
lean_dec(x_115);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
x_122 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_121;
 lean_ctor_set_tag(x_123, 1);
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_54);
x_124 = lean_ctor_get(x_67, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_67, 1);
lean_inc(x_125);
lean_dec(x_67);
x_126 = lean_io_error_to_string(x_124);
x_127 = lean_box(1);
x_128 = lean_box(0);
x_129 = lean_box(3);
x_130 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_130, 0, x_126);
x_131 = lean_unbox(x_129);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_131);
x_132 = lean_unbox(x_127);
x_133 = lean_unbox(x_128);
x_134 = l_Lake_OutStream_logEntry(x_42, x_130, x_132, x_133, x_125);
lean_dec(x_130);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_134, 0);
lean_dec(x_136);
x_137 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 0, x_137);
return x_134;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
lean_dec(x_134);
x_139 = l_Lake_setupFile___boxed__const__1;
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; lean_object* x_151; uint8_t x_152; 
lean_dec(x_54);
lean_dec(x_26);
lean_dec(x_3);
x_141 = lean_ctor_get(x_57, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_57, 1);
lean_inc(x_142);
lean_dec(x_57);
x_143 = lean_io_error_to_string(x_141);
x_144 = lean_box(1);
x_145 = lean_box(0);
x_146 = lean_box(3);
x_147 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_147, 0, x_143);
x_148 = lean_unbox(x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_148);
x_149 = lean_unbox(x_144);
x_150 = lean_unbox(x_145);
x_151 = l_Lake_OutStream_logEntry(x_42, x_147, x_149, x_150, x_142);
lean_dec(x_147);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_151, 0);
lean_dec(x_153);
x_154 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_151, 1);
lean_ctor_set(x_151, 0, x_154);
return x_151;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
lean_dec(x_151);
x_156 = l_Lake_setupFile___boxed__const__1;
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_26);
x_158 = !lean_is_exclusive(x_56);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_159 = lean_ctor_get(x_56, 0);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 2);
lean_inc(x_162);
x_163 = lean_box(x_37);
x_164 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_164, 0, x_163);
x_165 = lean_box(1);
x_166 = lean_unbox(x_165);
x_167 = l_Lean_Name_toString(x_161, x_166, x_164);
x_168 = l_Lake_setupFile___closed__0;
x_169 = lean_string_append(x_167, x_168);
x_170 = l_Lake_Module_setupFacet;
lean_ctor_set_tag(x_56, 0);
lean_ctor_set(x_56, 0, x_162);
x_171 = l_Lake_Module_keyword;
x_172 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_172, 0, x_56);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_172, 2, x_159);
lean_ctor_set(x_172, 3, x_170);
x_173 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 7, 1);
lean_closure_set(x_173, 0, x_172);
x_174 = lean_box(x_37);
x_175 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 9, 3);
lean_closure_set(x_175, 0, x_173);
lean_closure_set(x_175, 1, x_169);
lean_closure_set(x_175, 2, x_174);
lean_inc(x_54);
x_176 = l_Lake_Workspace_runFetchM___redArg(x_54, x_175, x_3, x_55);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_io_wait(x_179, x_178);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_232; lean_object* x_233; 
x_182 = lean_ctor_get(x_160, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_182, 3);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_ctor_get(x_160, 2);
lean_inc(x_185);
lean_dec(x_160);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec(x_185);
x_187 = lean_ctor_get(x_180, 1);
lean_inc(x_187);
lean_dec(x_180);
x_188 = lean_ctor_get(x_181, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_189 = x_181;
} else {
 lean_dec_ref(x_181);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get_uint8(x_184, sizeof(void*)*13);
x_191 = lean_ctor_get(x_184, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_184, 4);
lean_inc(x_192);
lean_dec(x_184);
x_193 = lean_ctor_get_uint8(x_186, sizeof(void*)*13);
x_194 = lean_ctor_get(x_186, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_186, 4);
lean_inc(x_195);
lean_dec(x_186);
x_196 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_54, x_188);
lean_dec(x_188);
lean_dec(x_54);
x_197 = lean_box(0);
x_232 = l_Lake_ordBuildType____x40_Lake_Config_LeanConfig___hyg_267_(x_190, x_193);
x_233 = lean_box(x_232);
if (lean_obj_tag(x_233) == 2)
{
if (x_37 == 0)
{
x_198 = x_193;
goto block_231;
}
else
{
x_198 = x_190;
goto block_231;
}
}
else
{
lean_dec(x_233);
x_198 = x_190;
goto block_231;
}
block_231:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_199 = l_Lake_BuildType_leanOptions(x_198);
x_200 = l_Lean_LeanOptions_append(x_197, x_199);
x_201 = l_Lean_LeanOptions_ofArray(x_191);
lean_dec(x_191);
x_202 = l_Lean_LeanOptions_appendArray(x_201, x_192);
lean_dec(x_192);
x_203 = l_Lean_LeanOptions_append(x_200, x_202);
x_204 = l_Lean_LeanOptions_appendArray(x_203, x_194);
lean_dec(x_194);
x_205 = l_Lean_LeanOptions_appendArray(x_204, x_195);
lean_dec(x_195);
if (lean_is_scalar(x_189)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_189;
}
lean_ctor_set(x_206, 0, x_196);
lean_ctor_set(x_206, 1, x_205);
x_207 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_206);
x_208 = l_Lean_Json_compress(x_207);
x_209 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_208, x_187);
if (lean_obj_tag(x_209) == 0)
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
return x_209;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_209, 0);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_209);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; lean_object* x_224; uint8_t x_225; 
x_214 = lean_ctor_get(x_209, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_209, 1);
lean_inc(x_215);
lean_dec(x_209);
x_216 = lean_io_error_to_string(x_214);
x_217 = lean_box(1);
x_218 = lean_box(0);
x_219 = lean_box(3);
x_220 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_220, 0, x_216);
x_221 = lean_unbox(x_219);
lean_ctor_set_uint8(x_220, sizeof(void*)*1, x_221);
x_222 = lean_unbox(x_217);
x_223 = lean_unbox(x_218);
x_224 = l_Lake_OutStream_logEntry(x_42, x_220, x_222, x_223, x_215);
lean_dec(x_220);
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_224, 0);
lean_dec(x_226);
x_227 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_224, 1);
lean_ctor_set(x_224, 0, x_227);
return x_224;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
lean_dec(x_224);
x_229 = l_Lake_setupFile___boxed__const__1;
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
}
}
else
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_181);
lean_dec(x_160);
lean_dec(x_54);
x_234 = lean_ctor_get(x_180, 1);
lean_inc(x_234);
lean_dec(x_180);
x_235 = l_Lake_mkModuleSetup___closed__1;
x_5 = x_235;
x_6 = x_234;
goto block_23;
}
}
else
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_160);
lean_dec(x_54);
x_236 = lean_ctor_get(x_176, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_176, 1);
lean_inc(x_237);
lean_dec(x_176);
x_5 = x_236;
x_6 = x_237;
goto block_23;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_238 = lean_ctor_get(x_56, 0);
lean_inc(x_238);
lean_dec(x_56);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_238, 2);
lean_inc(x_241);
x_242 = lean_box(x_37);
x_243 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_243, 0, x_242);
x_244 = lean_box(1);
x_245 = lean_unbox(x_244);
x_246 = l_Lean_Name_toString(x_240, x_245, x_243);
x_247 = l_Lake_setupFile___closed__0;
x_248 = lean_string_append(x_246, x_247);
x_249 = l_Lake_Module_setupFacet;
x_250 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_250, 0, x_241);
x_251 = l_Lake_Module_keyword;
x_252 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
lean_ctor_set(x_252, 2, x_238);
lean_ctor_set(x_252, 3, x_249);
x_253 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 7, 1);
lean_closure_set(x_253, 0, x_252);
x_254 = lean_box(x_37);
x_255 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 9, 3);
lean_closure_set(x_255, 0, x_253);
lean_closure_set(x_255, 1, x_248);
lean_closure_set(x_255, 2, x_254);
lean_inc(x_54);
x_256 = l_Lake_Workspace_runFetchM___redArg(x_54, x_255, x_3, x_55);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_io_wait(x_259, x_258);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; uint8_t x_310; lean_object* x_311; 
x_262 = lean_ctor_get(x_239, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_262, 3);
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_265 = lean_ctor_get(x_239, 2);
lean_inc(x_265);
lean_dec(x_239);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec(x_265);
x_267 = lean_ctor_get(x_260, 1);
lean_inc(x_267);
lean_dec(x_260);
x_268 = lean_ctor_get(x_261, 0);
lean_inc(x_268);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_269 = x_261;
} else {
 lean_dec_ref(x_261);
 x_269 = lean_box(0);
}
x_270 = lean_ctor_get_uint8(x_264, sizeof(void*)*13);
x_271 = lean_ctor_get(x_264, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_264, 4);
lean_inc(x_272);
lean_dec(x_264);
x_273 = lean_ctor_get_uint8(x_266, sizeof(void*)*13);
x_274 = lean_ctor_get(x_266, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_266, 4);
lean_inc(x_275);
lean_dec(x_266);
x_276 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_54, x_268);
lean_dec(x_268);
lean_dec(x_54);
x_277 = lean_box(0);
x_310 = l_Lake_ordBuildType____x40_Lake_Config_LeanConfig___hyg_267_(x_270, x_273);
x_311 = lean_box(x_310);
if (lean_obj_tag(x_311) == 2)
{
if (x_37 == 0)
{
x_278 = x_273;
goto block_309;
}
else
{
x_278 = x_270;
goto block_309;
}
}
else
{
lean_dec(x_311);
x_278 = x_270;
goto block_309;
}
block_309:
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_279 = l_Lake_BuildType_leanOptions(x_278);
x_280 = l_Lean_LeanOptions_append(x_277, x_279);
x_281 = l_Lean_LeanOptions_ofArray(x_271);
lean_dec(x_271);
x_282 = l_Lean_LeanOptions_appendArray(x_281, x_272);
lean_dec(x_272);
x_283 = l_Lean_LeanOptions_append(x_280, x_282);
x_284 = l_Lean_LeanOptions_appendArray(x_283, x_274);
lean_dec(x_274);
x_285 = l_Lean_LeanOptions_appendArray(x_284, x_275);
lean_dec(x_275);
if (lean_is_scalar(x_269)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_269;
}
lean_ctor_set(x_286, 0, x_276);
lean_ctor_set(x_286, 1, x_285);
x_287 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_286);
x_288 = l_Lean_Json_compress(x_287);
x_289 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_288, x_267);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_292 = x_289;
} else {
 lean_dec_ref(x_289);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; uint8_t x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_294 = lean_ctor_get(x_289, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_289, 1);
lean_inc(x_295);
lean_dec(x_289);
x_296 = lean_io_error_to_string(x_294);
x_297 = lean_box(1);
x_298 = lean_box(0);
x_299 = lean_box(3);
x_300 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_300, 0, x_296);
x_301 = lean_unbox(x_299);
lean_ctor_set_uint8(x_300, sizeof(void*)*1, x_301);
x_302 = lean_unbox(x_297);
x_303 = lean_unbox(x_298);
x_304 = l_Lake_OutStream_logEntry(x_42, x_300, x_302, x_303, x_295);
lean_dec(x_300);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_306 = x_304;
} else {
 lean_dec_ref(x_304);
 x_306 = lean_box(0);
}
x_307 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_306)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_306;
 lean_ctor_set_tag(x_308, 1);
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_305);
return x_308;
}
}
}
else
{
lean_object* x_312; lean_object* x_313; 
lean_dec(x_261);
lean_dec(x_239);
lean_dec(x_54);
x_312 = lean_ctor_get(x_260, 1);
lean_inc(x_312);
lean_dec(x_260);
x_313 = l_Lake_mkModuleSetup___closed__1;
x_5 = x_313;
x_6 = x_312;
goto block_23;
}
}
else
{
lean_object* x_314; lean_object* x_315; 
lean_dec(x_239);
lean_dec(x_54);
x_314 = lean_ctor_get(x_256, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_256, 1);
lean_inc(x_315);
lean_dec(x_256);
x_5 = x_314;
x_6 = x_315;
goto block_23;
}
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; uint8_t x_321; lean_object* x_322; uint8_t x_323; 
lean_dec(x_26);
lean_dec(x_3);
x_316 = lean_ctor_get(x_53, 1);
lean_inc(x_316);
lean_dec(x_53);
x_317 = lean_box(1);
x_318 = lean_box(0);
x_319 = l_Lake_setupFile___closed__2;
x_320 = lean_unbox(x_317);
x_321 = lean_unbox(x_318);
x_322 = l_Lake_OutStream_logEntry(x_42, x_319, x_320, x_321, x_316);
x_323 = !lean_is_exclusive(x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; 
x_324 = lean_ctor_get(x_322, 0);
lean_dec(x_324);
x_325 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_322, 1);
lean_ctor_set(x_322, 0, x_325);
return x_322;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_322, 1);
lean_inc(x_326);
lean_dec(x_322);
x_327 = l_Lake_setupFile___boxed__const__1;
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_329 = lean_ctor_get(x_39, 1);
lean_inc(x_329);
lean_dec(x_39);
x_330 = lean_ctor_get(x_40, 0);
lean_inc(x_330);
lean_dec(x_40);
x_331 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_330, x_329);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
lean_dec(x_331);
x_333 = l_Lake_setupFile___closed__3;
x_334 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_333, x_332);
if (lean_obj_tag(x_334) == 0)
{
uint8_t x_335; 
x_335 = !lean_is_exclusive(x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_334, 0);
lean_dec(x_336);
x_337 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_334, 1);
lean_ctor_set(x_334, 0, x_337);
return x_334;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_334, 1);
lean_inc(x_338);
lean_dec(x_334);
x_339 = l_Lake_setupFile___boxed__const__1;
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_338);
return x_340;
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_350; uint8_t x_351; lean_object* x_352; uint8_t x_353; 
x_341 = lean_ctor_get(x_334, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_334, 1);
lean_inc(x_342);
lean_dec(x_334);
x_343 = lean_io_error_to_string(x_341);
x_344 = lean_box(1);
x_345 = lean_box(0);
x_346 = lean_box(1);
x_347 = lean_box(3);
x_348 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_348, 0, x_343);
x_349 = lean_unbox(x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*1, x_349);
x_350 = lean_unbox(x_344);
x_351 = lean_unbox(x_345);
x_352 = l_Lake_OutStream_logEntry(x_346, x_348, x_350, x_351, x_342);
lean_dec(x_348);
x_353 = !lean_is_exclusive(x_352);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_352, 0);
lean_dec(x_354);
x_355 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_352, 1);
lean_ctor_set(x_352, 0, x_355);
return x_352;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
lean_dec(x_352);
x_357 = l_Lake_setupFile___boxed__const__1;
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_356);
return x_358;
}
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; uint8_t x_368; uint8_t x_369; lean_object* x_370; uint8_t x_371; 
x_359 = lean_ctor_get(x_331, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_331, 1);
lean_inc(x_360);
lean_dec(x_331);
x_361 = lean_io_error_to_string(x_359);
x_362 = lean_box(1);
x_363 = lean_box(0);
x_364 = lean_box(1);
x_365 = lean_box(3);
x_366 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_366, 0, x_361);
x_367 = lean_unbox(x_365);
lean_ctor_set_uint8(x_366, sizeof(void*)*1, x_367);
x_368 = lean_unbox(x_362);
x_369 = lean_unbox(x_363);
x_370 = l_Lake_OutStream_logEntry(x_364, x_366, x_368, x_369, x_360);
lean_dec(x_366);
x_371 = !lean_is_exclusive(x_370);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_370, 0);
lean_dec(x_372);
x_373 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_370, 1);
lean_ctor_set(x_370, 0, x_373);
return x_370;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_370, 1);
lean_inc(x_374);
lean_dec(x_370);
x_375 = l_Lake_setupFile___boxed__const__1;
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_374);
return x_376;
}
}
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_377 = lean_ctor_get(x_28, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_377, 4);
lean_inc(x_378);
lean_dec(x_377);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
lean_dec(x_378);
x_380 = l_Lake_Env_leanPath(x_28);
x_381 = l_Lake_Env_leanSrcPath(x_28);
lean_dec(x_28);
x_382 = l_Lake_setupFile___closed__4;
x_383 = l_Lake_setupFile___closed__5;
x_384 = lean_array_push(x_383, x_379);
x_385 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_385, 0, x_380);
lean_ctor_set(x_385, 1, x_381);
lean_ctor_set(x_385, 2, x_382);
lean_ctor_set(x_385, 3, x_384);
x_386 = lean_box(0);
lean_ctor_set(x_24, 1, x_386);
lean_ctor_set(x_24, 0, x_385);
x_387 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_24);
x_388 = l_Lean_Json_compress(x_387);
x_389 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_388, x_33);
if (lean_obj_tag(x_389) == 0)
{
uint8_t x_390; 
x_390 = !lean_is_exclusive(x_389);
if (x_390 == 0)
{
return x_389;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_389, 0);
x_392 = lean_ctor_get(x_389, 1);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_389);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; uint8_t x_403; uint8_t x_404; lean_object* x_405; uint8_t x_406; 
x_394 = lean_ctor_get(x_389, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_389, 1);
lean_inc(x_395);
lean_dec(x_389);
x_396 = lean_io_error_to_string(x_394);
x_397 = lean_box(1);
x_398 = lean_box(0);
x_399 = lean_box(1);
x_400 = lean_box(3);
x_401 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_401, 0, x_396);
x_402 = lean_unbox(x_400);
lean_ctor_set_uint8(x_401, sizeof(void*)*1, x_402);
x_403 = lean_unbox(x_397);
x_404 = lean_unbox(x_398);
x_405 = l_Lake_OutStream_logEntry(x_399, x_401, x_403, x_404, x_395);
lean_dec(x_401);
x_406 = !lean_is_exclusive(x_405);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_ctor_get(x_405, 0);
lean_dec(x_407);
x_408 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_405, 1);
lean_ctor_set(x_405, 0, x_408);
return x_405;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_405, 1);
lean_inc(x_409);
lean_dec(x_405);
x_410 = l_Lake_setupFile___boxed__const__1;
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_409);
return x_411;
}
}
}
}
else
{
lean_object* x_412; 
lean_dec(x_32);
lean_dec(x_28);
lean_free_object(x_24);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_412 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 0, x_412);
return x_30;
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
x_413 = lean_ctor_get(x_30, 0);
x_414 = lean_ctor_get(x_30, 1);
lean_inc(x_414);
lean_inc(x_413);
lean_dec(x_30);
x_415 = lean_string_utf8_byte_size(x_413);
x_416 = lean_unsigned_to_nat(0u);
x_417 = lean_nat_dec_eq(x_415, x_416);
lean_dec(x_415);
if (x_417 == 0)
{
uint8_t x_418; 
x_418 = lean_string_dec_eq(x_413, x_26);
lean_dec(x_413);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_28);
lean_free_object(x_24);
x_419 = l_Lake_invalidConfigEnvVar___closed__0;
x_420 = lean_io_getenv(x_419, x_414);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; uint8_t x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_box(1);
x_424 = l_Lake_OutStream_get(x_423, x_422);
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_427 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_428 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
lean_inc(x_425);
x_429 = l_Lake_AnsiMode_isEnabled(x_425, x_428, x_426);
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
lean_dec(x_429);
x_432 = lean_box(x_427);
x_433 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_433, 0, x_425);
lean_closure_set(x_433, 1, x_432);
lean_closure_set(x_433, 2, x_430);
x_434 = l_Lake_loadWorkspace(x_1, x_433, x_431);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
lean_inc(x_26);
x_437 = l_Lake_Workspace_findModuleBySrc_x3f(x_26, x_435);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; 
x_438 = l_IO_FS_readFile(x_26, x_436);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_439 = lean_ctor_get(x_435, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_439, 3);
lean_inc(x_440);
lean_dec(x_439);
x_441 = lean_ctor_get(x_440, 1);
lean_inc(x_441);
lean_dec(x_440);
x_442 = lean_ctor_get(x_438, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_438, 1);
lean_inc(x_443);
lean_dec(x_438);
x_444 = lean_ctor_get(x_441, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_441, 4);
lean_inc(x_445);
lean_dec(x_441);
x_446 = l_Lean_LeanOptions_ofArray(x_444);
lean_dec(x_444);
x_447 = l_Lean_LeanOptions_appendArray(x_446, x_445);
lean_dec(x_445);
lean_inc(x_435);
x_448 = l_Lake_mkModuleSetup(x_435, x_26, x_442, x_447, x_3, x_443);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_451 = x_448;
} else {
 lean_dec_ref(x_448);
 x_451 = lean_box(0);
}
x_452 = lean_ctor_get(x_449, 5);
lean_inc(x_452);
x_453 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_435, x_449);
lean_dec(x_449);
lean_dec(x_435);
if (lean_is_scalar(x_451)) {
 x_454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_454 = x_451;
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_452);
x_455 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_454);
x_456 = l_Lean_Json_compress(x_455);
x_457 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_456, x_450);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_460 = x_457;
} else {
 lean_dec_ref(x_457);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(0, 2, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_458);
lean_ctor_set(x_461, 1, x_459);
return x_461;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; uint8_t x_470; uint8_t x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_462 = lean_ctor_get(x_457, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_457, 1);
lean_inc(x_463);
lean_dec(x_457);
x_464 = lean_io_error_to_string(x_462);
x_465 = lean_box(1);
x_466 = lean_box(0);
x_467 = lean_box(3);
x_468 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_468, 0, x_464);
x_469 = lean_unbox(x_467);
lean_ctor_set_uint8(x_468, sizeof(void*)*1, x_469);
x_470 = lean_unbox(x_465);
x_471 = lean_unbox(x_466);
x_472 = l_Lake_OutStream_logEntry(x_423, x_468, x_470, x_471, x_463);
lean_dec(x_468);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_474 = x_472;
} else {
 lean_dec_ref(x_472);
 x_474 = lean_box(0);
}
x_475 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_474)) {
 x_476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_476 = x_474;
 lean_ctor_set_tag(x_476, 1);
}
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_473);
return x_476;
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; uint8_t x_485; uint8_t x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
lean_dec(x_435);
x_477 = lean_ctor_get(x_448, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_448, 1);
lean_inc(x_478);
lean_dec(x_448);
x_479 = lean_io_error_to_string(x_477);
x_480 = lean_box(1);
x_481 = lean_box(0);
x_482 = lean_box(3);
x_483 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_483, 0, x_479);
x_484 = lean_unbox(x_482);
lean_ctor_set_uint8(x_483, sizeof(void*)*1, x_484);
x_485 = lean_unbox(x_480);
x_486 = lean_unbox(x_481);
x_487 = l_Lake_OutStream_logEntry(x_423, x_483, x_485, x_486, x_478);
lean_dec(x_483);
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_489 = x_487;
} else {
 lean_dec_ref(x_487);
 x_489 = lean_box(0);
}
x_490 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 2, 0);
} else {
 x_491 = x_489;
 lean_ctor_set_tag(x_491, 1);
}
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_488);
return x_491;
}
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; uint8_t x_500; uint8_t x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_435);
lean_dec(x_26);
lean_dec(x_3);
x_492 = lean_ctor_get(x_438, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_438, 1);
lean_inc(x_493);
lean_dec(x_438);
x_494 = lean_io_error_to_string(x_492);
x_495 = lean_box(1);
x_496 = lean_box(0);
x_497 = lean_box(3);
x_498 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_498, 0, x_494);
x_499 = lean_unbox(x_497);
lean_ctor_set_uint8(x_498, sizeof(void*)*1, x_499);
x_500 = lean_unbox(x_495);
x_501 = lean_unbox(x_496);
x_502 = l_Lake_OutStream_logEntry(x_423, x_498, x_500, x_501, x_493);
lean_dec(x_498);
x_503 = lean_ctor_get(x_502, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_504 = x_502;
} else {
 lean_dec_ref(x_502);
 x_504 = lean_box(0);
}
x_505 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_504)) {
 x_506 = lean_alloc_ctor(1, 2, 0);
} else {
 x_506 = x_504;
 lean_ctor_set_tag(x_506, 1);
}
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_503);
return x_506;
}
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
lean_dec(x_26);
x_507 = lean_ctor_get(x_437, 0);
lean_inc(x_507);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 x_508 = x_437;
} else {
 lean_dec_ref(x_437);
 x_508 = lean_box(0);
}
x_509 = lean_ctor_get(x_507, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_507, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_507, 2);
lean_inc(x_511);
x_512 = lean_box(x_418);
x_513 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_513, 0, x_512);
x_514 = lean_box(1);
x_515 = lean_unbox(x_514);
x_516 = l_Lean_Name_toString(x_510, x_515, x_513);
x_517 = l_Lake_setupFile___closed__0;
x_518 = lean_string_append(x_516, x_517);
x_519 = l_Lake_Module_setupFacet;
if (lean_is_scalar(x_508)) {
 x_520 = lean_alloc_ctor(0, 1, 0);
} else {
 x_520 = x_508;
 lean_ctor_set_tag(x_520, 0);
}
lean_ctor_set(x_520, 0, x_511);
x_521 = l_Lake_Module_keyword;
x_522 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_522, 0, x_520);
lean_ctor_set(x_522, 1, x_521);
lean_ctor_set(x_522, 2, x_507);
lean_ctor_set(x_522, 3, x_519);
x_523 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 7, 1);
lean_closure_set(x_523, 0, x_522);
x_524 = lean_box(x_418);
x_525 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 9, 3);
lean_closure_set(x_525, 0, x_523);
lean_closure_set(x_525, 1, x_518);
lean_closure_set(x_525, 2, x_524);
lean_inc(x_435);
x_526 = l_Lake_Workspace_runFetchM___redArg(x_435, x_525, x_3, x_436);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
lean_dec(x_526);
x_529 = lean_ctor_get(x_527, 0);
lean_inc(x_529);
lean_dec(x_527);
x_530 = lean_io_wait(x_529, x_528);
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; uint8_t x_580; lean_object* x_581; 
x_532 = lean_ctor_get(x_509, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_532, 3);
lean_inc(x_533);
lean_dec(x_532);
x_534 = lean_ctor_get(x_533, 1);
lean_inc(x_534);
lean_dec(x_533);
x_535 = lean_ctor_get(x_509, 2);
lean_inc(x_535);
lean_dec(x_509);
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
lean_dec(x_535);
x_537 = lean_ctor_get(x_530, 1);
lean_inc(x_537);
lean_dec(x_530);
x_538 = lean_ctor_get(x_531, 0);
lean_inc(x_538);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_539 = x_531;
} else {
 lean_dec_ref(x_531);
 x_539 = lean_box(0);
}
x_540 = lean_ctor_get_uint8(x_534, sizeof(void*)*13);
x_541 = lean_ctor_get(x_534, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_534, 4);
lean_inc(x_542);
lean_dec(x_534);
x_543 = lean_ctor_get_uint8(x_536, sizeof(void*)*13);
x_544 = lean_ctor_get(x_536, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_536, 4);
lean_inc(x_545);
lean_dec(x_536);
x_546 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_435, x_538);
lean_dec(x_538);
lean_dec(x_435);
x_547 = lean_box(0);
x_580 = l_Lake_ordBuildType____x40_Lake_Config_LeanConfig___hyg_267_(x_540, x_543);
x_581 = lean_box(x_580);
if (lean_obj_tag(x_581) == 2)
{
if (x_418 == 0)
{
x_548 = x_543;
goto block_579;
}
else
{
x_548 = x_540;
goto block_579;
}
}
else
{
lean_dec(x_581);
x_548 = x_540;
goto block_579;
}
block_579:
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_549 = l_Lake_BuildType_leanOptions(x_548);
x_550 = l_Lean_LeanOptions_append(x_547, x_549);
x_551 = l_Lean_LeanOptions_ofArray(x_541);
lean_dec(x_541);
x_552 = l_Lean_LeanOptions_appendArray(x_551, x_542);
lean_dec(x_542);
x_553 = l_Lean_LeanOptions_append(x_550, x_552);
x_554 = l_Lean_LeanOptions_appendArray(x_553, x_544);
lean_dec(x_544);
x_555 = l_Lean_LeanOptions_appendArray(x_554, x_545);
lean_dec(x_545);
if (lean_is_scalar(x_539)) {
 x_556 = lean_alloc_ctor(0, 2, 0);
} else {
 x_556 = x_539;
}
lean_ctor_set(x_556, 0, x_546);
lean_ctor_set(x_556, 1, x_555);
x_557 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_556);
x_558 = l_Lean_Json_compress(x_557);
x_559 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_558, x_537);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_562 = x_559;
} else {
 lean_dec_ref(x_559);
 x_562 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_562;
}
lean_ctor_set(x_563, 0, x_560);
lean_ctor_set(x_563, 1, x_561);
return x_563;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; uint8_t x_571; uint8_t x_572; uint8_t x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_564 = lean_ctor_get(x_559, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_559, 1);
lean_inc(x_565);
lean_dec(x_559);
x_566 = lean_io_error_to_string(x_564);
x_567 = lean_box(1);
x_568 = lean_box(0);
x_569 = lean_box(3);
x_570 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_570, 0, x_566);
x_571 = lean_unbox(x_569);
lean_ctor_set_uint8(x_570, sizeof(void*)*1, x_571);
x_572 = lean_unbox(x_567);
x_573 = lean_unbox(x_568);
x_574 = l_Lake_OutStream_logEntry(x_423, x_570, x_572, x_573, x_565);
lean_dec(x_570);
x_575 = lean_ctor_get(x_574, 1);
lean_inc(x_575);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_576 = x_574;
} else {
 lean_dec_ref(x_574);
 x_576 = lean_box(0);
}
x_577 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_576)) {
 x_578 = lean_alloc_ctor(1, 2, 0);
} else {
 x_578 = x_576;
 lean_ctor_set_tag(x_578, 1);
}
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_575);
return x_578;
}
}
}
else
{
lean_object* x_582; lean_object* x_583; 
lean_dec(x_531);
lean_dec(x_509);
lean_dec(x_435);
x_582 = lean_ctor_get(x_530, 1);
lean_inc(x_582);
lean_dec(x_530);
x_583 = l_Lake_mkModuleSetup___closed__1;
x_5 = x_583;
x_6 = x_582;
goto block_23;
}
}
else
{
lean_object* x_584; lean_object* x_585; 
lean_dec(x_509);
lean_dec(x_435);
x_584 = lean_ctor_get(x_526, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_526, 1);
lean_inc(x_585);
lean_dec(x_526);
x_5 = x_584;
x_6 = x_585;
goto block_23;
}
}
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; uint8_t x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_26);
lean_dec(x_3);
x_586 = lean_ctor_get(x_434, 1);
lean_inc(x_586);
lean_dec(x_434);
x_587 = lean_box(1);
x_588 = lean_box(0);
x_589 = l_Lake_setupFile___closed__2;
x_590 = lean_unbox(x_587);
x_591 = lean_unbox(x_588);
x_592 = l_Lake_OutStream_logEntry(x_423, x_589, x_590, x_591, x_586);
x_593 = lean_ctor_get(x_592, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 x_594 = x_592;
} else {
 lean_dec_ref(x_592);
 x_594 = lean_box(0);
}
x_595 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_594)) {
 x_596 = lean_alloc_ctor(1, 2, 0);
} else {
 x_596 = x_594;
 lean_ctor_set_tag(x_596, 1);
}
lean_ctor_set(x_596, 0, x_595);
lean_ctor_set(x_596, 1, x_593);
return x_596;
}
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_597 = lean_ctor_get(x_420, 1);
lean_inc(x_597);
lean_dec(x_420);
x_598 = lean_ctor_get(x_421, 0);
lean_inc(x_598);
lean_dec(x_421);
x_599 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_598, x_597);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_599, 1);
lean_inc(x_600);
lean_dec(x_599);
x_601 = l_Lake_setupFile___closed__3;
x_602 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_601, x_600);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_603 = lean_ctor_get(x_602, 1);
lean_inc(x_603);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_604 = x_602;
} else {
 lean_dec_ref(x_602);
 x_604 = lean_box(0);
}
x_605 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_604)) {
 x_606 = lean_alloc_ctor(1, 2, 0);
} else {
 x_606 = x_604;
 lean_ctor_set_tag(x_606, 1);
}
lean_ctor_set(x_606, 0, x_605);
lean_ctor_set(x_606, 1, x_603);
return x_606;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; uint8_t x_616; uint8_t x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_607 = lean_ctor_get(x_602, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_602, 1);
lean_inc(x_608);
lean_dec(x_602);
x_609 = lean_io_error_to_string(x_607);
x_610 = lean_box(1);
x_611 = lean_box(0);
x_612 = lean_box(1);
x_613 = lean_box(3);
x_614 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_614, 0, x_609);
x_615 = lean_unbox(x_613);
lean_ctor_set_uint8(x_614, sizeof(void*)*1, x_615);
x_616 = lean_unbox(x_610);
x_617 = lean_unbox(x_611);
x_618 = l_Lake_OutStream_logEntry(x_612, x_614, x_616, x_617, x_608);
lean_dec(x_614);
x_619 = lean_ctor_get(x_618, 1);
lean_inc(x_619);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 lean_ctor_release(x_618, 1);
 x_620 = x_618;
} else {
 lean_dec_ref(x_618);
 x_620 = lean_box(0);
}
x_621 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_620)) {
 x_622 = lean_alloc_ctor(1, 2, 0);
} else {
 x_622 = x_620;
 lean_ctor_set_tag(x_622, 1);
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_619);
return x_622;
}
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; uint8_t x_632; uint8_t x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_623 = lean_ctor_get(x_599, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_599, 1);
lean_inc(x_624);
lean_dec(x_599);
x_625 = lean_io_error_to_string(x_623);
x_626 = lean_box(1);
x_627 = lean_box(0);
x_628 = lean_box(1);
x_629 = lean_box(3);
x_630 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_630, 0, x_625);
x_631 = lean_unbox(x_629);
lean_ctor_set_uint8(x_630, sizeof(void*)*1, x_631);
x_632 = lean_unbox(x_626);
x_633 = lean_unbox(x_627);
x_634 = l_Lake_OutStream_logEntry(x_628, x_630, x_632, x_633, x_624);
lean_dec(x_630);
x_635 = lean_ctor_get(x_634, 1);
lean_inc(x_635);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_636 = x_634;
} else {
 lean_dec_ref(x_634);
 x_636 = lean_box(0);
}
x_637 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_636)) {
 x_638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_638 = x_636;
 lean_ctor_set_tag(x_638, 1);
}
lean_ctor_set(x_638, 0, x_637);
lean_ctor_set(x_638, 1, x_635);
return x_638;
}
}
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_639 = lean_ctor_get(x_28, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_639, 4);
lean_inc(x_640);
lean_dec(x_639);
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
lean_dec(x_640);
x_642 = l_Lake_Env_leanPath(x_28);
x_643 = l_Lake_Env_leanSrcPath(x_28);
lean_dec(x_28);
x_644 = l_Lake_setupFile___closed__4;
x_645 = l_Lake_setupFile___closed__5;
x_646 = lean_array_push(x_645, x_641);
x_647 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_647, 0, x_642);
lean_ctor_set(x_647, 1, x_643);
lean_ctor_set(x_647, 2, x_644);
lean_ctor_set(x_647, 3, x_646);
x_648 = lean_box(0);
lean_ctor_set(x_24, 1, x_648);
lean_ctor_set(x_24, 0, x_647);
x_649 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_24);
x_650 = l_Lean_Json_compress(x_649);
x_651 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_650, x_414);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
if (lean_is_exclusive(x_651)) {
 lean_ctor_release(x_651, 0);
 lean_ctor_release(x_651, 1);
 x_654 = x_651;
} else {
 lean_dec_ref(x_651);
 x_654 = lean_box(0);
}
if (lean_is_scalar(x_654)) {
 x_655 = lean_alloc_ctor(0, 2, 0);
} else {
 x_655 = x_654;
}
lean_ctor_set(x_655, 0, x_652);
lean_ctor_set(x_655, 1, x_653);
return x_655;
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; uint8_t x_664; uint8_t x_665; uint8_t x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_656 = lean_ctor_get(x_651, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_651, 1);
lean_inc(x_657);
lean_dec(x_651);
x_658 = lean_io_error_to_string(x_656);
x_659 = lean_box(1);
x_660 = lean_box(0);
x_661 = lean_box(1);
x_662 = lean_box(3);
x_663 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_663, 0, x_658);
x_664 = lean_unbox(x_662);
lean_ctor_set_uint8(x_663, sizeof(void*)*1, x_664);
x_665 = lean_unbox(x_659);
x_666 = lean_unbox(x_660);
x_667 = l_Lake_OutStream_logEntry(x_661, x_663, x_665, x_666, x_657);
lean_dec(x_663);
x_668 = lean_ctor_get(x_667, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 x_669 = x_667;
} else {
 lean_dec_ref(x_667);
 x_669 = lean_box(0);
}
x_670 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_669)) {
 x_671 = lean_alloc_ctor(1, 2, 0);
} else {
 x_671 = x_669;
 lean_ctor_set_tag(x_671, 1);
}
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_668);
return x_671;
}
}
}
else
{
lean_object* x_672; lean_object* x_673; 
lean_dec(x_413);
lean_dec(x_28);
lean_free_object(x_24);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_672 = l_Lake_setupFile___boxed__const__2;
x_673 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_673, 0, x_672);
lean_ctor_set(x_673, 1, x_414);
return x_673;
}
}
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; 
x_674 = lean_ctor_get(x_24, 0);
x_675 = lean_ctor_get(x_24, 1);
lean_inc(x_675);
lean_inc(x_674);
lean_dec(x_24);
x_676 = lean_ctor_get(x_1, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_1, 6);
lean_inc(x_677);
x_678 = l_Lake_realConfigFile(x_677, x_675);
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_678, 1);
lean_inc(x_680);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_681 = x_678;
} else {
 lean_dec_ref(x_678);
 x_681 = lean_box(0);
}
x_682 = lean_string_utf8_byte_size(x_679);
x_683 = lean_unsigned_to_nat(0u);
x_684 = lean_nat_dec_eq(x_682, x_683);
lean_dec(x_682);
if (x_684 == 0)
{
uint8_t x_685; 
lean_dec(x_681);
x_685 = lean_string_dec_eq(x_679, x_674);
lean_dec(x_679);
if (x_685 == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
lean_dec(x_676);
x_686 = l_Lake_invalidConfigEnvVar___closed__0;
x_687 = lean_io_getenv(x_686, x_680);
x_688 = lean_ctor_get(x_687, 0);
lean_inc(x_688);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; uint8_t x_694; uint8_t x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
x_689 = lean_ctor_get(x_687, 1);
lean_inc(x_689);
lean_dec(x_687);
x_690 = lean_box(1);
x_691 = l_Lake_OutStream_get(x_690, x_689);
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_691, 1);
lean_inc(x_693);
lean_dec(x_691);
x_694 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_695 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
lean_inc(x_692);
x_696 = l_Lake_AnsiMode_isEnabled(x_692, x_695, x_693);
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
lean_dec(x_696);
x_699 = lean_box(x_694);
x_700 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_700, 0, x_692);
lean_closure_set(x_700, 1, x_699);
lean_closure_set(x_700, 2, x_697);
x_701 = l_Lake_loadWorkspace(x_1, x_700, x_698);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
lean_dec(x_701);
lean_inc(x_674);
x_704 = l_Lake_Workspace_findModuleBySrc_x3f(x_674, x_702);
if (lean_obj_tag(x_704) == 0)
{
lean_object* x_705; 
x_705 = l_IO_FS_readFile(x_674, x_703);
if (lean_obj_tag(x_705) == 0)
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_706 = lean_ctor_get(x_702, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_706, 3);
lean_inc(x_707);
lean_dec(x_706);
x_708 = lean_ctor_get(x_707, 1);
lean_inc(x_708);
lean_dec(x_707);
x_709 = lean_ctor_get(x_705, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_705, 1);
lean_inc(x_710);
lean_dec(x_705);
x_711 = lean_ctor_get(x_708, 0);
lean_inc(x_711);
x_712 = lean_ctor_get(x_708, 4);
lean_inc(x_712);
lean_dec(x_708);
x_713 = l_Lean_LeanOptions_ofArray(x_711);
lean_dec(x_711);
x_714 = l_Lean_LeanOptions_appendArray(x_713, x_712);
lean_dec(x_712);
lean_inc(x_702);
x_715 = l_Lake_mkModuleSetup(x_702, x_674, x_709, x_714, x_3, x_710);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_718 = x_715;
} else {
 lean_dec_ref(x_715);
 x_718 = lean_box(0);
}
x_719 = lean_ctor_get(x_716, 5);
lean_inc(x_719);
x_720 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_702, x_716);
lean_dec(x_716);
lean_dec(x_702);
if (lean_is_scalar(x_718)) {
 x_721 = lean_alloc_ctor(0, 2, 0);
} else {
 x_721 = x_718;
}
lean_ctor_set(x_721, 0, x_720);
lean_ctor_set(x_721, 1, x_719);
x_722 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_721);
x_723 = l_Lean_Json_compress(x_722);
x_724 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_723, x_717);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
if (lean_is_exclusive(x_724)) {
 lean_ctor_release(x_724, 0);
 lean_ctor_release(x_724, 1);
 x_727 = x_724;
} else {
 lean_dec_ref(x_724);
 x_727 = lean_box(0);
}
if (lean_is_scalar(x_727)) {
 x_728 = lean_alloc_ctor(0, 2, 0);
} else {
 x_728 = x_727;
}
lean_ctor_set(x_728, 0, x_725);
lean_ctor_set(x_728, 1, x_726);
return x_728;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; uint8_t x_736; uint8_t x_737; uint8_t x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_729 = lean_ctor_get(x_724, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_724, 1);
lean_inc(x_730);
lean_dec(x_724);
x_731 = lean_io_error_to_string(x_729);
x_732 = lean_box(1);
x_733 = lean_box(0);
x_734 = lean_box(3);
x_735 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_735, 0, x_731);
x_736 = lean_unbox(x_734);
lean_ctor_set_uint8(x_735, sizeof(void*)*1, x_736);
x_737 = lean_unbox(x_732);
x_738 = lean_unbox(x_733);
x_739 = l_Lake_OutStream_logEntry(x_690, x_735, x_737, x_738, x_730);
lean_dec(x_735);
x_740 = lean_ctor_get(x_739, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_739)) {
 lean_ctor_release(x_739, 0);
 lean_ctor_release(x_739, 1);
 x_741 = x_739;
} else {
 lean_dec_ref(x_739);
 x_741 = lean_box(0);
}
x_742 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_741)) {
 x_743 = lean_alloc_ctor(1, 2, 0);
} else {
 x_743 = x_741;
 lean_ctor_set_tag(x_743, 1);
}
lean_ctor_set(x_743, 0, x_742);
lean_ctor_set(x_743, 1, x_740);
return x_743;
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; uint8_t x_752; uint8_t x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_702);
x_744 = lean_ctor_get(x_715, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_715, 1);
lean_inc(x_745);
lean_dec(x_715);
x_746 = lean_io_error_to_string(x_744);
x_747 = lean_box(1);
x_748 = lean_box(0);
x_749 = lean_box(3);
x_750 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_750, 0, x_746);
x_751 = lean_unbox(x_749);
lean_ctor_set_uint8(x_750, sizeof(void*)*1, x_751);
x_752 = lean_unbox(x_747);
x_753 = lean_unbox(x_748);
x_754 = l_Lake_OutStream_logEntry(x_690, x_750, x_752, x_753, x_745);
lean_dec(x_750);
x_755 = lean_ctor_get(x_754, 1);
lean_inc(x_755);
if (lean_is_exclusive(x_754)) {
 lean_ctor_release(x_754, 0);
 lean_ctor_release(x_754, 1);
 x_756 = x_754;
} else {
 lean_dec_ref(x_754);
 x_756 = lean_box(0);
}
x_757 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_756)) {
 x_758 = lean_alloc_ctor(1, 2, 0);
} else {
 x_758 = x_756;
 lean_ctor_set_tag(x_758, 1);
}
lean_ctor_set(x_758, 0, x_757);
lean_ctor_set(x_758, 1, x_755);
return x_758;
}
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; uint8_t x_766; uint8_t x_767; uint8_t x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
lean_dec(x_702);
lean_dec(x_674);
lean_dec(x_3);
x_759 = lean_ctor_get(x_705, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_705, 1);
lean_inc(x_760);
lean_dec(x_705);
x_761 = lean_io_error_to_string(x_759);
x_762 = lean_box(1);
x_763 = lean_box(0);
x_764 = lean_box(3);
x_765 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_765, 0, x_761);
x_766 = lean_unbox(x_764);
lean_ctor_set_uint8(x_765, sizeof(void*)*1, x_766);
x_767 = lean_unbox(x_762);
x_768 = lean_unbox(x_763);
x_769 = l_Lake_OutStream_logEntry(x_690, x_765, x_767, x_768, x_760);
lean_dec(x_765);
x_770 = lean_ctor_get(x_769, 1);
lean_inc(x_770);
if (lean_is_exclusive(x_769)) {
 lean_ctor_release(x_769, 0);
 lean_ctor_release(x_769, 1);
 x_771 = x_769;
} else {
 lean_dec_ref(x_769);
 x_771 = lean_box(0);
}
x_772 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_771)) {
 x_773 = lean_alloc_ctor(1, 2, 0);
} else {
 x_773 = x_771;
 lean_ctor_set_tag(x_773, 1);
}
lean_ctor_set(x_773, 0, x_772);
lean_ctor_set(x_773, 1, x_770);
return x_773;
}
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; uint8_t x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
lean_dec(x_674);
x_774 = lean_ctor_get(x_704, 0);
lean_inc(x_774);
if (lean_is_exclusive(x_704)) {
 lean_ctor_release(x_704, 0);
 x_775 = x_704;
} else {
 lean_dec_ref(x_704);
 x_775 = lean_box(0);
}
x_776 = lean_ctor_get(x_774, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_774, 1);
lean_inc(x_777);
x_778 = lean_ctor_get(x_774, 2);
lean_inc(x_778);
x_779 = lean_box(x_685);
x_780 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_780, 0, x_779);
x_781 = lean_box(1);
x_782 = lean_unbox(x_781);
x_783 = l_Lean_Name_toString(x_777, x_782, x_780);
x_784 = l_Lake_setupFile___closed__0;
x_785 = lean_string_append(x_783, x_784);
x_786 = l_Lake_Module_setupFacet;
if (lean_is_scalar(x_775)) {
 x_787 = lean_alloc_ctor(0, 1, 0);
} else {
 x_787 = x_775;
 lean_ctor_set_tag(x_787, 0);
}
lean_ctor_set(x_787, 0, x_778);
x_788 = l_Lake_Module_keyword;
x_789 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_789, 0, x_787);
lean_ctor_set(x_789, 1, x_788);
lean_ctor_set(x_789, 2, x_774);
lean_ctor_set(x_789, 3, x_786);
x_790 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 7, 1);
lean_closure_set(x_790, 0, x_789);
x_791 = lean_box(x_685);
x_792 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 9, 3);
lean_closure_set(x_792, 0, x_790);
lean_closure_set(x_792, 1, x_785);
lean_closure_set(x_792, 2, x_791);
lean_inc(x_702);
x_793 = l_Lake_Workspace_runFetchM___redArg(x_702, x_792, x_3, x_703);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_793, 1);
lean_inc(x_795);
lean_dec(x_793);
x_796 = lean_ctor_get(x_794, 0);
lean_inc(x_796);
lean_dec(x_794);
x_797 = lean_io_wait(x_796, x_795);
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
if (lean_obj_tag(x_798) == 0)
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; uint8_t x_807; lean_object* x_808; lean_object* x_809; uint8_t x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; uint8_t x_847; lean_object* x_848; 
x_799 = lean_ctor_get(x_776, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_799, 3);
lean_inc(x_800);
lean_dec(x_799);
x_801 = lean_ctor_get(x_800, 1);
lean_inc(x_801);
lean_dec(x_800);
x_802 = lean_ctor_get(x_776, 2);
lean_inc(x_802);
lean_dec(x_776);
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
lean_dec(x_802);
x_804 = lean_ctor_get(x_797, 1);
lean_inc(x_804);
lean_dec(x_797);
x_805 = lean_ctor_get(x_798, 0);
lean_inc(x_805);
if (lean_is_exclusive(x_798)) {
 lean_ctor_release(x_798, 0);
 lean_ctor_release(x_798, 1);
 x_806 = x_798;
} else {
 lean_dec_ref(x_798);
 x_806 = lean_box(0);
}
x_807 = lean_ctor_get_uint8(x_801, sizeof(void*)*13);
x_808 = lean_ctor_get(x_801, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_801, 4);
lean_inc(x_809);
lean_dec(x_801);
x_810 = lean_ctor_get_uint8(x_803, sizeof(void*)*13);
x_811 = lean_ctor_get(x_803, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_803, 4);
lean_inc(x_812);
lean_dec(x_803);
x_813 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_702, x_805);
lean_dec(x_805);
lean_dec(x_702);
x_814 = lean_box(0);
x_847 = l_Lake_ordBuildType____x40_Lake_Config_LeanConfig___hyg_267_(x_807, x_810);
x_848 = lean_box(x_847);
if (lean_obj_tag(x_848) == 2)
{
if (x_685 == 0)
{
x_815 = x_810;
goto block_846;
}
else
{
x_815 = x_807;
goto block_846;
}
}
else
{
lean_dec(x_848);
x_815 = x_807;
goto block_846;
}
block_846:
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; 
x_816 = l_Lake_BuildType_leanOptions(x_815);
x_817 = l_Lean_LeanOptions_append(x_814, x_816);
x_818 = l_Lean_LeanOptions_ofArray(x_808);
lean_dec(x_808);
x_819 = l_Lean_LeanOptions_appendArray(x_818, x_809);
lean_dec(x_809);
x_820 = l_Lean_LeanOptions_append(x_817, x_819);
x_821 = l_Lean_LeanOptions_appendArray(x_820, x_811);
lean_dec(x_811);
x_822 = l_Lean_LeanOptions_appendArray(x_821, x_812);
lean_dec(x_812);
if (lean_is_scalar(x_806)) {
 x_823 = lean_alloc_ctor(0, 2, 0);
} else {
 x_823 = x_806;
}
lean_ctor_set(x_823, 0, x_813);
lean_ctor_set(x_823, 1, x_822);
x_824 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_823);
x_825 = l_Lean_Json_compress(x_824);
x_826 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_825, x_804);
if (lean_obj_tag(x_826) == 0)
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
if (lean_is_exclusive(x_826)) {
 lean_ctor_release(x_826, 0);
 lean_ctor_release(x_826, 1);
 x_829 = x_826;
} else {
 lean_dec_ref(x_826);
 x_829 = lean_box(0);
}
if (lean_is_scalar(x_829)) {
 x_830 = lean_alloc_ctor(0, 2, 0);
} else {
 x_830 = x_829;
}
lean_ctor_set(x_830, 0, x_827);
lean_ctor_set(x_830, 1, x_828);
return x_830;
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; uint8_t x_838; uint8_t x_839; uint8_t x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_831 = lean_ctor_get(x_826, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_826, 1);
lean_inc(x_832);
lean_dec(x_826);
x_833 = lean_io_error_to_string(x_831);
x_834 = lean_box(1);
x_835 = lean_box(0);
x_836 = lean_box(3);
x_837 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_837, 0, x_833);
x_838 = lean_unbox(x_836);
lean_ctor_set_uint8(x_837, sizeof(void*)*1, x_838);
x_839 = lean_unbox(x_834);
x_840 = lean_unbox(x_835);
x_841 = l_Lake_OutStream_logEntry(x_690, x_837, x_839, x_840, x_832);
lean_dec(x_837);
x_842 = lean_ctor_get(x_841, 1);
lean_inc(x_842);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 x_843 = x_841;
} else {
 lean_dec_ref(x_841);
 x_843 = lean_box(0);
}
x_844 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_843)) {
 x_845 = lean_alloc_ctor(1, 2, 0);
} else {
 x_845 = x_843;
 lean_ctor_set_tag(x_845, 1);
}
lean_ctor_set(x_845, 0, x_844);
lean_ctor_set(x_845, 1, x_842);
return x_845;
}
}
}
else
{
lean_object* x_849; lean_object* x_850; 
lean_dec(x_798);
lean_dec(x_776);
lean_dec(x_702);
x_849 = lean_ctor_get(x_797, 1);
lean_inc(x_849);
lean_dec(x_797);
x_850 = l_Lake_mkModuleSetup___closed__1;
x_5 = x_850;
x_6 = x_849;
goto block_23;
}
}
else
{
lean_object* x_851; lean_object* x_852; 
lean_dec(x_776);
lean_dec(x_702);
x_851 = lean_ctor_get(x_793, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_793, 1);
lean_inc(x_852);
lean_dec(x_793);
x_5 = x_851;
x_6 = x_852;
goto block_23;
}
}
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; uint8_t x_857; uint8_t x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
lean_dec(x_674);
lean_dec(x_3);
x_853 = lean_ctor_get(x_701, 1);
lean_inc(x_853);
lean_dec(x_701);
x_854 = lean_box(1);
x_855 = lean_box(0);
x_856 = l_Lake_setupFile___closed__2;
x_857 = lean_unbox(x_854);
x_858 = lean_unbox(x_855);
x_859 = l_Lake_OutStream_logEntry(x_690, x_856, x_857, x_858, x_853);
x_860 = lean_ctor_get(x_859, 1);
lean_inc(x_860);
if (lean_is_exclusive(x_859)) {
 lean_ctor_release(x_859, 0);
 lean_ctor_release(x_859, 1);
 x_861 = x_859;
} else {
 lean_dec_ref(x_859);
 x_861 = lean_box(0);
}
x_862 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_861)) {
 x_863 = lean_alloc_ctor(1, 2, 0);
} else {
 x_863 = x_861;
 lean_ctor_set_tag(x_863, 1);
}
lean_ctor_set(x_863, 0, x_862);
lean_ctor_set(x_863, 1, x_860);
return x_863;
}
}
else
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; 
lean_dec(x_674);
lean_dec(x_3);
lean_dec(x_1);
x_864 = lean_ctor_get(x_687, 1);
lean_inc(x_864);
lean_dec(x_687);
x_865 = lean_ctor_get(x_688, 0);
lean_inc(x_865);
lean_dec(x_688);
x_866 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_865, x_864);
if (lean_obj_tag(x_866) == 0)
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_867 = lean_ctor_get(x_866, 1);
lean_inc(x_867);
lean_dec(x_866);
x_868 = l_Lake_setupFile___closed__3;
x_869 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_868, x_867);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_870 = lean_ctor_get(x_869, 1);
lean_inc(x_870);
if (lean_is_exclusive(x_869)) {
 lean_ctor_release(x_869, 0);
 lean_ctor_release(x_869, 1);
 x_871 = x_869;
} else {
 lean_dec_ref(x_869);
 x_871 = lean_box(0);
}
x_872 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_871)) {
 x_873 = lean_alloc_ctor(1, 2, 0);
} else {
 x_873 = x_871;
 lean_ctor_set_tag(x_873, 1);
}
lean_ctor_set(x_873, 0, x_872);
lean_ctor_set(x_873, 1, x_870);
return x_873;
}
else
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; uint8_t x_882; uint8_t x_883; uint8_t x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; 
x_874 = lean_ctor_get(x_869, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_869, 1);
lean_inc(x_875);
lean_dec(x_869);
x_876 = lean_io_error_to_string(x_874);
x_877 = lean_box(1);
x_878 = lean_box(0);
x_879 = lean_box(1);
x_880 = lean_box(3);
x_881 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_881, 0, x_876);
x_882 = lean_unbox(x_880);
lean_ctor_set_uint8(x_881, sizeof(void*)*1, x_882);
x_883 = lean_unbox(x_877);
x_884 = lean_unbox(x_878);
x_885 = l_Lake_OutStream_logEntry(x_879, x_881, x_883, x_884, x_875);
lean_dec(x_881);
x_886 = lean_ctor_get(x_885, 1);
lean_inc(x_886);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 x_887 = x_885;
} else {
 lean_dec_ref(x_885);
 x_887 = lean_box(0);
}
x_888 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_887)) {
 x_889 = lean_alloc_ctor(1, 2, 0);
} else {
 x_889 = x_887;
 lean_ctor_set_tag(x_889, 1);
}
lean_ctor_set(x_889, 0, x_888);
lean_ctor_set(x_889, 1, x_886);
return x_889;
}
}
else
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; uint8_t x_898; uint8_t x_899; uint8_t x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; 
x_890 = lean_ctor_get(x_866, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_866, 1);
lean_inc(x_891);
lean_dec(x_866);
x_892 = lean_io_error_to_string(x_890);
x_893 = lean_box(1);
x_894 = lean_box(0);
x_895 = lean_box(1);
x_896 = lean_box(3);
x_897 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_897, 0, x_892);
x_898 = lean_unbox(x_896);
lean_ctor_set_uint8(x_897, sizeof(void*)*1, x_898);
x_899 = lean_unbox(x_893);
x_900 = lean_unbox(x_894);
x_901 = l_Lake_OutStream_logEntry(x_895, x_897, x_899, x_900, x_891);
lean_dec(x_897);
x_902 = lean_ctor_get(x_901, 1);
lean_inc(x_902);
if (lean_is_exclusive(x_901)) {
 lean_ctor_release(x_901, 0);
 lean_ctor_release(x_901, 1);
 x_903 = x_901;
} else {
 lean_dec_ref(x_901);
 x_903 = lean_box(0);
}
x_904 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_903)) {
 x_905 = lean_alloc_ctor(1, 2, 0);
} else {
 x_905 = x_903;
 lean_ctor_set_tag(x_905, 1);
}
lean_ctor_set(x_905, 0, x_904);
lean_ctor_set(x_905, 1, x_902);
return x_905;
}
}
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; 
lean_dec(x_674);
lean_dec(x_3);
lean_dec(x_1);
x_906 = lean_ctor_get(x_676, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_906, 4);
lean_inc(x_907);
lean_dec(x_906);
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
lean_dec(x_907);
x_909 = l_Lake_Env_leanPath(x_676);
x_910 = l_Lake_Env_leanSrcPath(x_676);
lean_dec(x_676);
x_911 = l_Lake_setupFile___closed__4;
x_912 = l_Lake_setupFile___closed__5;
x_913 = lean_array_push(x_912, x_908);
x_914 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_914, 0, x_909);
lean_ctor_set(x_914, 1, x_910);
lean_ctor_set(x_914, 2, x_911);
lean_ctor_set(x_914, 3, x_913);
x_915 = lean_box(0);
x_916 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_916, 0, x_914);
lean_ctor_set(x_916, 1, x_915);
x_917 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_137_(x_916);
x_918 = l_Lean_Json_compress(x_917);
x_919 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_918, x_680);
if (lean_obj_tag(x_919) == 0)
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_920 = lean_ctor_get(x_919, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_919, 1);
lean_inc(x_921);
if (lean_is_exclusive(x_919)) {
 lean_ctor_release(x_919, 0);
 lean_ctor_release(x_919, 1);
 x_922 = x_919;
} else {
 lean_dec_ref(x_919);
 x_922 = lean_box(0);
}
if (lean_is_scalar(x_922)) {
 x_923 = lean_alloc_ctor(0, 2, 0);
} else {
 x_923 = x_922;
}
lean_ctor_set(x_923, 0, x_920);
lean_ctor_set(x_923, 1, x_921);
return x_923;
}
else
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; uint8_t x_932; uint8_t x_933; uint8_t x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; 
x_924 = lean_ctor_get(x_919, 0);
lean_inc(x_924);
x_925 = lean_ctor_get(x_919, 1);
lean_inc(x_925);
lean_dec(x_919);
x_926 = lean_io_error_to_string(x_924);
x_927 = lean_box(1);
x_928 = lean_box(0);
x_929 = lean_box(1);
x_930 = lean_box(3);
x_931 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_931, 0, x_926);
x_932 = lean_unbox(x_930);
lean_ctor_set_uint8(x_931, sizeof(void*)*1, x_932);
x_933 = lean_unbox(x_927);
x_934 = lean_unbox(x_928);
x_935 = l_Lake_OutStream_logEntry(x_929, x_931, x_933, x_934, x_925);
lean_dec(x_931);
x_936 = lean_ctor_get(x_935, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_935)) {
 lean_ctor_release(x_935, 0);
 lean_ctor_release(x_935, 1);
 x_937 = x_935;
} else {
 lean_dec_ref(x_935);
 x_937 = lean_box(0);
}
x_938 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_937)) {
 x_939 = lean_alloc_ctor(1, 2, 0);
} else {
 x_939 = x_937;
 lean_ctor_set_tag(x_939, 1);
}
lean_ctor_set(x_939, 0, x_938);
lean_ctor_set(x_939, 1, x_936);
return x_939;
}
}
}
else
{
lean_object* x_940; lean_object* x_941; 
lean_dec(x_679);
lean_dec(x_676);
lean_dec(x_674);
lean_dec(x_3);
lean_dec(x_1);
x_940 = l_Lake_setupFile___boxed__const__2;
if (lean_is_scalar(x_681)) {
 x_941 = lean_alloc_ctor(1, 2, 0);
} else {
 x_941 = x_681;
 lean_ctor_set_tag(x_941, 1);
}
lean_ctor_set(x_941, 0, x_940);
lean_ctor_set(x_941, 1, x_680);
return x_941;
}
}
block_23:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; 
x_7 = lean_io_error_to_string(x_5);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_box(1);
x_11 = lean_box(3);
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_7);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_13);
x_14 = lean_unbox(x_8);
x_15 = lean_unbox(x_9);
x_16 = l_Lake_OutStream_logEntry(x_10, x_12, x_14, x_15, x_6);
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lake_setupFile___boxed__const__1;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lake_setupFile___lam__0(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_setupFile___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_setupFile___lam__3(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_7);
x_10 = lean_array_uget(x_4, x_5);
x_11 = l_Lake_OutStream_logEntry(x_1, x_10, x_2, x_3, x_8);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
x_7 = x_12;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
}
static lean_object* _init_l_Lake_serve___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 0, 3);
x_3 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 0, x_3);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 1, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 2, x_5);
return x_2;
}
}
static lean_object* _init_l_Lake_serve___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--server", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_serve___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_serve___closed__1;
x_2 = l_Lake_setupFile___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_serve___closed__3() {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_inc(x_1);
x_29 = lean_alloc_closure((void*)(l_Lake_loadWorkspace), 3, 1);
lean_closure_set(x_29, 0, x_1);
x_30 = l_Lake_LoggerIO_captureLog___redArg(x_29, x_3);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get_size(x_34);
x_60 = lean_nat_dec_lt(x_58, x_59);
if (x_60 == 0)
{
lean_dec(x_59);
x_36 = x_32;
goto block_57;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_59, x_59);
if (x_61 == 0)
{
lean_dec(x_59);
x_36 = x_32;
goto block_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_62 = lean_box(1);
x_63 = lean_box(0);
x_64 = lean_box(1);
x_65 = lean_box(0);
x_66 = 0;
x_67 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_68 = lean_unbox(x_62);
x_69 = lean_unbox(x_63);
x_70 = l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(x_64, x_68, x_69, x_34, x_66, x_67, x_65, x_32);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_36 = x_71;
goto block_57;
}
}
block_28:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 7);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lake_serve___closed__0;
x_11 = l_Lake_serve___closed__2;
x_12 = l_Array_append___redArg(x_11, x_5);
lean_dec(x_5);
x_13 = l_Array_append___redArg(x_12, x_2);
x_14 = lean_box(0);
x_15 = lean_box(1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_4);
x_18 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_18);
x_19 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_19);
x_20 = lean_io_process_spawn(x_17, x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_io_process_child_wait(x_10, x_21, x_22);
lean_dec(x_21);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
block_57:
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lake_serve___closed__3;
x_38 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_37, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = l_Lake_Env_baseVars(x_40);
x_42 = l_Lake_invalidConfigEnvVar___closed__0;
x_43 = l_Lake_Log_toString(x_34);
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
if (lean_is_scalar(x_35)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_35;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_array_push(x_41, x_45);
x_47 = l_Lake_setupFile___closed__4;
x_4 = x_46;
x_5 = x_47;
x_6 = x_39;
goto block_28;
}
else
{
uint8_t x_48; 
lean_dec(x_35);
lean_dec(x_34);
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
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_35);
lean_dec(x_34);
x_52 = lean_ctor_get(x_33, 0);
lean_inc(x_52);
lean_dec(x_33);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 3);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 4);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lake_Workspace_augmentedEnvVars(x_52);
x_4 = x_56;
x_5 = x_55;
x_6 = x_36;
goto block_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(x_1, x_9, x_10, x_4, x_11, x_12, x_7, x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
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
l_Lake_invalidConfigEnvVar___closed__0 = _init_l_Lake_invalidConfigEnvVar___closed__0();
lean_mark_persistent(l_Lake_invalidConfigEnvVar___closed__0);
l_Lake_invalidConfigEnvVar = _init_l_Lake_invalidConfigEnvVar();
lean_mark_persistent(l_Lake_invalidConfigEnvVar);
l_Lake_mkModuleSetup___closed__0 = _init_l_Lake_mkModuleSetup___closed__0();
lean_mark_persistent(l_Lake_mkModuleSetup___closed__0);
l_Lake_mkModuleSetup___closed__1 = _init_l_Lake_mkModuleSetup___closed__1();
lean_mark_persistent(l_Lake_mkModuleSetup___closed__1);
l_Lake_setupFile___closed__0 = _init_l_Lake_setupFile___closed__0();
lean_mark_persistent(l_Lake_setupFile___closed__0);
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
l_Lake_setupFile___boxed__const__1 = _init_l_Lake_setupFile___boxed__const__1();
lean_mark_persistent(l_Lake_setupFile___boxed__const__1);
l_Lake_setupFile___boxed__const__2 = _init_l_Lake_setupFile___boxed__const__2();
lean_mark_persistent(l_Lake_setupFile___boxed__const__2);
l_Lake_serve___closed__0 = _init_l_Lake_serve___closed__0();
lean_mark_persistent(l_Lake_serve___closed__0);
l_Lake_serve___closed__1 = _init_l_Lake_serve___closed__1();
lean_mark_persistent(l_Lake_serve___closed__1);
l_Lake_serve___closed__2 = _init_l_Lake_serve___closed__2();
lean_mark_persistent(l_Lake_serve___closed__2);
l_Lake_serve___closed__3 = _init_l_Lake_serve___closed__3();
lean_mark_persistent(l_Lake_serve___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
