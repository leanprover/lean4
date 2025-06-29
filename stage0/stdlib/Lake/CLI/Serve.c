// Lean compiler output
// Module: Lake.CLI.Serve
// Imports: Lake.Load Lake.Build Lake.Util.MainM
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
lean_object* l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(lean_object*);
static lean_object* l_Lake_setupFile___closed__5;
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l_Lake_mkModuleSetup___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_io_getenv(lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__3;
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
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ensureJob___at___Lake_Module_recFetchSetup_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lake_mkModuleSetup___closed__2;
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_invalidConfigEnvVar;
LEAN_EXPORT uint8_t l_Lake_setupFile___lam__1(uint8_t, lean_object*);
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
static lean_object* l_Lake_mkModuleSetup___closed__1;
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__0;
lean_object* l_Lake_buildImportsAndDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lake_setupFile___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lake_configModuleName;
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
x_1 = lean_mk_string_unchecked("_unknown", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_mkModuleSetup___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_mkModuleSetup___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mkModuleSetup___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_mkModuleSetup___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_mkModuleSetup___closed__2;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_mkModuleSetup(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_dec(x_3);
x_9 = lean_alloc_closure((void*)(l_Lake_buildImportsAndDeps), 9, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_7);
x_10 = l_Lake_Workspace_runFetchM___redArg(x_1, x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_io_wait(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_closure((void*)(l_Lake_mkModuleSetup___lam__0___boxed), 1, 0);
x_22 = l_Lake_mkModuleSetup___closed__1;
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_array_size(x_19);
x_26 = 0;
lean_inc(x_21);
x_27 = l_Array_mapMUnsafe_map___at___Lake_Module_recFetchSetup_spec__4(x_21, x_25, x_26, x_19);
x_28 = lean_array_size(x_20);
x_29 = l_Array_mapMUnsafe_map___at___Lake_Module_recFetchSetup_spec__4(x_21, x_28, x_26, x_20);
x_30 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_27);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_4);
lean_ctor_set_uint8(x_30, sizeof(void*)*6, x_8);
lean_ctor_set(x_14, 0, x_30);
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_alloc_closure((void*)(l_Lake_mkModuleSetup___lam__0___boxed), 1, 0);
x_35 = l_Lake_mkModuleSetup___closed__1;
x_36 = lean_box(0);
x_37 = lean_box(0);
x_38 = lean_array_size(x_32);
x_39 = 0;
lean_inc(x_34);
x_40 = l_Array_mapMUnsafe_map___at___Lake_Module_recFetchSetup_spec__4(x_34, x_38, x_39, x_32);
x_41 = lean_array_size(x_33);
x_42 = l_Array_mapMUnsafe_map___at___Lake_Module_recFetchSetup_spec__4(x_34, x_41, x_39, x_33);
x_43 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set(x_43, 5, x_4);
lean_ctor_set_uint8(x_43, sizeof(void*)*6, x_8);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_31);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_15);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_14, 0);
lean_dec(x_46);
x_47 = l_Lake_mkModuleSetup___closed__3;
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_47);
return x_14;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_dec(x_14);
x_49 = l_Lake_mkModuleSetup___closed__3;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_10);
if (x_51 == 0)
{
return x_10;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_10, 0);
x_53 = lean_ctor_get(x_10, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_10);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
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
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_8);
x_11 = l_Lake_ensureJob___at___Lake_Module_recFetchSetup_spec__7(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_18 = lean_ctor_get(x_13, 2);
lean_dec(x_18);
x_19 = lean_ctor_get(x_8, 3);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_st_ref_take(x_19, x_14);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_3);
lean_inc(x_13);
x_23 = l_Lake_Job_toOpaque___redArg(x_13);
x_24 = lean_array_push(x_21, x_23);
x_25 = lean_st_ref_set(x_19, x_24, x_22);
lean_dec(x_19);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = l_Lake_Job_renew___redArg(x_13);
lean_ctor_set(x_12, 0, x_28);
lean_ctor_set(x_25, 0, x_12);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lake_Job_renew___redArg(x_13);
lean_ctor_set(x_12, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_ctor_get(x_8, 3);
lean_inc(x_34);
lean_dec(x_8);
x_35 = lean_st_ref_take(x_34, x_14);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_2);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_3);
lean_inc(x_38);
x_39 = l_Lake_Job_toOpaque___redArg(x_38);
x_40 = lean_array_push(x_36, x_39);
x_41 = lean_st_ref_set(x_34, x_40, x_37);
lean_dec(x_34);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = l_Lake_Job_renew___redArg(x_38);
lean_ctor_set(x_12, 0, x_44);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_dec(x_12);
x_47 = lean_ctor_get(x_13, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 x_49 = x_13;
} else {
 lean_dec_ref(x_13);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_8, 3);
lean_inc(x_50);
lean_dec(x_8);
x_51 = lean_st_ref_take(x_50, x_14);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 3, 1);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_48);
lean_ctor_set(x_54, 2, x_2);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_3);
lean_inc(x_54);
x_55 = l_Lake_Job_toOpaque___redArg(x_54);
x_56 = lean_array_push(x_52, x_55);
x_57 = lean_st_ref_set(x_50, x_56, x_53);
lean_dec(x_50);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = l_Lake_Job_renew___redArg(x_54);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_46);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
return x_62;
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
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_inc(x_2);
x_25 = l_Lake_resolvePath(x_2, x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
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
x_46 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_47 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
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
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_110; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_26);
x_110 = l_Lake_Workspace_findModuleBySrc_x3f(x_26, x_54);
if (lean_obj_tag(x_110) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_111; 
x_111 = l_IO_FS_readFile(x_26, x_55);
lean_dec(x_26);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_2);
x_114 = l_Lean_parseImports_x27(x_112, x_2, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_56 = x_115;
x_57 = x_116;
goto block_109;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_2);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_dec(x_114);
x_119 = lean_io_error_to_string(x_117);
x_120 = lean_box(1);
x_121 = lean_box(0);
x_122 = lean_box(3);
x_123 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_123, 0, x_119);
x_124 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, sizeof(void*)*1, x_124);
x_125 = lean_unbox(x_120);
x_126 = lean_unbox(x_121);
x_127 = l_Lake_OutStream_logEntry(x_42, x_123, x_125, x_126, x_118);
lean_dec(x_123);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_127, 0);
lean_dec(x_129);
x_130 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_127, 1);
lean_ctor_set(x_127, 0, x_130);
return x_127;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
lean_dec(x_127);
x_132 = l_Lake_setupFile___boxed__const__1;
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_2);
x_134 = lean_ctor_get(x_111, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_111, 1);
lean_inc(x_135);
lean_dec(x_111);
x_136 = lean_io_error_to_string(x_134);
x_137 = lean_box(1);
x_138 = lean_box(0);
x_139 = lean_box(3);
x_140 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_140, 0, x_136);
x_141 = lean_unbox(x_139);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_141);
x_142 = lean_unbox(x_137);
x_143 = lean_unbox(x_138);
x_144 = l_Lake_OutStream_logEntry(x_42, x_140, x_142, x_143, x_135);
lean_dec(x_140);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_144, 0);
lean_dec(x_146);
x_147 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_144, 1);
lean_ctor_set(x_144, 0, x_147);
return x_144;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_dec(x_144);
x_149 = l_Lake_setupFile___boxed__const__1;
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
}
else
{
lean_object* x_151; 
lean_dec(x_26);
x_151 = lean_ctor_get(x_3, 0);
lean_inc(x_151);
lean_dec(x_3);
x_56 = x_151;
x_57 = x_55;
goto block_109;
}
}
else
{
uint8_t x_152; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_110);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_153 = lean_ctor_get(x_110, 0);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 2);
lean_inc(x_155);
x_156 = lean_box(x_37);
x_157 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_157, 0, x_156);
x_158 = lean_box(1);
x_159 = lean_unbox(x_158);
x_160 = l_Lean_Name_toString(x_154, x_159, x_157);
x_161 = l_Lake_setupFile___closed__0;
x_162 = lean_string_append(x_160, x_161);
x_163 = l_Lake_Module_setupFacet;
lean_ctor_set_tag(x_110, 0);
lean_ctor_set(x_110, 0, x_155);
x_164 = l_Lake_Module_keyword;
x_165 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_165, 0, x_110);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_153);
lean_ctor_set(x_165, 3, x_163);
x_166 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 8, 1);
lean_closure_set(x_166, 0, x_165);
x_167 = lean_box(x_37);
x_168 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 10, 3);
lean_closure_set(x_168, 0, x_166);
lean_closure_set(x_168, 1, x_162);
lean_closure_set(x_168, 2, x_167);
x_169 = l_Lake_Workspace_runFetchM___redArg(x_54, x_168, x_4, x_55);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_io_wait(x_172, x_171);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
x_177 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_176);
x_178 = l_Lean_Json_compress(x_177);
x_179 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_178, x_175);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
return x_179;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_179);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; lean_object* x_194; uint8_t x_195; 
x_184 = lean_ctor_get(x_179, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_179, 1);
lean_inc(x_185);
lean_dec(x_179);
x_186 = lean_io_error_to_string(x_184);
x_187 = lean_box(1);
x_188 = lean_box(0);
x_189 = lean_box(3);
x_190 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_190, 0, x_186);
x_191 = lean_unbox(x_189);
lean_ctor_set_uint8(x_190, sizeof(void*)*1, x_191);
x_192 = lean_unbox(x_187);
x_193 = lean_unbox(x_188);
x_194 = l_Lake_OutStream_logEntry(x_42, x_190, x_192, x_193, x_185);
lean_dec(x_190);
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_194, 0);
lean_dec(x_196);
x_197 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_194, 1);
lean_ctor_set(x_194, 0, x_197);
return x_194;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_194, 1);
lean_inc(x_198);
lean_dec(x_194);
x_199 = l_Lake_setupFile___boxed__const__1;
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_174);
x_201 = lean_ctor_get(x_173, 1);
lean_inc(x_201);
lean_dec(x_173);
x_202 = l_Lake_mkModuleSetup___closed__3;
x_6 = x_202;
x_7 = x_201;
goto block_24;
}
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_169, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_169, 1);
lean_inc(x_204);
lean_dec(x_169);
x_6 = x_203;
x_7 = x_204;
goto block_24;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_205 = lean_ctor_get(x_110, 0);
lean_inc(x_205);
lean_dec(x_110);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 2);
lean_inc(x_207);
x_208 = lean_box(x_37);
x_209 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_209, 0, x_208);
x_210 = lean_box(1);
x_211 = lean_unbox(x_210);
x_212 = l_Lean_Name_toString(x_206, x_211, x_209);
x_213 = l_Lake_setupFile___closed__0;
x_214 = lean_string_append(x_212, x_213);
x_215 = l_Lake_Module_setupFacet;
x_216 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_216, 0, x_207);
x_217 = l_Lake_Module_keyword;
x_218 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_218, 2, x_205);
lean_ctor_set(x_218, 3, x_215);
x_219 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 8, 1);
lean_closure_set(x_219, 0, x_218);
x_220 = lean_box(x_37);
x_221 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 10, 3);
lean_closure_set(x_221, 0, x_219);
lean_closure_set(x_221, 1, x_214);
lean_closure_set(x_221, 2, x_220);
x_222 = l_Lake_Workspace_runFetchM___redArg(x_54, x_221, x_4, x_55);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_ctor_get(x_223, 0);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_io_wait(x_225, x_224);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_ctor_get(x_227, 0);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_229);
x_231 = l_Lean_Json_compress(x_230);
x_232 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_231, x_228);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_237 = lean_ctor_get(x_232, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_232, 1);
lean_inc(x_238);
lean_dec(x_232);
x_239 = lean_io_error_to_string(x_237);
x_240 = lean_box(1);
x_241 = lean_box(0);
x_242 = lean_box(3);
x_243 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_243, 0, x_239);
x_244 = lean_unbox(x_242);
lean_ctor_set_uint8(x_243, sizeof(void*)*1, x_244);
x_245 = lean_unbox(x_240);
x_246 = lean_unbox(x_241);
x_247 = l_Lake_OutStream_logEntry(x_42, x_243, x_245, x_246, x_238);
lean_dec(x_243);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_249 = x_247;
} else {
 lean_dec_ref(x_247);
 x_249 = lean_box(0);
}
x_250 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_249;
 lean_ctor_set_tag(x_251, 1);
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_248);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_227);
x_252 = lean_ctor_get(x_226, 1);
lean_inc(x_252);
lean_dec(x_226);
x_253 = l_Lake_mkModuleSetup___closed__3;
x_6 = x_253;
x_7 = x_252;
goto block_24;
}
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_222, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_222, 1);
lean_inc(x_255);
lean_dec(x_222);
x_6 = x_254;
x_7 = x_255;
goto block_24;
}
}
}
block_109:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 3);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 4);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_LeanOptions_ofArray(x_61);
lean_dec(x_61);
x_64 = l_Lean_LeanOptions_appendArray(x_63, x_62);
lean_dec(x_62);
x_65 = l_Lake_mkModuleSetup(x_54, x_2, x_56, x_64, x_4, x_57);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_66);
x_69 = l_Lean_Json_compress(x_68);
x_70 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_69, x_67);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
return x_70;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; uint8_t x_86; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_io_error_to_string(x_75);
x_78 = lean_box(1);
x_79 = lean_box(0);
x_80 = lean_box(3);
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_77);
x_82 = lean_unbox(x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_82);
x_83 = lean_unbox(x_78);
x_84 = lean_unbox(x_79);
x_85 = l_Lake_OutStream_logEntry(x_42, x_81, x_83, x_84, x_76);
lean_dec(x_81);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_85, 1);
lean_ctor_set(x_85, 0, x_88);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = l_Lake_setupFile___boxed__const__1;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; uint8_t x_103; 
x_92 = lean_ctor_get(x_65, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_65, 1);
lean_inc(x_93);
lean_dec(x_65);
x_94 = lean_io_error_to_string(x_92);
x_95 = lean_box(1);
x_96 = lean_box(0);
x_97 = lean_box(3);
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_94);
x_99 = lean_unbox(x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_99);
x_100 = lean_unbox(x_95);
x_101 = lean_unbox(x_96);
x_102 = l_Lake_OutStream_logEntry(x_42, x_98, x_100, x_101, x_93);
lean_dec(x_98);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
x_105 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_102, 1);
lean_ctor_set(x_102, 0, x_105);
return x_102;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
lean_dec(x_102);
x_107 = l_Lake_setupFile___boxed__const__1;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; uint8_t x_261; lean_object* x_262; uint8_t x_263; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_256 = lean_ctor_get(x_53, 1);
lean_inc(x_256);
lean_dec(x_53);
x_257 = lean_box(1);
x_258 = lean_box(0);
x_259 = l_Lake_setupFile___closed__2;
x_260 = lean_unbox(x_257);
x_261 = lean_unbox(x_258);
x_262 = l_Lake_OutStream_logEntry(x_42, x_259, x_260, x_261, x_256);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_262, 0);
lean_dec(x_264);
x_265 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_262, 1);
lean_ctor_set(x_262, 0, x_265);
return x_262;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_262, 1);
lean_inc(x_266);
lean_dec(x_262);
x_267 = l_Lake_setupFile___boxed__const__1;
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_269 = lean_ctor_get(x_39, 1);
lean_inc(x_269);
lean_dec(x_39);
x_270 = lean_ctor_get(x_40, 0);
lean_inc(x_270);
lean_dec(x_40);
x_271 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_270, x_269);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
lean_dec(x_271);
x_273 = l_Lake_setupFile___closed__3;
x_274 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_273, x_272);
if (lean_obj_tag(x_274) == 0)
{
uint8_t x_275; 
x_275 = !lean_is_exclusive(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_274, 0);
lean_dec(x_276);
x_277 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_274, 1);
lean_ctor_set(x_274, 0, x_277);
return x_274;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_274, 1);
lean_inc(x_278);
lean_dec(x_274);
x_279 = l_Lake_setupFile___boxed__const__1;
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; uint8_t x_291; lean_object* x_292; uint8_t x_293; 
x_281 = lean_ctor_get(x_274, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_274, 1);
lean_inc(x_282);
lean_dec(x_274);
x_283 = lean_io_error_to_string(x_281);
x_284 = lean_box(1);
x_285 = lean_box(0);
x_286 = lean_box(1);
x_287 = lean_box(3);
x_288 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_288, 0, x_283);
x_289 = lean_unbox(x_287);
lean_ctor_set_uint8(x_288, sizeof(void*)*1, x_289);
x_290 = lean_unbox(x_284);
x_291 = lean_unbox(x_285);
x_292 = l_Lake_OutStream_logEntry(x_286, x_288, x_290, x_291, x_282);
lean_dec(x_288);
x_293 = !lean_is_exclusive(x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_292, 0);
lean_dec(x_294);
x_295 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_292, 1);
lean_ctor_set(x_292, 0, x_295);
return x_292;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_292, 1);
lean_inc(x_296);
lean_dec(x_292);
x_297 = l_Lake_setupFile___boxed__const__1;
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_296);
return x_298;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_308; uint8_t x_309; lean_object* x_310; uint8_t x_311; 
x_299 = lean_ctor_get(x_271, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_271, 1);
lean_inc(x_300);
lean_dec(x_271);
x_301 = lean_io_error_to_string(x_299);
x_302 = lean_box(1);
x_303 = lean_box(0);
x_304 = lean_box(1);
x_305 = lean_box(3);
x_306 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_306, 0, x_301);
x_307 = lean_unbox(x_305);
lean_ctor_set_uint8(x_306, sizeof(void*)*1, x_307);
x_308 = lean_unbox(x_302);
x_309 = lean_unbox(x_303);
x_310 = l_Lake_OutStream_logEntry(x_304, x_306, x_308, x_309, x_300);
lean_dec(x_306);
x_311 = !lean_is_exclusive(x_310);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_310, 0);
lean_dec(x_312);
x_313 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_310, 1);
lean_ctor_set(x_310, 0, x_313);
return x_310;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_310, 1);
lean_inc(x_314);
lean_dec(x_310);
x_315 = l_Lake_setupFile___boxed__const__1;
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
}
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_317 = lean_ctor_get(x_28, 0);
lean_inc(x_317);
lean_dec(x_28);
x_318 = lean_ctor_get(x_317, 4);
lean_inc(x_318);
lean_dec(x_317);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
lean_dec(x_318);
x_320 = l_Lake_configModuleName;
x_321 = lean_box(0);
x_322 = lean_box(0);
x_323 = l_Lake_setupFile___closed__4;
x_324 = l_Lake_setupFile___closed__5;
x_325 = lean_array_push(x_324, x_319);
x_326 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_326, 0, x_320);
lean_ctor_set(x_326, 1, x_321);
lean_ctor_set(x_326, 2, x_322);
lean_ctor_set(x_326, 3, x_323);
lean_ctor_set(x_326, 4, x_325);
lean_ctor_set(x_326, 5, x_322);
lean_ctor_set_uint8(x_326, sizeof(void*)*6, x_36);
x_327 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_326);
x_328 = l_Lean_Json_compress(x_327);
x_329 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_328, x_33);
if (lean_obj_tag(x_329) == 0)
{
uint8_t x_330; 
x_330 = !lean_is_exclusive(x_329);
if (x_330 == 0)
{
return x_329;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_329, 0);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_329);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; uint8_t x_343; uint8_t x_344; lean_object* x_345; uint8_t x_346; 
x_334 = lean_ctor_get(x_329, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_329, 1);
lean_inc(x_335);
lean_dec(x_329);
x_336 = lean_io_error_to_string(x_334);
x_337 = lean_box(1);
x_338 = lean_box(0);
x_339 = lean_box(1);
x_340 = lean_box(3);
x_341 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_341, 0, x_336);
x_342 = lean_unbox(x_340);
lean_ctor_set_uint8(x_341, sizeof(void*)*1, x_342);
x_343 = lean_unbox(x_337);
x_344 = lean_unbox(x_338);
x_345 = l_Lake_OutStream_logEntry(x_339, x_341, x_343, x_344, x_335);
lean_dec(x_341);
x_346 = !lean_is_exclusive(x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_345, 0);
lean_dec(x_347);
x_348 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_345, 1);
lean_ctor_set(x_345, 0, x_348);
return x_345;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_345, 1);
lean_inc(x_349);
lean_dec(x_345);
x_350 = l_Lake_setupFile___boxed__const__1;
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_349);
return x_351;
}
}
}
}
else
{
lean_object* x_352; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_352 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 0, x_352);
return x_30;
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_353 = lean_ctor_get(x_30, 0);
x_354 = lean_ctor_get(x_30, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_30);
x_355 = lean_string_utf8_byte_size(x_353);
x_356 = lean_unsigned_to_nat(0u);
x_357 = lean_nat_dec_eq(x_355, x_356);
lean_dec(x_355);
if (x_357 == 0)
{
uint8_t x_358; 
x_358 = lean_string_dec_eq(x_353, x_26);
lean_dec(x_353);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_28);
x_359 = l_Lake_invalidConfigEnvVar___closed__0;
x_360 = lean_io_getenv(x_359, x_354);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = lean_box(1);
x_364 = l_Lake_OutStream_get(x_363, x_362);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_367 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_368 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
lean_inc(x_365);
x_369 = l_Lake_AnsiMode_isEnabled(x_365, x_368, x_366);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
x_372 = lean_box(x_367);
x_373 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_373, 0, x_365);
lean_closure_set(x_373, 1, x_372);
lean_closure_set(x_373, 2, x_370);
x_374 = l_Lake_loadWorkspace(x_1, x_373, x_371);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_427; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
lean_inc(x_26);
x_427 = l_Lake_Workspace_findModuleBySrc_x3f(x_26, x_375);
if (lean_obj_tag(x_427) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_428; 
x_428 = l_IO_FS_readFile(x_26, x_376);
lean_dec(x_26);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
lean_inc(x_2);
x_431 = l_Lean_parseImports_x27(x_429, x_2, x_430);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
x_377 = x_432;
x_378 = x_433;
goto block_426;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; uint8_t x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_375);
lean_dec(x_4);
lean_dec(x_2);
x_434 = lean_ctor_get(x_431, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_431, 1);
lean_inc(x_435);
lean_dec(x_431);
x_436 = lean_io_error_to_string(x_434);
x_437 = lean_box(1);
x_438 = lean_box(0);
x_439 = lean_box(3);
x_440 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_440, 0, x_436);
x_441 = lean_unbox(x_439);
lean_ctor_set_uint8(x_440, sizeof(void*)*1, x_441);
x_442 = lean_unbox(x_437);
x_443 = lean_unbox(x_438);
x_444 = l_Lake_OutStream_logEntry(x_363, x_440, x_442, x_443, x_435);
lean_dec(x_440);
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_446 = x_444;
} else {
 lean_dec_ref(x_444);
 x_446 = lean_box(0);
}
x_447 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_446;
 lean_ctor_set_tag(x_448, 1);
}
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_445);
return x_448;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; uint8_t x_456; uint8_t x_457; uint8_t x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_375);
lean_dec(x_4);
lean_dec(x_2);
x_449 = lean_ctor_get(x_428, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_428, 1);
lean_inc(x_450);
lean_dec(x_428);
x_451 = lean_io_error_to_string(x_449);
x_452 = lean_box(1);
x_453 = lean_box(0);
x_454 = lean_box(3);
x_455 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_455, 0, x_451);
x_456 = lean_unbox(x_454);
lean_ctor_set_uint8(x_455, sizeof(void*)*1, x_456);
x_457 = lean_unbox(x_452);
x_458 = lean_unbox(x_453);
x_459 = l_Lake_OutStream_logEntry(x_363, x_455, x_457, x_458, x_450);
lean_dec(x_455);
x_460 = lean_ctor_get(x_459, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_461 = x_459;
} else {
 lean_dec_ref(x_459);
 x_461 = lean_box(0);
}
x_462 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_461)) {
 x_463 = lean_alloc_ctor(1, 2, 0);
} else {
 x_463 = x_461;
 lean_ctor_set_tag(x_463, 1);
}
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_460);
return x_463;
}
}
else
{
lean_object* x_464; 
lean_dec(x_26);
x_464 = lean_ctor_get(x_3, 0);
lean_inc(x_464);
lean_dec(x_3);
x_377 = x_464;
x_378 = x_376;
goto block_426;
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
x_465 = lean_ctor_get(x_427, 0);
lean_inc(x_465);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 x_466 = x_427;
} else {
 lean_dec_ref(x_427);
 x_466 = lean_box(0);
}
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_465, 2);
lean_inc(x_468);
x_469 = lean_box(x_358);
x_470 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_470, 0, x_469);
x_471 = lean_box(1);
x_472 = lean_unbox(x_471);
x_473 = l_Lean_Name_toString(x_467, x_472, x_470);
x_474 = l_Lake_setupFile___closed__0;
x_475 = lean_string_append(x_473, x_474);
x_476 = l_Lake_Module_setupFacet;
if (lean_is_scalar(x_466)) {
 x_477 = lean_alloc_ctor(0, 1, 0);
} else {
 x_477 = x_466;
 lean_ctor_set_tag(x_477, 0);
}
lean_ctor_set(x_477, 0, x_468);
x_478 = l_Lake_Module_keyword;
x_479 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
lean_ctor_set(x_479, 2, x_465);
lean_ctor_set(x_479, 3, x_476);
x_480 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 8, 1);
lean_closure_set(x_480, 0, x_479);
x_481 = lean_box(x_358);
x_482 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 10, 3);
lean_closure_set(x_482, 0, x_480);
lean_closure_set(x_482, 1, x_475);
lean_closure_set(x_482, 2, x_481);
x_483 = l_Lake_Workspace_runFetchM___redArg(x_375, x_482, x_4, x_376);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_483, 1);
lean_inc(x_485);
lean_dec(x_483);
x_486 = lean_ctor_get(x_484, 0);
lean_inc(x_486);
lean_dec(x_484);
x_487 = lean_io_wait(x_486, x_485);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_489 = lean_ctor_get(x_487, 1);
lean_inc(x_489);
lean_dec(x_487);
x_490 = lean_ctor_get(x_488, 0);
lean_inc(x_490);
lean_dec(x_488);
x_491 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_490);
x_492 = l_Lean_Json_compress(x_491);
x_493 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_492, x_489);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_496 = x_493;
} else {
 lean_dec_ref(x_493);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_494);
lean_ctor_set(x_497, 1, x_495);
return x_497;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; uint8_t x_506; uint8_t x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_498 = lean_ctor_get(x_493, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_493, 1);
lean_inc(x_499);
lean_dec(x_493);
x_500 = lean_io_error_to_string(x_498);
x_501 = lean_box(1);
x_502 = lean_box(0);
x_503 = lean_box(3);
x_504 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_504, 0, x_500);
x_505 = lean_unbox(x_503);
lean_ctor_set_uint8(x_504, sizeof(void*)*1, x_505);
x_506 = lean_unbox(x_501);
x_507 = lean_unbox(x_502);
x_508 = l_Lake_OutStream_logEntry(x_363, x_504, x_506, x_507, x_499);
lean_dec(x_504);
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_510 = x_508;
} else {
 lean_dec_ref(x_508);
 x_510 = lean_box(0);
}
x_511 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_510)) {
 x_512 = lean_alloc_ctor(1, 2, 0);
} else {
 x_512 = x_510;
 lean_ctor_set_tag(x_512, 1);
}
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_509);
return x_512;
}
}
else
{
lean_object* x_513; lean_object* x_514; 
lean_dec(x_488);
x_513 = lean_ctor_get(x_487, 1);
lean_inc(x_513);
lean_dec(x_487);
x_514 = l_Lake_mkModuleSetup___closed__3;
x_6 = x_514;
x_7 = x_513;
goto block_24;
}
}
else
{
lean_object* x_515; lean_object* x_516; 
x_515 = lean_ctor_get(x_483, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_483, 1);
lean_inc(x_516);
lean_dec(x_483);
x_6 = x_515;
x_7 = x_516;
goto block_24;
}
}
block_426:
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_379 = lean_ctor_get(x_375, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_379, 3);
lean_inc(x_380);
lean_dec(x_379);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 4);
lean_inc(x_383);
lean_dec(x_381);
x_384 = l_Lean_LeanOptions_ofArray(x_382);
lean_dec(x_382);
x_385 = l_Lean_LeanOptions_appendArray(x_384, x_383);
lean_dec(x_383);
x_386 = l_Lake_mkModuleSetup(x_375, x_2, x_377, x_385, x_4, x_378);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_389 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_387);
x_390 = l_Lean_Json_compress(x_389);
x_391 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_390, x_388);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_394 = x_391;
} else {
 lean_dec_ref(x_391);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_393);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; uint8_t x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_396 = lean_ctor_get(x_391, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_391, 1);
lean_inc(x_397);
lean_dec(x_391);
x_398 = lean_io_error_to_string(x_396);
x_399 = lean_box(1);
x_400 = lean_box(0);
x_401 = lean_box(3);
x_402 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_402, 0, x_398);
x_403 = lean_unbox(x_401);
lean_ctor_set_uint8(x_402, sizeof(void*)*1, x_403);
x_404 = lean_unbox(x_399);
x_405 = lean_unbox(x_400);
x_406 = l_Lake_OutStream_logEntry(x_363, x_402, x_404, x_405, x_397);
lean_dec(x_402);
x_407 = lean_ctor_get(x_406, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_408 = x_406;
} else {
 lean_dec_ref(x_406);
 x_408 = lean_box(0);
}
x_409 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_408)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_408;
 lean_ctor_set_tag(x_410, 1);
}
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_407);
return x_410;
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; uint8_t x_419; uint8_t x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_411 = lean_ctor_get(x_386, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_386, 1);
lean_inc(x_412);
lean_dec(x_386);
x_413 = lean_io_error_to_string(x_411);
x_414 = lean_box(1);
x_415 = lean_box(0);
x_416 = lean_box(3);
x_417 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_417, 0, x_413);
x_418 = lean_unbox(x_416);
lean_ctor_set_uint8(x_417, sizeof(void*)*1, x_418);
x_419 = lean_unbox(x_414);
x_420 = lean_unbox(x_415);
x_421 = l_Lake_OutStream_logEntry(x_363, x_417, x_419, x_420, x_412);
lean_dec(x_417);
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_423 = x_421;
} else {
 lean_dec_ref(x_421);
 x_423 = lean_box(0);
}
x_424 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_423)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_423;
 lean_ctor_set_tag(x_425, 1);
}
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_422);
return x_425;
}
}
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_517 = lean_ctor_get(x_374, 1);
lean_inc(x_517);
lean_dec(x_374);
x_518 = lean_box(1);
x_519 = lean_box(0);
x_520 = l_Lake_setupFile___closed__2;
x_521 = lean_unbox(x_518);
x_522 = lean_unbox(x_519);
x_523 = l_Lake_OutStream_logEntry(x_363, x_520, x_521, x_522, x_517);
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_525 = x_523;
} else {
 lean_dec_ref(x_523);
 x_525 = lean_box(0);
}
x_526 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(1, 2, 0);
} else {
 x_527 = x_525;
 lean_ctor_set_tag(x_527, 1);
}
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_524);
return x_527;
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_528 = lean_ctor_get(x_360, 1);
lean_inc(x_528);
lean_dec(x_360);
x_529 = lean_ctor_get(x_361, 0);
lean_inc(x_529);
lean_dec(x_361);
x_530 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_529, x_528);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_531 = lean_ctor_get(x_530, 1);
lean_inc(x_531);
lean_dec(x_530);
x_532 = l_Lake_setupFile___closed__3;
x_533 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_532, x_531);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_534 = lean_ctor_get(x_533, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 x_535 = x_533;
} else {
 lean_dec_ref(x_533);
 x_535 = lean_box(0);
}
x_536 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_535)) {
 x_537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_537 = x_535;
 lean_ctor_set_tag(x_537, 1);
}
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_534);
return x_537;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; uint8_t x_547; uint8_t x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_538 = lean_ctor_get(x_533, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_533, 1);
lean_inc(x_539);
lean_dec(x_533);
x_540 = lean_io_error_to_string(x_538);
x_541 = lean_box(1);
x_542 = lean_box(0);
x_543 = lean_box(1);
x_544 = lean_box(3);
x_545 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_545, 0, x_540);
x_546 = lean_unbox(x_544);
lean_ctor_set_uint8(x_545, sizeof(void*)*1, x_546);
x_547 = lean_unbox(x_541);
x_548 = lean_unbox(x_542);
x_549 = l_Lake_OutStream_logEntry(x_543, x_545, x_547, x_548, x_539);
lean_dec(x_545);
x_550 = lean_ctor_get(x_549, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_551 = x_549;
} else {
 lean_dec_ref(x_549);
 x_551 = lean_box(0);
}
x_552 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_551)) {
 x_553 = lean_alloc_ctor(1, 2, 0);
} else {
 x_553 = x_551;
 lean_ctor_set_tag(x_553, 1);
}
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_550);
return x_553;
}
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint8_t x_562; uint8_t x_563; uint8_t x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_554 = lean_ctor_get(x_530, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_530, 1);
lean_inc(x_555);
lean_dec(x_530);
x_556 = lean_io_error_to_string(x_554);
x_557 = lean_box(1);
x_558 = lean_box(0);
x_559 = lean_box(1);
x_560 = lean_box(3);
x_561 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_561, 0, x_556);
x_562 = lean_unbox(x_560);
lean_ctor_set_uint8(x_561, sizeof(void*)*1, x_562);
x_563 = lean_unbox(x_557);
x_564 = lean_unbox(x_558);
x_565 = l_Lake_OutStream_logEntry(x_559, x_561, x_563, x_564, x_555);
lean_dec(x_561);
x_566 = lean_ctor_get(x_565, 1);
lean_inc(x_566);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_567 = x_565;
} else {
 lean_dec_ref(x_565);
 x_567 = lean_box(0);
}
x_568 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_567)) {
 x_569 = lean_alloc_ctor(1, 2, 0);
} else {
 x_569 = x_567;
 lean_ctor_set_tag(x_569, 1);
}
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_566);
return x_569;
}
}
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_570 = lean_ctor_get(x_28, 0);
lean_inc(x_570);
lean_dec(x_28);
x_571 = lean_ctor_get(x_570, 4);
lean_inc(x_571);
lean_dec(x_570);
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec(x_571);
x_573 = l_Lake_configModuleName;
x_574 = lean_box(0);
x_575 = lean_box(0);
x_576 = l_Lake_setupFile___closed__4;
x_577 = l_Lake_setupFile___closed__5;
x_578 = lean_array_push(x_577, x_572);
x_579 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_579, 0, x_573);
lean_ctor_set(x_579, 1, x_574);
lean_ctor_set(x_579, 2, x_575);
lean_ctor_set(x_579, 3, x_576);
lean_ctor_set(x_579, 4, x_578);
lean_ctor_set(x_579, 5, x_575);
lean_ctor_set_uint8(x_579, sizeof(void*)*6, x_357);
x_580 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_579);
x_581 = l_Lean_Json_compress(x_580);
x_582 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_581, x_354);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_585 = x_582;
} else {
 lean_dec_ref(x_582);
 x_585 = lean_box(0);
}
if (lean_is_scalar(x_585)) {
 x_586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_586 = x_585;
}
lean_ctor_set(x_586, 0, x_583);
lean_ctor_set(x_586, 1, x_584);
return x_586;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; uint8_t x_596; uint8_t x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_587 = lean_ctor_get(x_582, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_582, 1);
lean_inc(x_588);
lean_dec(x_582);
x_589 = lean_io_error_to_string(x_587);
x_590 = lean_box(1);
x_591 = lean_box(0);
x_592 = lean_box(1);
x_593 = lean_box(3);
x_594 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_594, 0, x_589);
x_595 = lean_unbox(x_593);
lean_ctor_set_uint8(x_594, sizeof(void*)*1, x_595);
x_596 = lean_unbox(x_590);
x_597 = lean_unbox(x_591);
x_598 = l_Lake_OutStream_logEntry(x_592, x_594, x_596, x_597, x_588);
lean_dec(x_594);
x_599 = lean_ctor_get(x_598, 1);
lean_inc(x_599);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_600 = x_598;
} else {
 lean_dec_ref(x_598);
 x_600 = lean_box(0);
}
x_601 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_600)) {
 x_602 = lean_alloc_ctor(1, 2, 0);
} else {
 x_602 = x_600;
 lean_ctor_set_tag(x_602, 1);
}
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_599);
return x_602;
}
}
}
else
{
lean_object* x_603; lean_object* x_604; 
lean_dec(x_353);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_603 = l_Lake_setupFile___boxed__const__2;
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_603);
lean_ctor_set(x_604, 1, x_354);
return x_604;
}
}
block_24:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_io_error_to_string(x_6);
x_9 = lean_box(1);
x_10 = lean_box(0);
x_11 = lean_box(1);
x_12 = lean_box(3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_8);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
x_15 = lean_unbox(x_9);
x_16 = lean_unbox(x_10);
x_17 = l_Lake_OutStream_logEntry(x_11, x_13, x_15, x_16, x_7);
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lake_setupFile___boxed__const__1;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
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
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lake_setupFile___lam__3(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
l_Lake_noConfigFileCode = _init_l_Lake_noConfigFileCode();
l_Lake_invalidConfigEnvVar___closed__0 = _init_l_Lake_invalidConfigEnvVar___closed__0();
lean_mark_persistent(l_Lake_invalidConfigEnvVar___closed__0);
l_Lake_invalidConfigEnvVar = _init_l_Lake_invalidConfigEnvVar();
lean_mark_persistent(l_Lake_invalidConfigEnvVar);
l_Lake_mkModuleSetup___closed__0 = _init_l_Lake_mkModuleSetup___closed__0();
lean_mark_persistent(l_Lake_mkModuleSetup___closed__0);
l_Lake_mkModuleSetup___closed__1 = _init_l_Lake_mkModuleSetup___closed__1();
lean_mark_persistent(l_Lake_mkModuleSetup___closed__1);
l_Lake_mkModuleSetup___closed__2 = _init_l_Lake_mkModuleSetup___closed__2();
lean_mark_persistent(l_Lake_mkModuleSetup___closed__2);
l_Lake_mkModuleSetup___closed__3 = _init_l_Lake_mkModuleSetup___closed__3();
lean_mark_persistent(l_Lake_mkModuleSetup___closed__3);
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
