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
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_setupFile___closed__1;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
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
lean_object* x_6; lean_object* x_7; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_2);
x_22 = l_Lake_resolvePath(x_2, x_5);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 6);
lean_inc(x_26);
x_27 = l_Lake_realConfigFile(x_26, x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_string_utf8_byte_size(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
lean_free_object(x_27);
x_34 = lean_string_dec_eq(x_29, x_23);
lean_dec(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_25);
x_35 = l_Lake_invalidConfigEnvVar___closed__0;
x_36 = lean_io_getenv(x_35, x_30);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_box(1);
x_40 = l_Lake_OutStream_get(x_39, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_44 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
lean_inc(x_41);
x_45 = l_Lake_AnsiMode_isEnabled(x_41, x_44, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_box(x_43);
x_49 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_49, 0, x_41);
lean_closure_set(x_49, 1, x_48);
lean_closure_set(x_49, 2, x_46);
x_50 = l_Lake_loadWorkspace(x_1, x_49, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_101; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_23);
x_101 = l_Lake_Workspace_findModuleBySrc_x3f(x_23, x_51);
if (lean_obj_tag(x_101) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_102; 
x_102 = l_IO_FS_readFile(x_23, x_52);
lean_dec(x_23);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_2);
x_105 = l_Lean_parseImports_x27(x_103, x_2, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_53 = x_106;
x_54 = x_107;
goto block_100;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_51);
lean_dec(x_4);
lean_dec(x_2);
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec(x_105);
x_110 = lean_io_error_to_string(x_108);
x_111 = 1;
x_112 = 0;
x_113 = 3;
x_114 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_113);
x_115 = l_Lake_OutStream_logEntry(x_39, x_114, x_111, x_112, x_109);
lean_dec(x_114);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
x_118 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_115, 1);
lean_ctor_set(x_115, 0, x_118);
return x_115;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_dec(x_115);
x_120 = l_Lake_setupFile___boxed__const__1;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
lean_dec(x_51);
lean_dec(x_4);
lean_dec(x_2);
x_122 = lean_ctor_get(x_102, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_102, 1);
lean_inc(x_123);
lean_dec(x_102);
x_124 = lean_io_error_to_string(x_122);
x_125 = 1;
x_126 = 0;
x_127 = 3;
x_128 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_127);
x_129 = l_Lake_OutStream_logEntry(x_39, x_128, x_125, x_126, x_123);
lean_dec(x_128);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_129, 0);
lean_dec(x_131);
x_132 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_129, 1);
lean_ctor_set(x_129, 0, x_132);
return x_129;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_dec(x_129);
x_134 = l_Lake_setupFile___boxed__const__1;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
else
{
lean_object* x_136; 
lean_dec(x_23);
x_136 = lean_ctor_get(x_3, 0);
lean_inc(x_136);
lean_dec(x_3);
x_53 = x_136;
x_54 = x_52;
goto block_100;
}
}
else
{
uint8_t x_137; 
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_2);
x_137 = !lean_is_exclusive(x_101);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_138 = lean_ctor_get(x_101, 0);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 2);
lean_inc(x_140);
x_141 = lean_box(x_34);
x_142 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_142, 0, x_141);
x_143 = 1;
x_144 = l_Lean_Name_toString(x_139, x_143, x_142);
x_145 = l_Lake_setupFile___closed__0;
x_146 = lean_string_append(x_144, x_145);
x_147 = l_Lake_Module_setupFacet;
lean_ctor_set_tag(x_101, 0);
lean_ctor_set(x_101, 0, x_140);
x_148 = l_Lake_Module_keyword;
x_149 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_149, 0, x_101);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_138);
lean_ctor_set(x_149, 3, x_147);
x_150 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 8, 1);
lean_closure_set(x_150, 0, x_149);
x_151 = lean_box(x_34);
x_152 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 10, 3);
lean_closure_set(x_152, 0, x_150);
lean_closure_set(x_152, 1, x_146);
lean_closure_set(x_152, 2, x_151);
x_153 = l_Lake_Workspace_runFetchM___redArg(x_51, x_152, x_4, x_52);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_io_wait(x_156, x_155);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_160);
x_162 = l_Lean_Json_compress(x_161);
x_163 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_162, x_159);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
return x_163;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_163);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_168 = lean_ctor_get(x_163, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_163, 1);
lean_inc(x_169);
lean_dec(x_163);
x_170 = lean_io_error_to_string(x_168);
x_171 = 1;
x_172 = 0;
x_173 = 3;
x_174 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_174, 0, x_170);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_173);
x_175 = l_Lake_OutStream_logEntry(x_39, x_174, x_171, x_172, x_169);
lean_dec(x_174);
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_175, 0);
lean_dec(x_177);
x_178 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_175, 1);
lean_ctor_set(x_175, 0, x_178);
return x_175;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
lean_dec(x_175);
x_180 = l_Lake_setupFile___boxed__const__1;
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_158);
x_182 = lean_ctor_get(x_157, 1);
lean_inc(x_182);
lean_dec(x_157);
x_183 = l_Lake_mkModuleSetup___closed__3;
x_6 = x_183;
x_7 = x_182;
goto block_21;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_153, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_153, 1);
lean_inc(x_185);
lean_dec(x_153);
x_6 = x_184;
x_7 = x_185;
goto block_21;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_186 = lean_ctor_get(x_101, 0);
lean_inc(x_186);
lean_dec(x_101);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 2);
lean_inc(x_188);
x_189 = lean_box(x_34);
x_190 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_190, 0, x_189);
x_191 = 1;
x_192 = l_Lean_Name_toString(x_187, x_191, x_190);
x_193 = l_Lake_setupFile___closed__0;
x_194 = lean_string_append(x_192, x_193);
x_195 = l_Lake_Module_setupFacet;
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_188);
x_197 = l_Lake_Module_keyword;
x_198 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set(x_198, 2, x_186);
lean_ctor_set(x_198, 3, x_195);
x_199 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 8, 1);
lean_closure_set(x_199, 0, x_198);
x_200 = lean_box(x_34);
x_201 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 10, 3);
lean_closure_set(x_201, 0, x_199);
lean_closure_set(x_201, 1, x_194);
lean_closure_set(x_201, 2, x_200);
x_202 = l_Lake_Workspace_runFetchM___redArg(x_51, x_201, x_4, x_52);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_io_wait(x_205, x_204);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_ctor_get(x_207, 0);
lean_inc(x_209);
lean_dec(x_207);
x_210 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_209);
x_211 = l_Lean_Json_compress(x_210);
x_212 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_211, x_208);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_215 = x_212;
} else {
 lean_dec_ref(x_212);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; uint8_t x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_217 = lean_ctor_get(x_212, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_212, 1);
lean_inc(x_218);
lean_dec(x_212);
x_219 = lean_io_error_to_string(x_217);
x_220 = 1;
x_221 = 0;
x_222 = 3;
x_223 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_223, 0, x_219);
lean_ctor_set_uint8(x_223, sizeof(void*)*1, x_222);
x_224 = l_Lake_OutStream_logEntry(x_39, x_223, x_220, x_221, x_218);
lean_dec(x_223);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
x_227 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_226;
 lean_ctor_set_tag(x_228, 1);
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_207);
x_229 = lean_ctor_get(x_206, 1);
lean_inc(x_229);
lean_dec(x_206);
x_230 = l_Lake_mkModuleSetup___closed__3;
x_6 = x_230;
x_7 = x_229;
goto block_21;
}
}
else
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_202, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_202, 1);
lean_inc(x_232);
lean_dec(x_202);
x_6 = x_231;
x_7 = x_232;
goto block_21;
}
}
}
block_100:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 3);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 4);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_LeanOptions_ofArray(x_58);
lean_dec(x_58);
x_61 = l_Lean_LeanOptions_appendArray(x_60, x_59);
lean_dec(x_59);
x_62 = l_Lake_mkModuleSetup(x_51, x_2, x_53, x_61, x_4, x_54);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_63);
x_66 = l_Lean_Json_compress(x_65);
x_67 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_66, x_64);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
return x_67;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_dec(x_67);
x_74 = lean_io_error_to_string(x_72);
x_75 = 1;
x_76 = 0;
x_77 = 3;
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = l_Lake_OutStream_logEntry(x_39, x_78, x_75, x_76, x_73);
lean_dec(x_78);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
x_82 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 0, x_82);
return x_79;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = l_Lake_setupFile___boxed__const__1;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_86 = lean_ctor_get(x_62, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_62, 1);
lean_inc(x_87);
lean_dec(x_62);
x_88 = lean_io_error_to_string(x_86);
x_89 = 1;
x_90 = 0;
x_91 = 3;
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
x_93 = l_Lake_OutStream_logEntry(x_39, x_92, x_89, x_90, x_87);
lean_dec(x_92);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
lean_dec(x_95);
x_96 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_93, 1);
lean_ctor_set(x_93, 0, x_96);
return x_93;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = l_Lake_setupFile___boxed__const__1;
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
else
{
lean_object* x_233; uint8_t x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_233 = lean_ctor_get(x_50, 1);
lean_inc(x_233);
lean_dec(x_50);
x_234 = 1;
x_235 = 0;
x_236 = l_Lake_setupFile___closed__2;
x_237 = l_Lake_OutStream_logEntry(x_39, x_236, x_234, x_235, x_233);
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_237, 0);
lean_dec(x_239);
x_240 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_237, 1);
lean_ctor_set(x_237, 0, x_240);
return x_237;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_237, 1);
lean_inc(x_241);
lean_dec(x_237);
x_242 = l_Lake_setupFile___boxed__const__1;
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_244 = lean_ctor_get(x_36, 1);
lean_inc(x_244);
lean_dec(x_36);
x_245 = lean_ctor_get(x_37, 0);
lean_inc(x_245);
lean_dec(x_37);
x_246 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_245, x_244);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec(x_246);
x_248 = l_Lake_setupFile___closed__3;
x_249 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_248, x_247);
if (lean_obj_tag(x_249) == 0)
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_249, 0);
lean_dec(x_251);
x_252 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_249, 1);
lean_ctor_set(x_249, 0, x_252);
return x_249;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_249, 1);
lean_inc(x_253);
lean_dec(x_249);
x_254 = l_Lake_setupFile___boxed__const__1;
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; uint8_t x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_256 = lean_ctor_get(x_249, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_249, 1);
lean_inc(x_257);
lean_dec(x_249);
x_258 = lean_io_error_to_string(x_256);
x_259 = 1;
x_260 = 0;
x_261 = lean_box(1);
x_262 = 3;
x_263 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_263, 0, x_258);
lean_ctor_set_uint8(x_263, sizeof(void*)*1, x_262);
x_264 = l_Lake_OutStream_logEntry(x_261, x_263, x_259, x_260, x_257);
lean_dec(x_263);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_264, 0);
lean_dec(x_266);
x_267 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_264, 1);
lean_ctor_set(x_264, 0, x_267);
return x_264;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_264, 1);
lean_inc(x_268);
lean_dec(x_264);
x_269 = l_Lake_setupFile___boxed__const__1;
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; uint8_t x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_271 = lean_ctor_get(x_246, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_246, 1);
lean_inc(x_272);
lean_dec(x_246);
x_273 = lean_io_error_to_string(x_271);
x_274 = 1;
x_275 = 0;
x_276 = lean_box(1);
x_277 = 3;
x_278 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_278, 0, x_273);
lean_ctor_set_uint8(x_278, sizeof(void*)*1, x_277);
x_279 = l_Lake_OutStream_logEntry(x_276, x_278, x_274, x_275, x_272);
lean_dec(x_278);
x_280 = !lean_is_exclusive(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_279, 0);
lean_dec(x_281);
x_282 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_279, 1);
lean_ctor_set(x_279, 0, x_282);
return x_279;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_279, 1);
lean_inc(x_283);
lean_dec(x_279);
x_284 = l_Lake_setupFile___boxed__const__1;
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_286 = lean_ctor_get(x_25, 0);
lean_inc(x_286);
lean_dec(x_25);
x_287 = lean_ctor_get(x_286, 4);
lean_inc(x_287);
lean_dec(x_286);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
lean_dec(x_287);
x_289 = l_Lake_configModuleName;
x_290 = lean_box(0);
x_291 = lean_box(0);
x_292 = l_Lake_setupFile___closed__4;
x_293 = l_Lake_setupFile___closed__5;
x_294 = lean_array_push(x_293, x_288);
x_295 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_295, 0, x_289);
lean_ctor_set(x_295, 1, x_290);
lean_ctor_set(x_295, 2, x_291);
lean_ctor_set(x_295, 3, x_292);
lean_ctor_set(x_295, 4, x_294);
lean_ctor_set(x_295, 5, x_291);
lean_ctor_set_uint8(x_295, sizeof(void*)*6, x_33);
x_296 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_295);
x_297 = l_Lean_Json_compress(x_296);
x_298 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_297, x_30);
if (lean_obj_tag(x_298) == 0)
{
uint8_t x_299; 
x_299 = !lean_is_exclusive(x_298);
if (x_299 == 0)
{
return x_298;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_298, 0);
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_298);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; uint8_t x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_303 = lean_ctor_get(x_298, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_298, 1);
lean_inc(x_304);
lean_dec(x_298);
x_305 = lean_io_error_to_string(x_303);
x_306 = 1;
x_307 = 0;
x_308 = lean_box(1);
x_309 = 3;
x_310 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_310, 0, x_305);
lean_ctor_set_uint8(x_310, sizeof(void*)*1, x_309);
x_311 = l_Lake_OutStream_logEntry(x_308, x_310, x_306, x_307, x_304);
lean_dec(x_310);
x_312 = !lean_is_exclusive(x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_311, 0);
lean_dec(x_313);
x_314 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_311, 1);
lean_ctor_set(x_311, 0, x_314);
return x_311;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_311, 1);
lean_inc(x_315);
lean_dec(x_311);
x_316 = l_Lake_setupFile___boxed__const__1;
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
}
}
else
{
lean_object* x_318; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_318 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_318);
return x_27;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_319 = lean_ctor_get(x_27, 0);
x_320 = lean_ctor_get(x_27, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_27);
x_321 = lean_string_utf8_byte_size(x_319);
x_322 = lean_unsigned_to_nat(0u);
x_323 = lean_nat_dec_eq(x_321, x_322);
lean_dec(x_321);
if (x_323 == 0)
{
uint8_t x_324; 
x_324 = lean_string_dec_eq(x_319, x_23);
lean_dec(x_319);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_25);
x_325 = l_Lake_invalidConfigEnvVar___closed__0;
x_326 = lean_io_getenv(x_325, x_320);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; uint8_t x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = lean_box(1);
x_330 = l_Lake_OutStream_get(x_329, x_328);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_334 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
lean_inc(x_331);
x_335 = l_Lake_AnsiMode_isEnabled(x_331, x_334, x_332);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = lean_box(x_333);
x_339 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_339, 0, x_331);
lean_closure_set(x_339, 1, x_338);
lean_closure_set(x_339, 2, x_336);
x_340 = l_Lake_loadWorkspace(x_1, x_339, x_337);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_387; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
lean_inc(x_23);
x_387 = l_Lake_Workspace_findModuleBySrc_x3f(x_23, x_341);
if (lean_obj_tag(x_387) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_388; 
x_388 = l_IO_FS_readFile(x_23, x_342);
lean_dec(x_23);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
lean_inc(x_2);
x_391 = l_Lean_parseImports_x27(x_389, x_2, x_390);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_343 = x_392;
x_344 = x_393;
goto block_386;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; uint8_t x_398; uint8_t x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_341);
lean_dec(x_4);
lean_dec(x_2);
x_394 = lean_ctor_get(x_391, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_391, 1);
lean_inc(x_395);
lean_dec(x_391);
x_396 = lean_io_error_to_string(x_394);
x_397 = 1;
x_398 = 0;
x_399 = 3;
x_400 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_400, 0, x_396);
lean_ctor_set_uint8(x_400, sizeof(void*)*1, x_399);
x_401 = l_Lake_OutStream_logEntry(x_329, x_400, x_397, x_398, x_395);
lean_dec(x_400);
x_402 = lean_ctor_get(x_401, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_403 = x_401;
} else {
 lean_dec_ref(x_401);
 x_403 = lean_box(0);
}
x_404 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_403)) {
 x_405 = lean_alloc_ctor(1, 2, 0);
} else {
 x_405 = x_403;
 lean_ctor_set_tag(x_405, 1);
}
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_402);
return x_405;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; uint8_t x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_341);
lean_dec(x_4);
lean_dec(x_2);
x_406 = lean_ctor_get(x_388, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_388, 1);
lean_inc(x_407);
lean_dec(x_388);
x_408 = lean_io_error_to_string(x_406);
x_409 = 1;
x_410 = 0;
x_411 = 3;
x_412 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_412, 0, x_408);
lean_ctor_set_uint8(x_412, sizeof(void*)*1, x_411);
x_413 = l_Lake_OutStream_logEntry(x_329, x_412, x_409, x_410, x_407);
lean_dec(x_412);
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_415 = x_413;
} else {
 lean_dec_ref(x_413);
 x_415 = lean_box(0);
}
x_416 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_415)) {
 x_417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_417 = x_415;
 lean_ctor_set_tag(x_417, 1);
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_414);
return x_417;
}
}
else
{
lean_object* x_418; 
lean_dec(x_23);
x_418 = lean_ctor_get(x_3, 0);
lean_inc(x_418);
lean_dec(x_3);
x_343 = x_418;
x_344 = x_342;
goto block_386;
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_2);
x_419 = lean_ctor_get(x_387, 0);
lean_inc(x_419);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 x_420 = x_387;
} else {
 lean_dec_ref(x_387);
 x_420 = lean_box(0);
}
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_419, 2);
lean_inc(x_422);
x_423 = lean_box(x_324);
x_424 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_424, 0, x_423);
x_425 = 1;
x_426 = l_Lean_Name_toString(x_421, x_425, x_424);
x_427 = l_Lake_setupFile___closed__0;
x_428 = lean_string_append(x_426, x_427);
x_429 = l_Lake_Module_setupFacet;
if (lean_is_scalar(x_420)) {
 x_430 = lean_alloc_ctor(0, 1, 0);
} else {
 x_430 = x_420;
 lean_ctor_set_tag(x_430, 0);
}
lean_ctor_set(x_430, 0, x_422);
x_431 = l_Lake_Module_keyword;
x_432 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
lean_ctor_set(x_432, 2, x_419);
lean_ctor_set(x_432, 3, x_429);
x_433 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 8, 1);
lean_closure_set(x_433, 0, x_432);
x_434 = lean_box(x_324);
x_435 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 10, 3);
lean_closure_set(x_435, 0, x_433);
lean_closure_set(x_435, 1, x_428);
lean_closure_set(x_435, 2, x_434);
x_436 = l_Lake_Workspace_runFetchM___redArg(x_341, x_435, x_4, x_342);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
x_439 = lean_ctor_get(x_437, 0);
lean_inc(x_439);
lean_dec(x_437);
x_440 = lean_io_wait(x_439, x_438);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_443 = lean_ctor_get(x_441, 0);
lean_inc(x_443);
lean_dec(x_441);
x_444 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_443);
x_445 = l_Lean_Json_compress(x_444);
x_446 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_445, x_442);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 x_449 = x_446;
} else {
 lean_dec_ref(x_446);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_450 = x_449;
}
lean_ctor_set(x_450, 0, x_447);
lean_ctor_set(x_450, 1, x_448);
return x_450;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; uint8_t x_455; uint8_t x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_451 = lean_ctor_get(x_446, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_446, 1);
lean_inc(x_452);
lean_dec(x_446);
x_453 = lean_io_error_to_string(x_451);
x_454 = 1;
x_455 = 0;
x_456 = 3;
x_457 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_457, 0, x_453);
lean_ctor_set_uint8(x_457, sizeof(void*)*1, x_456);
x_458 = l_Lake_OutStream_logEntry(x_329, x_457, x_454, x_455, x_452);
lean_dec(x_457);
x_459 = lean_ctor_get(x_458, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_460 = x_458;
} else {
 lean_dec_ref(x_458);
 x_460 = lean_box(0);
}
x_461 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_460)) {
 x_462 = lean_alloc_ctor(1, 2, 0);
} else {
 x_462 = x_460;
 lean_ctor_set_tag(x_462, 1);
}
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_459);
return x_462;
}
}
else
{
lean_object* x_463; lean_object* x_464; 
lean_dec(x_441);
x_463 = lean_ctor_get(x_440, 1);
lean_inc(x_463);
lean_dec(x_440);
x_464 = l_Lake_mkModuleSetup___closed__3;
x_6 = x_464;
x_7 = x_463;
goto block_21;
}
}
else
{
lean_object* x_465; lean_object* x_466; 
x_465 = lean_ctor_get(x_436, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_436, 1);
lean_inc(x_466);
lean_dec(x_436);
x_6 = x_465;
x_7 = x_466;
goto block_21;
}
}
block_386:
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_345 = lean_ctor_get(x_341, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_345, 3);
lean_inc(x_346);
lean_dec(x_345);
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
lean_dec(x_346);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 4);
lean_inc(x_349);
lean_dec(x_347);
x_350 = l_Lean_LeanOptions_ofArray(x_348);
lean_dec(x_348);
x_351 = l_Lean_LeanOptions_appendArray(x_350, x_349);
lean_dec(x_349);
x_352 = l_Lake_mkModuleSetup(x_341, x_2, x_343, x_351, x_4, x_344);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_353);
x_356 = l_Lean_Json_compress(x_355);
x_357 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_356, x_354);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_360 = x_357;
} else {
 lean_dec_ref(x_357);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; uint8_t x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_362 = lean_ctor_get(x_357, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_357, 1);
lean_inc(x_363);
lean_dec(x_357);
x_364 = lean_io_error_to_string(x_362);
x_365 = 1;
x_366 = 0;
x_367 = 3;
x_368 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_368, 0, x_364);
lean_ctor_set_uint8(x_368, sizeof(void*)*1, x_367);
x_369 = l_Lake_OutStream_logEntry(x_329, x_368, x_365, x_366, x_363);
lean_dec(x_368);
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_371 = x_369;
} else {
 lean_dec_ref(x_369);
 x_371 = lean_box(0);
}
x_372 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 2, 0);
} else {
 x_373 = x_371;
 lean_ctor_set_tag(x_373, 1);
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_370);
return x_373;
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; uint8_t x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_374 = lean_ctor_get(x_352, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_352, 1);
lean_inc(x_375);
lean_dec(x_352);
x_376 = lean_io_error_to_string(x_374);
x_377 = 1;
x_378 = 0;
x_379 = 3;
x_380 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_380, 0, x_376);
lean_ctor_set_uint8(x_380, sizeof(void*)*1, x_379);
x_381 = l_Lake_OutStream_logEntry(x_329, x_380, x_377, x_378, x_375);
lean_dec(x_380);
x_382 = lean_ctor_get(x_381, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_383 = x_381;
} else {
 lean_dec_ref(x_381);
 x_383 = lean_box(0);
}
x_384 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_385 = x_383;
 lean_ctor_set_tag(x_385, 1);
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_382);
return x_385;
}
}
}
else
{
lean_object* x_467; uint8_t x_468; uint8_t x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_467 = lean_ctor_get(x_340, 1);
lean_inc(x_467);
lean_dec(x_340);
x_468 = 1;
x_469 = 0;
x_470 = l_Lake_setupFile___closed__2;
x_471 = l_Lake_OutStream_logEntry(x_329, x_470, x_468, x_469, x_467);
x_472 = lean_ctor_get(x_471, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 x_473 = x_471;
} else {
 lean_dec_ref(x_471);
 x_473 = lean_box(0);
}
x_474 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_473)) {
 x_475 = lean_alloc_ctor(1, 2, 0);
} else {
 x_475 = x_473;
 lean_ctor_set_tag(x_475, 1);
}
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_472);
return x_475;
}
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_476 = lean_ctor_get(x_326, 1);
lean_inc(x_476);
lean_dec(x_326);
x_477 = lean_ctor_get(x_327, 0);
lean_inc(x_477);
lean_dec(x_327);
x_478 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_477, x_476);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_478, 1);
lean_inc(x_479);
lean_dec(x_478);
x_480 = l_Lake_setupFile___closed__3;
x_481 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_480, x_479);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_483 = x_481;
} else {
 lean_dec_ref(x_481);
 x_483 = lean_box(0);
}
x_484 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_483)) {
 x_485 = lean_alloc_ctor(1, 2, 0);
} else {
 x_485 = x_483;
 lean_ctor_set_tag(x_485, 1);
}
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_482);
return x_485;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; uint8_t x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_486 = lean_ctor_get(x_481, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_481, 1);
lean_inc(x_487);
lean_dec(x_481);
x_488 = lean_io_error_to_string(x_486);
x_489 = 1;
x_490 = 0;
x_491 = lean_box(1);
x_492 = 3;
x_493 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_493, 0, x_488);
lean_ctor_set_uint8(x_493, sizeof(void*)*1, x_492);
x_494 = l_Lake_OutStream_logEntry(x_491, x_493, x_489, x_490, x_487);
lean_dec(x_493);
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_496 = x_494;
} else {
 lean_dec_ref(x_494);
 x_496 = lean_box(0);
}
x_497 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_496)) {
 x_498 = lean_alloc_ctor(1, 2, 0);
} else {
 x_498 = x_496;
 lean_ctor_set_tag(x_498, 1);
}
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_495);
return x_498;
}
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; uint8_t x_503; lean_object* x_504; uint8_t x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_499 = lean_ctor_get(x_478, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_478, 1);
lean_inc(x_500);
lean_dec(x_478);
x_501 = lean_io_error_to_string(x_499);
x_502 = 1;
x_503 = 0;
x_504 = lean_box(1);
x_505 = 3;
x_506 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_506, 0, x_501);
lean_ctor_set_uint8(x_506, sizeof(void*)*1, x_505);
x_507 = l_Lake_OutStream_logEntry(x_504, x_506, x_502, x_503, x_500);
lean_dec(x_506);
x_508 = lean_ctor_get(x_507, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 lean_ctor_release(x_507, 1);
 x_509 = x_507;
} else {
 lean_dec_ref(x_507);
 x_509 = lean_box(0);
}
x_510 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_509)) {
 x_511 = lean_alloc_ctor(1, 2, 0);
} else {
 x_511 = x_509;
 lean_ctor_set_tag(x_511, 1);
}
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_508);
return x_511;
}
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_512 = lean_ctor_get(x_25, 0);
lean_inc(x_512);
lean_dec(x_25);
x_513 = lean_ctor_get(x_512, 4);
lean_inc(x_513);
lean_dec(x_512);
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
lean_dec(x_513);
x_515 = l_Lake_configModuleName;
x_516 = lean_box(0);
x_517 = lean_box(0);
x_518 = l_Lake_setupFile___closed__4;
x_519 = l_Lake_setupFile___closed__5;
x_520 = lean_array_push(x_519, x_514);
x_521 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_521, 0, x_515);
lean_ctor_set(x_521, 1, x_516);
lean_ctor_set(x_521, 2, x_517);
lean_ctor_set(x_521, 3, x_518);
lean_ctor_set(x_521, 4, x_520);
lean_ctor_set(x_521, 5, x_517);
lean_ctor_set_uint8(x_521, sizeof(void*)*6, x_323);
x_522 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2010_(x_521);
x_523 = l_Lean_Json_compress(x_522);
x_524 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_523, x_320);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_527 = x_524;
} else {
 lean_dec_ref(x_524);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_525);
lean_ctor_set(x_528, 1, x_526);
return x_528;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; uint8_t x_533; lean_object* x_534; uint8_t x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_529 = lean_ctor_get(x_524, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_524, 1);
lean_inc(x_530);
lean_dec(x_524);
x_531 = lean_io_error_to_string(x_529);
x_532 = 1;
x_533 = 0;
x_534 = lean_box(1);
x_535 = 3;
x_536 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_536, 0, x_531);
lean_ctor_set_uint8(x_536, sizeof(void*)*1, x_535);
x_537 = l_Lake_OutStream_logEntry(x_534, x_536, x_532, x_533, x_530);
lean_dec(x_536);
x_538 = lean_ctor_get(x_537, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 lean_ctor_release(x_537, 1);
 x_539 = x_537;
} else {
 lean_dec_ref(x_537);
 x_539 = lean_box(0);
}
x_540 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_539)) {
 x_541 = lean_alloc_ctor(1, 2, 0);
} else {
 x_541 = x_539;
 lean_ctor_set_tag(x_541, 1);
}
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_538);
return x_541;
}
}
}
else
{
lean_object* x_542; lean_object* x_543; 
lean_dec(x_319);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_542 = l_Lake_setupFile___boxed__const__2;
x_543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_320);
return x_543;
}
}
block_21:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_io_error_to_string(x_6);
x_9 = 1;
x_10 = 0;
x_11 = lean_box(1);
x_12 = 3;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = l_Lake_OutStream_logEntry(x_11, x_13, x_9, x_10, x_7);
lean_dec(x_13);
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
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Lake_loadWorkspace), 3, 1);
lean_closure_set(x_27, 0, x_1);
x_28 = l_Lake_LoggerIO_captureLog___redArg(x_27, x_3);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_33 = x_29;
} else {
 lean_dec_ref(x_29);
 x_33 = lean_box(0);
}
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_array_get_size(x_32);
x_58 = lean_nat_dec_lt(x_56, x_57);
if (x_58 == 0)
{
lean_dec(x_57);
x_34 = x_30;
goto block_55;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_57, x_57);
if (x_59 == 0)
{
lean_dec(x_57);
x_34 = x_30;
goto block_55;
}
else
{
uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; 
x_60 = 1;
x_61 = 0;
x_62 = lean_box(1);
x_63 = lean_box(0);
x_64 = 0;
x_65 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_66 = l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(x_62, x_60, x_61, x_32, x_64, x_65, x_63, x_30);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_34 = x_67;
goto block_55;
}
}
block_26:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
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
x_15 = 1;
x_16 = 0;
x_17 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_4);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_16);
x_18 = lean_io_process_spawn(x_17, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_io_process_child_wait(x_10, x_19, x_20);
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
block_55:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lake_serve___closed__3;
x_36 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_35, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = l_Lake_Env_baseVars(x_38);
x_40 = l_Lake_invalidConfigEnvVar___closed__0;
x_41 = l_Lake_Log_toString(x_32);
lean_dec(x_32);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
if (lean_is_scalar(x_33)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_33;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_array_push(x_39, x_43);
x_45 = l_Lake_setupFile___closed__4;
x_4 = x_44;
x_5 = x_45;
x_6 = x_37;
goto block_26;
}
else
{
uint8_t x_46; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_36);
if (x_46 == 0)
{
return x_36;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_36, 0);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_36);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_33);
lean_dec(x_32);
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
lean_dec(x_31);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 4);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lake_Workspace_augmentedEnvVars(x_50);
x_4 = x_54;
x_5 = x_53;
x_6 = x_34;
goto block_26;
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
