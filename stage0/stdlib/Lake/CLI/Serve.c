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
lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(lean_object*);
lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instOrdBuildType;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
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
uint8_t l_Ord_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_299 = lean_ctor_get(x_1, 6);
lean_inc(x_299);
x_300 = l_Lake_realConfigFile(x_299, x_25);
x_301 = !lean_is_exclusive(x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_302 = lean_ctor_get(x_300, 0);
x_303 = lean_ctor_get(x_300, 1);
x_304 = lean_string_utf8_byte_size(x_302);
x_305 = lean_unsigned_to_nat(0u);
x_306 = lean_nat_dec_eq(x_304, x_305);
lean_dec(x_304);
if (x_306 == 0)
{
uint8_t x_307; 
lean_free_object(x_300);
x_307 = lean_string_dec_eq(x_302, x_24);
lean_dec(x_302);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_free_object(x_22);
x_308 = l_Lake_invalidConfigEnvVar;
x_309 = lean_io_getenv(x_308, x_303);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; uint8_t x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_312 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_313 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
x_314 = lean_box(1);
x_315 = l_Lake_OutStream_get(x_314, x_311);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
lean_inc(x_316);
x_318 = l_Lake_AnsiMode_isEnabled(x_316, x_313, x_317);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_321 = lean_box(x_312);
x_322 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__2___boxed), 5, 3);
lean_closure_set(x_322, 0, x_316);
lean_closure_set(x_322, 1, x_321);
lean_closure_set(x_322, 2, x_319);
x_323 = l_Lake_loadWorkspace(x_1, x_322, x_320);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_324);
x_26 = x_326;
x_27 = x_325;
goto block_298;
}
else
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
lean_dec(x_323);
x_328 = lean_box(0);
x_26 = x_328;
x_27 = x_327;
goto block_298;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_329 = lean_ctor_get(x_309, 1);
lean_inc(x_329);
lean_dec(x_309);
x_330 = lean_ctor_get(x_310, 0);
lean_inc(x_330);
lean_dec(x_310);
x_331 = l_IO_eprint___at_IO_eprintln___spec__1(x_330, x_329);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
lean_dec(x_331);
x_333 = l_Lake_setupFile___closed__9;
x_334 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_333, x_332);
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
lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; uint8_t x_348; lean_object* x_349; uint8_t x_350; 
x_341 = lean_ctor_get(x_334, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_334, 1);
lean_inc(x_342);
lean_dec(x_334);
x_343 = lean_io_error_to_string(x_341);
x_344 = 3;
x_345 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set_uint8(x_345, sizeof(void*)*1, x_344);
x_346 = lean_box(1);
x_347 = 1;
x_348 = 0;
x_349 = l_Lake_OutStream_logEntry(x_346, x_345, x_347, x_348, x_342);
lean_dec(x_345);
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_349, 0);
lean_dec(x_351);
x_352 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_349, 1);
lean_ctor_set(x_349, 0, x_352);
return x_349;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_349, 1);
lean_inc(x_353);
lean_dec(x_349);
x_354 = l_Lake_setupFile___boxed__const__1;
x_355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_353);
return x_355;
}
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; uint8_t x_363; lean_object* x_364; uint8_t x_365; 
x_356 = lean_ctor_get(x_331, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_331, 1);
lean_inc(x_357);
lean_dec(x_331);
x_358 = lean_io_error_to_string(x_356);
x_359 = 3;
x_360 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set_uint8(x_360, sizeof(void*)*1, x_359);
x_361 = lean_box(1);
x_362 = 1;
x_363 = 0;
x_364 = l_Lake_OutStream_logEntry(x_361, x_360, x_362, x_363, x_357);
lean_dec(x_360);
x_365 = !lean_is_exclusive(x_364);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_364, 0);
lean_dec(x_366);
x_367 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_364, 1);
lean_ctor_set(x_364, 0, x_367);
return x_364;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_364, 1);
lean_inc(x_368);
lean_dec(x_364);
x_369 = l_Lake_setupFile___boxed__const__1;
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
}
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
x_371 = lean_ctor_get(x_1, 0);
lean_inc(x_371);
lean_dec(x_1);
x_372 = l_Lake_Env_leanPath(x_371);
x_373 = l_Lake_Env_leanSrcPath(x_371);
x_374 = lean_box(0);
x_375 = lean_ctor_get(x_371, 0);
lean_inc(x_375);
lean_dec(x_371);
x_376 = lean_ctor_get(x_375, 4);
lean_inc(x_376);
lean_dec(x_375);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
lean_dec(x_376);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 1, x_374);
lean_ctor_set(x_22, 0, x_377);
x_378 = lean_array_mk(x_22);
x_379 = l_Lake_setupFile___closed__3;
x_380 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_380, 0, x_372);
lean_ctor_set(x_380, 1, x_373);
lean_ctor_set(x_380, 2, x_379);
lean_ctor_set(x_380, 3, x_378);
x_381 = lean_box(0);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
x_383 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_382);
x_384 = l_Lean_Json_compress(x_383);
x_385 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_384, x_303);
if (lean_obj_tag(x_385) == 0)
{
uint8_t x_386; 
x_386 = !lean_is_exclusive(x_385);
if (x_386 == 0)
{
return x_385;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_385, 0);
x_388 = lean_ctor_get(x_385, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_385);
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; uint8_t x_397; lean_object* x_398; uint8_t x_399; 
x_390 = lean_ctor_get(x_385, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_385, 1);
lean_inc(x_391);
lean_dec(x_385);
x_392 = lean_io_error_to_string(x_390);
x_393 = 3;
x_394 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*1, x_393);
x_395 = lean_box(1);
x_396 = 1;
x_397 = 0;
x_398 = l_Lake_OutStream_logEntry(x_395, x_394, x_396, x_397, x_391);
lean_dec(x_394);
x_399 = !lean_is_exclusive(x_398);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; 
x_400 = lean_ctor_get(x_398, 0);
lean_dec(x_400);
x_401 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_398, 1);
lean_ctor_set(x_398, 0, x_401);
return x_398;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_398, 1);
lean_inc(x_402);
lean_dec(x_398);
x_403 = l_Lake_setupFile___boxed__const__1;
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_402);
return x_404;
}
}
}
}
else
{
lean_object* x_405; 
lean_dec(x_302);
lean_free_object(x_22);
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_405 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_300, 1);
lean_ctor_set(x_300, 0, x_405);
return x_300;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; 
x_406 = lean_ctor_get(x_300, 0);
x_407 = lean_ctor_get(x_300, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_300);
x_408 = lean_string_utf8_byte_size(x_406);
x_409 = lean_unsigned_to_nat(0u);
x_410 = lean_nat_dec_eq(x_408, x_409);
lean_dec(x_408);
if (x_410 == 0)
{
uint8_t x_411; 
x_411 = lean_string_dec_eq(x_406, x_24);
lean_dec(x_406);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_free_object(x_22);
x_412 = l_Lake_invalidConfigEnvVar;
x_413 = lean_io_getenv(x_412, x_407);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; uint8_t x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_417 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
x_418 = lean_box(1);
x_419 = l_Lake_OutStream_get(x_418, x_415);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
lean_inc(x_420);
x_422 = l_Lake_AnsiMode_isEnabled(x_420, x_417, x_421);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
x_425 = lean_box(x_416);
x_426 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__2___boxed), 5, 3);
lean_closure_set(x_426, 0, x_420);
lean_closure_set(x_426, 1, x_425);
lean_closure_set(x_426, 2, x_423);
x_427 = l_Lake_loadWorkspace(x_1, x_426, x_424);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_430, 0, x_428);
x_26 = x_430;
x_27 = x_429;
goto block_298;
}
else
{
lean_object* x_431; lean_object* x_432; 
x_431 = lean_ctor_get(x_427, 1);
lean_inc(x_431);
lean_dec(x_427);
x_432 = lean_box(0);
x_26 = x_432;
x_27 = x_431;
goto block_298;
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_433 = lean_ctor_get(x_413, 1);
lean_inc(x_433);
lean_dec(x_413);
x_434 = lean_ctor_get(x_414, 0);
lean_inc(x_434);
lean_dec(x_414);
x_435 = l_IO_eprint___at_IO_eprintln___spec__1(x_434, x_433);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
lean_dec(x_435);
x_437 = l_Lake_setupFile___closed__9;
x_438 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_437, x_436);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_439 = lean_ctor_get(x_438, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_440 = x_438;
} else {
 lean_dec_ref(x_438);
 x_440 = lean_box(0);
}
x_441 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_440)) {
 x_442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_442 = x_440;
 lean_ctor_set_tag(x_442, 1);
}
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_439);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_443 = lean_ctor_get(x_438, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_438, 1);
lean_inc(x_444);
lean_dec(x_438);
x_445 = lean_io_error_to_string(x_443);
x_446 = 3;
x_447 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set_uint8(x_447, sizeof(void*)*1, x_446);
x_448 = lean_box(1);
x_449 = 1;
x_450 = 0;
x_451 = l_Lake_OutStream_logEntry(x_448, x_447, x_449, x_450, x_444);
lean_dec(x_447);
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
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; uint8_t x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_456 = lean_ctor_get(x_435, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_435, 1);
lean_inc(x_457);
lean_dec(x_435);
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
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
x_469 = lean_ctor_get(x_1, 0);
lean_inc(x_469);
lean_dec(x_1);
x_470 = l_Lake_Env_leanPath(x_469);
x_471 = l_Lake_Env_leanSrcPath(x_469);
x_472 = lean_box(0);
x_473 = lean_ctor_get(x_469, 0);
lean_inc(x_473);
lean_dec(x_469);
x_474 = lean_ctor_get(x_473, 4);
lean_inc(x_474);
lean_dec(x_473);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
lean_dec(x_474);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 1, x_472);
lean_ctor_set(x_22, 0, x_475);
x_476 = lean_array_mk(x_22);
x_477 = l_Lake_setupFile___closed__3;
x_478 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_478, 0, x_470);
lean_ctor_set(x_478, 1, x_471);
lean_ctor_set(x_478, 2, x_477);
lean_ctor_set(x_478, 3, x_476);
x_479 = lean_box(0);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_478);
lean_ctor_set(x_480, 1, x_479);
x_481 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_480);
x_482 = l_Lean_Json_compress(x_481);
x_483 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_482, x_407);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_483, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_486 = x_483;
} else {
 lean_dec_ref(x_483);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(0, 2, 0);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_485);
return x_487;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; uint8_t x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_488 = lean_ctor_get(x_483, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_483, 1);
lean_inc(x_489);
lean_dec(x_483);
x_490 = lean_io_error_to_string(x_488);
x_491 = 3;
x_492 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set_uint8(x_492, sizeof(void*)*1, x_491);
x_493 = lean_box(1);
x_494 = 1;
x_495 = 0;
x_496 = l_Lake_OutStream_logEntry(x_493, x_492, x_494, x_495, x_489);
lean_dec(x_492);
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_498 = x_496;
} else {
 lean_dec_ref(x_496);
 x_498 = lean_box(0);
}
x_499 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_498)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_498;
 lean_ctor_set_tag(x_500, 1);
}
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_497);
return x_500;
}
}
}
else
{
lean_object* x_501; lean_object* x_502; 
lean_dec(x_406);
lean_free_object(x_22);
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_501 = l_Lake_setupFile___boxed__const__2;
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_407);
return x_502;
}
}
block_298:
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
x_56 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_49);
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
x_82 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_81);
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
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
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
x_142 = l_Lake_instOrdBuildType;
x_143 = lean_box(x_138);
x_144 = lean_box(x_141);
x_145 = l_Ord_instDecidableRelLe___rarg(x_142, x_143, x_144);
x_146 = lean_ctor_get(x_137, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_137, 4);
lean_inc(x_147);
lean_dec(x_137);
x_148 = l_Array_append___rarg(x_146, x_147);
lean_dec(x_147);
x_149 = lean_ctor_get(x_140, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_140, 4);
lean_inc(x_150);
lean_dec(x_140);
x_151 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_39, x_131);
lean_dec(x_39);
if (x_145 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_177 = l_Lake_BuildType_leanOptions(x_141);
x_178 = l_Array_append___rarg(x_177, x_148);
lean_dec(x_148);
x_179 = l_Array_append___rarg(x_178, x_149);
lean_dec(x_149);
x_180 = l_Array_append___rarg(x_179, x_150);
lean_dec(x_150);
x_181 = lean_array_get_size(x_180);
x_182 = lean_unsigned_to_nat(0u);
x_183 = lean_nat_dec_lt(x_182, x_181);
if (x_183 == 0)
{
lean_dec(x_181);
lean_dec(x_180);
x_152 = x_133;
goto block_176;
}
else
{
uint8_t x_184; 
x_184 = lean_nat_dec_le(x_181, x_181);
if (x_184 == 0)
{
lean_dec(x_181);
lean_dec(x_180);
x_152 = x_133;
goto block_176;
}
else
{
size_t x_185; size_t x_186; lean_object* x_187; 
x_185 = 0;
x_186 = lean_usize_of_nat(x_181);
lean_dec(x_181);
x_187 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(x_180, x_185, x_186, x_133);
lean_dec(x_180);
x_152 = x_187;
goto block_176;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_188 = l_Lake_BuildType_leanOptions(x_138);
x_189 = l_Array_append___rarg(x_188, x_148);
lean_dec(x_148);
x_190 = l_Array_append___rarg(x_189, x_149);
lean_dec(x_149);
x_191 = l_Array_append___rarg(x_190, x_150);
lean_dec(x_150);
x_192 = lean_array_get_size(x_191);
x_193 = lean_unsigned_to_nat(0u);
x_194 = lean_nat_dec_lt(x_193, x_192);
if (x_194 == 0)
{
lean_dec(x_192);
lean_dec(x_191);
x_152 = x_133;
goto block_176;
}
else
{
uint8_t x_195; 
x_195 = lean_nat_dec_le(x_192, x_192);
if (x_195 == 0)
{
lean_dec(x_192);
lean_dec(x_191);
x_152 = x_133;
goto block_176;
}
else
{
size_t x_196; size_t x_197; lean_object* x_198; 
x_196 = 0;
x_197 = lean_usize_of_nat(x_192);
lean_dec(x_192);
x_198 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(x_191, x_196, x_197, x_133);
lean_dec(x_191);
x_152 = x_198;
goto block_176;
}
}
}
block_176:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
if (lean_is_scalar(x_132)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_132;
}
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_153);
x_155 = l_Lean_Json_compress(x_154);
x_156 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_155, x_130);
if (lean_obj_tag(x_156) == 0)
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
return x_156;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_156);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_168; lean_object* x_169; uint8_t x_170; 
x_161 = lean_ctor_get(x_156, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_156, 1);
lean_inc(x_162);
lean_dec(x_156);
x_163 = lean_io_error_to_string(x_161);
x_164 = 3;
x_165 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set_uint8(x_165, sizeof(void*)*1, x_164);
x_166 = lean_box(1);
x_167 = 1;
x_168 = 0;
x_169 = l_Lake_OutStream_logEntry(x_166, x_165, x_167, x_168, x_162);
lean_dec(x_165);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_169, 0);
lean_dec(x_171);
x_172 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_169, 1);
lean_ctor_set(x_169, 0, x_172);
return x_169;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
lean_dec(x_169);
x_174 = l_Lake_setupFile___boxed__const__1;
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_129);
lean_dec(x_107);
lean_dec(x_39);
x_199 = lean_ctor_get(x_128, 1);
lean_inc(x_199);
lean_dec(x_128);
x_200 = l_Lake_setupFile___closed__5;
x_6 = x_200;
x_7 = x_199;
goto block_21;
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_107);
lean_dec(x_39);
x_201 = lean_ctor_get(x_124, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_124, 1);
lean_inc(x_202);
lean_dec(x_124);
x_6 = x_201;
x_7 = x_202;
goto block_21;
}
}
else
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_203 = lean_ctor_get(x_40, 0);
lean_inc(x_203);
lean_dec(x_40);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
x_205 = 1;
x_206 = l_Lake_setupFile___closed__6;
x_207 = l_Lean_Name_toString(x_204, x_205, x_206);
x_208 = l_Lake_setupFile___closed__7;
x_209 = lean_string_append(x_208, x_207);
lean_dec(x_207);
x_210 = l_Lake_setupFile___closed__8;
x_211 = lean_string_append(x_209, x_210);
x_212 = lean_ctor_get(x_203, 2);
lean_inc(x_212);
x_213 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = l_Lake_Module_keyword;
x_215 = l_Lake_Module_depsFacet;
lean_inc(x_203);
x_216 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
lean_ctor_set(x_216, 2, x_203);
lean_ctor_set(x_216, 3, x_215);
x_217 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_217, 0, x_216);
lean_closure_set(x_217, 1, lean_box(0));
x_218 = 0;
x_219 = lean_box(x_218);
x_220 = lean_alloc_closure((void*)(l_Lake_withRegisterJob___at_Lake_setupFile___spec__2___boxed), 9, 3);
lean_closure_set(x_220, 0, x_211);
lean_closure_set(x_220, 1, x_217);
lean_closure_set(x_220, 2, x_219);
lean_inc(x_39);
x_221 = l_Lake_Workspace_runFetchM___rarg(x_39, x_220, x_4, x_27);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_io_wait(x_224, x_223);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_229 = x_226;
} else {
 lean_dec_ref(x_226);
 x_229 = lean_box(0);
}
x_230 = lean_box(0);
x_231 = lean_ctor_get(x_203, 0);
lean_inc(x_231);
lean_dec(x_203);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_232, 3);
lean_inc(x_233);
lean_dec(x_232);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_235 = lean_ctor_get_uint8(x_234, sizeof(void*)*13);
x_236 = lean_ctor_get(x_231, 2);
lean_inc(x_236);
lean_dec(x_231);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_ctor_get_uint8(x_237, sizeof(void*)*13);
x_239 = l_Lake_instOrdBuildType;
x_240 = lean_box(x_235);
x_241 = lean_box(x_238);
x_242 = l_Ord_instDecidableRelLe___rarg(x_239, x_240, x_241);
x_243 = lean_ctor_get(x_234, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_234, 4);
lean_inc(x_244);
lean_dec(x_234);
x_245 = l_Array_append___rarg(x_243, x_244);
lean_dec(x_244);
x_246 = lean_ctor_get(x_237, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_237, 4);
lean_inc(x_247);
lean_dec(x_237);
x_248 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_39, x_228);
lean_dec(x_39);
if (x_242 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_272 = l_Lake_BuildType_leanOptions(x_238);
x_273 = l_Array_append___rarg(x_272, x_245);
lean_dec(x_245);
x_274 = l_Array_append___rarg(x_273, x_246);
lean_dec(x_246);
x_275 = l_Array_append___rarg(x_274, x_247);
lean_dec(x_247);
x_276 = lean_array_get_size(x_275);
x_277 = lean_unsigned_to_nat(0u);
x_278 = lean_nat_dec_lt(x_277, x_276);
if (x_278 == 0)
{
lean_dec(x_276);
lean_dec(x_275);
x_249 = x_230;
goto block_271;
}
else
{
uint8_t x_279; 
x_279 = lean_nat_dec_le(x_276, x_276);
if (x_279 == 0)
{
lean_dec(x_276);
lean_dec(x_275);
x_249 = x_230;
goto block_271;
}
else
{
size_t x_280; size_t x_281; lean_object* x_282; 
x_280 = 0;
x_281 = lean_usize_of_nat(x_276);
lean_dec(x_276);
x_282 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(x_275, x_280, x_281, x_230);
lean_dec(x_275);
x_249 = x_282;
goto block_271;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_283 = l_Lake_BuildType_leanOptions(x_235);
x_284 = l_Array_append___rarg(x_283, x_245);
lean_dec(x_245);
x_285 = l_Array_append___rarg(x_284, x_246);
lean_dec(x_246);
x_286 = l_Array_append___rarg(x_285, x_247);
lean_dec(x_247);
x_287 = lean_array_get_size(x_286);
x_288 = lean_unsigned_to_nat(0u);
x_289 = lean_nat_dec_lt(x_288, x_287);
if (x_289 == 0)
{
lean_dec(x_287);
lean_dec(x_286);
x_249 = x_230;
goto block_271;
}
else
{
uint8_t x_290; 
x_290 = lean_nat_dec_le(x_287, x_287);
if (x_290 == 0)
{
lean_dec(x_287);
lean_dec(x_286);
x_249 = x_230;
goto block_271;
}
else
{
size_t x_291; size_t x_292; lean_object* x_293; 
x_291 = 0;
x_292 = lean_usize_of_nat(x_287);
lean_dec(x_287);
x_293 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(x_286, x_291, x_292, x_230);
lean_dec(x_286);
x_249 = x_293;
goto block_271;
}
}
}
block_271:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
if (lean_is_scalar(x_229)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_229;
}
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_250);
x_252 = l_Lean_Json_compress(x_251);
x_253 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_252, x_227);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_256 = x_253;
} else {
 lean_dec_ref(x_253);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_258 = lean_ctor_get(x_253, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_253, 1);
lean_inc(x_259);
lean_dec(x_253);
x_260 = lean_io_error_to_string(x_258);
x_261 = 3;
x_262 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set_uint8(x_262, sizeof(void*)*1, x_261);
x_263 = lean_box(1);
x_264 = 1;
x_265 = 0;
x_266 = l_Lake_OutStream_logEntry(x_263, x_262, x_264, x_265, x_259);
lean_dec(x_262);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_268 = x_266;
} else {
 lean_dec_ref(x_266);
 x_268 = lean_box(0);
}
x_269 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_268)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_268;
 lean_ctor_set_tag(x_270, 1);
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_267);
return x_270;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_226);
lean_dec(x_203);
lean_dec(x_39);
x_294 = lean_ctor_get(x_225, 1);
lean_inc(x_294);
lean_dec(x_225);
x_295 = l_Lake_setupFile___closed__5;
x_6 = x_295;
x_7 = x_294;
goto block_21;
}
}
else
{
lean_object* x_296; lean_object* x_297; 
lean_dec(x_203);
lean_dec(x_39);
x_296 = lean_ctor_get(x_221, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_221, 1);
lean_inc(x_297);
lean_dec(x_221);
x_6 = x_296;
x_7 = x_297;
goto block_21;
}
}
}
}
}
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; uint8_t x_661; 
x_503 = lean_ctor_get(x_22, 0);
x_504 = lean_ctor_get(x_22, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_22);
x_654 = lean_ctor_get(x_1, 6);
lean_inc(x_654);
x_655 = l_Lake_realConfigFile(x_654, x_504);
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_658 = x_655;
} else {
 lean_dec_ref(x_655);
 x_658 = lean_box(0);
}
x_659 = lean_string_utf8_byte_size(x_656);
x_660 = lean_unsigned_to_nat(0u);
x_661 = lean_nat_dec_eq(x_659, x_660);
lean_dec(x_659);
if (x_661 == 0)
{
uint8_t x_662; 
lean_dec(x_658);
x_662 = lean_string_dec_eq(x_656, x_503);
lean_dec(x_656);
if (x_662 == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_663 = l_Lake_invalidConfigEnvVar;
x_664 = lean_io_getenv(x_663, x_657);
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
if (lean_obj_tag(x_665) == 0)
{
lean_object* x_666; uint8_t x_667; uint8_t x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
lean_dec(x_664);
x_667 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_668 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
x_669 = lean_box(1);
x_670 = l_Lake_OutStream_get(x_669, x_666);
x_671 = lean_ctor_get(x_670, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_670, 1);
lean_inc(x_672);
lean_dec(x_670);
lean_inc(x_671);
x_673 = l_Lake_AnsiMode_isEnabled(x_671, x_668, x_672);
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
lean_dec(x_673);
x_676 = lean_box(x_667);
x_677 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__2___boxed), 5, 3);
lean_closure_set(x_677, 0, x_671);
lean_closure_set(x_677, 1, x_676);
lean_closure_set(x_677, 2, x_674);
x_678 = l_Lake_loadWorkspace(x_1, x_677, x_675);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_678, 1);
lean_inc(x_680);
lean_dec(x_678);
x_681 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_681, 0, x_679);
x_505 = x_681;
x_506 = x_680;
goto block_653;
}
else
{
lean_object* x_682; lean_object* x_683; 
x_682 = lean_ctor_get(x_678, 1);
lean_inc(x_682);
lean_dec(x_678);
x_683 = lean_box(0);
x_505 = x_683;
x_506 = x_682;
goto block_653;
}
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; 
lean_dec(x_503);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_684 = lean_ctor_get(x_664, 1);
lean_inc(x_684);
lean_dec(x_664);
x_685 = lean_ctor_get(x_665, 0);
lean_inc(x_685);
lean_dec(x_665);
x_686 = l_IO_eprint___at_IO_eprintln___spec__1(x_685, x_684);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_687 = lean_ctor_get(x_686, 1);
lean_inc(x_687);
lean_dec(x_686);
x_688 = l_Lake_setupFile___closed__9;
x_689 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_688, x_687);
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_690 = lean_ctor_get(x_689, 1);
lean_inc(x_690);
if (lean_is_exclusive(x_689)) {
 lean_ctor_release(x_689, 0);
 lean_ctor_release(x_689, 1);
 x_691 = x_689;
} else {
 lean_dec_ref(x_689);
 x_691 = lean_box(0);
}
x_692 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_691)) {
 x_693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_693 = x_691;
 lean_ctor_set_tag(x_693, 1);
}
lean_ctor_set(x_693, 0, x_692);
lean_ctor_set(x_693, 1, x_690);
return x_693;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; uint8_t x_697; lean_object* x_698; lean_object* x_699; uint8_t x_700; uint8_t x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_694 = lean_ctor_get(x_689, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_689, 1);
lean_inc(x_695);
lean_dec(x_689);
x_696 = lean_io_error_to_string(x_694);
x_697 = 3;
x_698 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set_uint8(x_698, sizeof(void*)*1, x_697);
x_699 = lean_box(1);
x_700 = 1;
x_701 = 0;
x_702 = l_Lake_OutStream_logEntry(x_699, x_698, x_700, x_701, x_695);
lean_dec(x_698);
x_703 = lean_ctor_get(x_702, 1);
lean_inc(x_703);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_704 = x_702;
} else {
 lean_dec_ref(x_702);
 x_704 = lean_box(0);
}
x_705 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_704)) {
 x_706 = lean_alloc_ctor(1, 2, 0);
} else {
 x_706 = x_704;
 lean_ctor_set_tag(x_706, 1);
}
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_703);
return x_706;
}
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; uint8_t x_710; lean_object* x_711; lean_object* x_712; uint8_t x_713; uint8_t x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_707 = lean_ctor_get(x_686, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_686, 1);
lean_inc(x_708);
lean_dec(x_686);
x_709 = lean_io_error_to_string(x_707);
x_710 = 3;
x_711 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set_uint8(x_711, sizeof(void*)*1, x_710);
x_712 = lean_box(1);
x_713 = 1;
x_714 = 0;
x_715 = l_Lake_OutStream_logEntry(x_712, x_711, x_713, x_714, x_708);
lean_dec(x_711);
x_716 = lean_ctor_get(x_715, 1);
lean_inc(x_716);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_717 = x_715;
} else {
 lean_dec_ref(x_715);
 x_717 = lean_box(0);
}
x_718 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_717)) {
 x_719 = lean_alloc_ctor(1, 2, 0);
} else {
 x_719 = x_717;
 lean_ctor_set_tag(x_719, 1);
}
lean_ctor_set(x_719, 0, x_718);
lean_ctor_set(x_719, 1, x_716);
return x_719;
}
}
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_503);
lean_dec(x_4);
lean_dec(x_3);
x_720 = lean_ctor_get(x_1, 0);
lean_inc(x_720);
lean_dec(x_1);
x_721 = l_Lake_Env_leanPath(x_720);
x_722 = l_Lake_Env_leanSrcPath(x_720);
x_723 = lean_box(0);
x_724 = lean_ctor_get(x_720, 0);
lean_inc(x_724);
lean_dec(x_720);
x_725 = lean_ctor_get(x_724, 4);
lean_inc(x_725);
lean_dec(x_724);
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
lean_dec(x_725);
x_727 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_723);
x_728 = lean_array_mk(x_727);
x_729 = l_Lake_setupFile___closed__3;
x_730 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_730, 0, x_721);
lean_ctor_set(x_730, 1, x_722);
lean_ctor_set(x_730, 2, x_729);
lean_ctor_set(x_730, 3, x_728);
x_731 = lean_box(0);
x_732 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set(x_732, 1, x_731);
x_733 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_732);
x_734 = l_Lean_Json_compress(x_733);
x_735 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_734, x_657);
if (lean_obj_tag(x_735) == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_735, 1);
lean_inc(x_737);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 lean_ctor_release(x_735, 1);
 x_738 = x_735;
} else {
 lean_dec_ref(x_735);
 x_738 = lean_box(0);
}
if (lean_is_scalar(x_738)) {
 x_739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_739 = x_738;
}
lean_ctor_set(x_739, 0, x_736);
lean_ctor_set(x_739, 1, x_737);
return x_739;
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; uint8_t x_743; lean_object* x_744; lean_object* x_745; uint8_t x_746; uint8_t x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_740 = lean_ctor_get(x_735, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_735, 1);
lean_inc(x_741);
lean_dec(x_735);
x_742 = lean_io_error_to_string(x_740);
x_743 = 3;
x_744 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_744, 0, x_742);
lean_ctor_set_uint8(x_744, sizeof(void*)*1, x_743);
x_745 = lean_box(1);
x_746 = 1;
x_747 = 0;
x_748 = l_Lake_OutStream_logEntry(x_745, x_744, x_746, x_747, x_741);
lean_dec(x_744);
x_749 = lean_ctor_get(x_748, 1);
lean_inc(x_749);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_750 = x_748;
} else {
 lean_dec_ref(x_748);
 x_750 = lean_box(0);
}
x_751 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_750)) {
 x_752 = lean_alloc_ctor(1, 2, 0);
} else {
 x_752 = x_750;
 lean_ctor_set_tag(x_752, 1);
}
lean_ctor_set(x_752, 0, x_751);
lean_ctor_set(x_752, 1, x_749);
return x_752;
}
}
}
else
{
lean_object* x_753; lean_object* x_754; 
lean_dec(x_656);
lean_dec(x_503);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_753 = l_Lake_setupFile___boxed__const__2;
if (lean_is_scalar(x_658)) {
 x_754 = lean_alloc_ctor(1, 2, 0);
} else {
 x_754 = x_658;
 lean_ctor_set_tag(x_754, 1);
}
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set(x_754, 1, x_657);
return x_754;
}
block_653:
{
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_507; lean_object* x_508; uint8_t x_509; uint8_t x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_503);
lean_dec(x_4);
lean_dec(x_3);
x_507 = lean_box(1);
x_508 = l_Lake_setupFile___closed__2;
x_509 = 1;
x_510 = 0;
x_511 = l_Lake_OutStream_logEntry(x_507, x_508, x_509, x_510, x_506);
x_512 = lean_ctor_get(x_511, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_513 = x_511;
} else {
 lean_dec_ref(x_511);
 x_513 = lean_box(0);
}
x_514 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_513)) {
 x_515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_515 = x_513;
 lean_ctor_set_tag(x_515, 1);
}
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_512);
return x_515;
}
else
{
lean_object* x_516; lean_object* x_517; 
x_516 = lean_ctor_get(x_505, 0);
lean_inc(x_516);
lean_dec(x_505);
lean_inc(x_503);
x_517 = l_Lake_Workspace_findModuleBySrc_x3f(x_503, x_516);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_518 = l_Lake_setupFile___closed__3;
x_519 = l_List_foldl___at_Lake_setupFile___spec__1(x_516, x_518, x_3);
x_520 = lean_alloc_closure((void*)(l_Lake_buildImportsAndDeps), 8, 2);
lean_closure_set(x_520, 0, x_503);
lean_closure_set(x_520, 1, x_519);
lean_inc(x_516);
x_521 = l_Lake_Workspace_runFetchM___rarg(x_516, x_520, x_4, x_506);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
lean_dec(x_521);
x_524 = lean_ctor_get(x_522, 0);
lean_inc(x_524);
lean_dec(x_522);
x_525 = lean_io_wait(x_524, x_523);
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_527 = lean_ctor_get(x_525, 1);
lean_inc(x_527);
lean_dec(x_525);
x_528 = lean_ctor_get(x_526, 0);
lean_inc(x_528);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_529 = x_526;
} else {
 lean_dec_ref(x_526);
 x_529 = lean_box(0);
}
x_530 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_516, x_528);
lean_dec(x_516);
x_531 = lean_box(0);
if (lean_is_scalar(x_529)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_529;
}
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_531);
x_533 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_532);
x_534 = l_Lean_Json_compress(x_533);
x_535 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_534, x_527);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_538 = x_535;
} else {
 lean_dec_ref(x_535);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_536);
lean_ctor_set(x_539, 1, x_537);
return x_539;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; uint8_t x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_540 = lean_ctor_get(x_535, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_535, 1);
lean_inc(x_541);
lean_dec(x_535);
x_542 = lean_io_error_to_string(x_540);
x_543 = 3;
x_544 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set_uint8(x_544, sizeof(void*)*1, x_543);
x_545 = lean_box(1);
x_546 = 1;
x_547 = 0;
x_548 = l_Lake_OutStream_logEntry(x_545, x_544, x_546, x_547, x_541);
lean_dec(x_544);
x_549 = lean_ctor_get(x_548, 1);
lean_inc(x_549);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 x_550 = x_548;
} else {
 lean_dec_ref(x_548);
 x_550 = lean_box(0);
}
x_551 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_550)) {
 x_552 = lean_alloc_ctor(1, 2, 0);
} else {
 x_552 = x_550;
 lean_ctor_set_tag(x_552, 1);
}
lean_ctor_set(x_552, 0, x_551);
lean_ctor_set(x_552, 1, x_549);
return x_552;
}
}
else
{
lean_object* x_553; lean_object* x_554; 
lean_dec(x_526);
lean_dec(x_516);
x_553 = lean_ctor_get(x_525, 1);
lean_inc(x_553);
lean_dec(x_525);
x_554 = l_Lake_setupFile___closed__5;
x_6 = x_554;
x_7 = x_553;
goto block_21;
}
}
else
{
lean_object* x_555; lean_object* x_556; 
lean_dec(x_516);
x_555 = lean_ctor_get(x_521, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_521, 1);
lean_inc(x_556);
lean_dec(x_521);
x_6 = x_555;
x_7 = x_556;
goto block_21;
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; uint8_t x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_503);
lean_dec(x_3);
x_557 = lean_ctor_get(x_517, 0);
lean_inc(x_557);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 x_558 = x_517;
} else {
 lean_dec_ref(x_517);
 x_558 = lean_box(0);
}
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
x_560 = 1;
x_561 = l_Lake_setupFile___closed__6;
x_562 = l_Lean_Name_toString(x_559, x_560, x_561);
x_563 = l_Lake_setupFile___closed__7;
x_564 = lean_string_append(x_563, x_562);
lean_dec(x_562);
x_565 = l_Lake_setupFile___closed__8;
x_566 = lean_string_append(x_564, x_565);
x_567 = lean_ctor_get(x_557, 2);
lean_inc(x_567);
if (lean_is_scalar(x_558)) {
 x_568 = lean_alloc_ctor(0, 1, 0);
} else {
 x_568 = x_558;
 lean_ctor_set_tag(x_568, 0);
}
lean_ctor_set(x_568, 0, x_567);
x_569 = l_Lake_Module_keyword;
x_570 = l_Lake_Module_depsFacet;
lean_inc(x_557);
x_571 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_571, 0, x_568);
lean_ctor_set(x_571, 1, x_569);
lean_ctor_set(x_571, 2, x_557);
lean_ctor_set(x_571, 3, x_570);
x_572 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_572, 0, x_571);
lean_closure_set(x_572, 1, lean_box(0));
x_573 = 0;
x_574 = lean_box(x_573);
x_575 = lean_alloc_closure((void*)(l_Lake_withRegisterJob___at_Lake_setupFile___spec__2___boxed), 9, 3);
lean_closure_set(x_575, 0, x_566);
lean_closure_set(x_575, 1, x_572);
lean_closure_set(x_575, 2, x_574);
lean_inc(x_516);
x_576 = l_Lake_Workspace_runFetchM___rarg(x_516, x_575, x_4, x_506);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec(x_576);
x_579 = lean_ctor_get(x_577, 0);
lean_inc(x_579);
lean_dec(x_577);
x_580 = lean_io_wait(x_579, x_578);
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; uint8_t x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
lean_dec(x_580);
x_583 = lean_ctor_get(x_581, 0);
lean_inc(x_583);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 x_584 = x_581;
} else {
 lean_dec_ref(x_581);
 x_584 = lean_box(0);
}
x_585 = lean_box(0);
x_586 = lean_ctor_get(x_557, 0);
lean_inc(x_586);
lean_dec(x_557);
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_587, 3);
lean_inc(x_588);
lean_dec(x_587);
x_589 = lean_ctor_get(x_588, 1);
lean_inc(x_589);
lean_dec(x_588);
x_590 = lean_ctor_get_uint8(x_589, sizeof(void*)*13);
x_591 = lean_ctor_get(x_586, 2);
lean_inc(x_591);
lean_dec(x_586);
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
lean_dec(x_591);
x_593 = lean_ctor_get_uint8(x_592, sizeof(void*)*13);
x_594 = l_Lake_instOrdBuildType;
x_595 = lean_box(x_590);
x_596 = lean_box(x_593);
x_597 = l_Ord_instDecidableRelLe___rarg(x_594, x_595, x_596);
x_598 = lean_ctor_get(x_589, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_589, 4);
lean_inc(x_599);
lean_dec(x_589);
x_600 = l_Array_append___rarg(x_598, x_599);
lean_dec(x_599);
x_601 = lean_ctor_get(x_592, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_592, 4);
lean_inc(x_602);
lean_dec(x_592);
x_603 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_516, x_583);
lean_dec(x_516);
if (x_597 == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; uint8_t x_633; 
x_627 = l_Lake_BuildType_leanOptions(x_593);
x_628 = l_Array_append___rarg(x_627, x_600);
lean_dec(x_600);
x_629 = l_Array_append___rarg(x_628, x_601);
lean_dec(x_601);
x_630 = l_Array_append___rarg(x_629, x_602);
lean_dec(x_602);
x_631 = lean_array_get_size(x_630);
x_632 = lean_unsigned_to_nat(0u);
x_633 = lean_nat_dec_lt(x_632, x_631);
if (x_633 == 0)
{
lean_dec(x_631);
lean_dec(x_630);
x_604 = x_585;
goto block_626;
}
else
{
uint8_t x_634; 
x_634 = lean_nat_dec_le(x_631, x_631);
if (x_634 == 0)
{
lean_dec(x_631);
lean_dec(x_630);
x_604 = x_585;
goto block_626;
}
else
{
size_t x_635; size_t x_636; lean_object* x_637; 
x_635 = 0;
x_636 = lean_usize_of_nat(x_631);
lean_dec(x_631);
x_637 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(x_630, x_635, x_636, x_585);
lean_dec(x_630);
x_604 = x_637;
goto block_626;
}
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; uint8_t x_644; 
x_638 = l_Lake_BuildType_leanOptions(x_590);
x_639 = l_Array_append___rarg(x_638, x_600);
lean_dec(x_600);
x_640 = l_Array_append___rarg(x_639, x_601);
lean_dec(x_601);
x_641 = l_Array_append___rarg(x_640, x_602);
lean_dec(x_602);
x_642 = lean_array_get_size(x_641);
x_643 = lean_unsigned_to_nat(0u);
x_644 = lean_nat_dec_lt(x_643, x_642);
if (x_644 == 0)
{
lean_dec(x_642);
lean_dec(x_641);
x_604 = x_585;
goto block_626;
}
else
{
uint8_t x_645; 
x_645 = lean_nat_dec_le(x_642, x_642);
if (x_645 == 0)
{
lean_dec(x_642);
lean_dec(x_641);
x_604 = x_585;
goto block_626;
}
else
{
size_t x_646; size_t x_647; lean_object* x_648; 
x_646 = 0;
x_647 = lean_usize_of_nat(x_642);
lean_dec(x_642);
x_648 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__3(x_641, x_646, x_647, x_585);
lean_dec(x_641);
x_604 = x_648;
goto block_626;
}
}
}
block_626:
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
if (lean_is_scalar(x_584)) {
 x_605 = lean_alloc_ctor(0, 2, 0);
} else {
 x_605 = x_584;
}
lean_ctor_set(x_605, 0, x_603);
lean_ctor_set(x_605, 1, x_604);
x_606 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_605);
x_607 = l_Lean_Json_compress(x_606);
x_608 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_607, x_582);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 lean_ctor_release(x_608, 1);
 x_611 = x_608;
} else {
 lean_dec_ref(x_608);
 x_611 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_612 = lean_alloc_ctor(0, 2, 0);
} else {
 x_612 = x_611;
}
lean_ctor_set(x_612, 0, x_609);
lean_ctor_set(x_612, 1, x_610);
return x_612;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; uint8_t x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; uint8_t x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_613 = lean_ctor_get(x_608, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_608, 1);
lean_inc(x_614);
lean_dec(x_608);
x_615 = lean_io_error_to_string(x_613);
x_616 = 3;
x_617 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_617, 0, x_615);
lean_ctor_set_uint8(x_617, sizeof(void*)*1, x_616);
x_618 = lean_box(1);
x_619 = 1;
x_620 = 0;
x_621 = l_Lake_OutStream_logEntry(x_618, x_617, x_619, x_620, x_614);
lean_dec(x_617);
x_622 = lean_ctor_get(x_621, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_623 = x_621;
} else {
 lean_dec_ref(x_621);
 x_623 = lean_box(0);
}
x_624 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_623)) {
 x_625 = lean_alloc_ctor(1, 2, 0);
} else {
 x_625 = x_623;
 lean_ctor_set_tag(x_625, 1);
}
lean_ctor_set(x_625, 0, x_624);
lean_ctor_set(x_625, 1, x_622);
return x_625;
}
}
}
else
{
lean_object* x_649; lean_object* x_650; 
lean_dec(x_581);
lean_dec(x_557);
lean_dec(x_516);
x_649 = lean_ctor_get(x_580, 1);
lean_inc(x_649);
lean_dec(x_580);
x_650 = l_Lake_setupFile___closed__5;
x_6 = x_650;
x_7 = x_649;
goto block_21;
}
}
else
{
lean_object* x_651; lean_object* x_652; 
lean_dec(x_557);
lean_dec(x_516);
x_651 = lean_ctor_get(x_576, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_576, 1);
lean_inc(x_652);
lean_dec(x_576);
x_6 = x_651;
x_7 = x_652;
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
