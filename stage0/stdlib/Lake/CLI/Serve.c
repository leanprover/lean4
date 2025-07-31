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
static lean_object* l_Lake_setupFile___closed__5;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_Log_toString(lean_object*);
static lean_object* l_Lake_setupFile___closed__4;
lean_object* l_Lake_ensureJob___at___Lake_Module_recFetchSetup_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(lean_object*);
lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__3;
lean_object* l_Lake_Env_baseVars(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
static lean_object* l_Lake_serve___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_invalidConfigEnvVar;
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__0;
static lean_object* l_Lake_setupFile___closed__0;
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lake_setupExternalModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___closed__2;
static lean_object* l_Lake_setupFile___closed__7;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__1;
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
lean_object* l_Lean_parseImports_x27(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__2;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
static lean_object* l_Lake_invalidConfigEnvVar___closed__0;
lean_object* l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___closed__6;
extern lean_object* l_Lake_configModuleName;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object*, lean_object*);
lean_object* l_IO_println___at___Lean_printImportsJson_spec__1(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_logToStream(x_4, x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc_ref(x_8);
x_11 = l_Lake_ensureJob___at___Lake_Module_recFetchSetup_spec__6(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec_ref(x_11);
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
lean_dec_ref(x_8);
x_20 = lean_st_ref_take(x_19, x_14);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_3);
lean_inc_ref(x_13);
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
lean_dec_ref(x_8);
x_35 = lean_st_ref_take(x_34, x_14);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_2);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_3);
lean_inc_ref(x_38);
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
lean_inc_ref(x_47);
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
lean_dec_ref(x_8);
x_51 = lean_st_ref_take(x_50, x_14);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 3, 1);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_48);
lean_ctor_set(x_54, 2, x_2);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_3);
lean_inc_ref(x_54);
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
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_setupFile___closed__0;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":setup", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to load workspace", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_setupFile___closed__3;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_setupFile___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to configure the Lake workspace. Please restart the server after fixing the error above.", 95, 95);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___closed__7() {
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
lean_object* x_6; lean_object* x_7; lean_object* x_22; lean_object* x_23; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_inc_ref(x_2);
x_38 = l_Lake_resolvePath(x_2, x_5);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_42);
x_43 = l_Lake_realConfigFile(x_42, x_40);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
x_47 = lean_string_utf8_byte_size(x_45);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_47);
if (x_49 == 0)
{
uint8_t x_50; 
lean_free_object(x_43);
x_50 = lean_string_dec_eq(x_45, x_39);
lean_dec(x_45);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_41);
x_51 = l_Lake_invalidConfigEnvVar___closed__0;
x_52 = lean_io_getenv(x_51, x_46);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_box(1);
x_56 = l_Lake_OutStream_get(x_55, x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_60 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
lean_inc(x_57);
x_61 = l_Lake_AnsiMode_isEnabled(x_57, x_60, x_58);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_box(x_59);
x_65 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_65, 0, x_57);
lean_closure_set(x_65, 1, x_64);
lean_closure_set(x_65, 2, x_62);
x_66 = l_Lake_loadWorkspace(x_1, x_65, x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_113; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec_ref(x_66);
lean_inc(x_39);
x_113 = l_Lake_Workspace_findModuleBySrc_x3f(x_39, x_67);
if (lean_obj_tag(x_113) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_114; 
x_114 = l_IO_FS_readFile(x_39, x_68);
lean_dec(x_39);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec_ref(x_114);
lean_inc_ref(x_2);
x_117 = l_Lean_parseImports_x27(x_115, x_2, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_69 = x_118;
x_70 = x_119;
goto block_112;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_67);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_120 = lean_ctor_get(x_117, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
lean_dec_ref(x_117);
x_122 = lean_io_error_to_string(x_120);
x_123 = 1;
x_124 = 0;
x_125 = 3;
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_125);
x_127 = l_Lake_OutStream_logEntry(x_55, x_126, x_123, x_124, x_121);
lean_dec_ref(x_126);
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
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_67);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_134 = lean_ctor_get(x_114, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_114, 1);
lean_inc(x_135);
lean_dec_ref(x_114);
x_136 = lean_io_error_to_string(x_134);
x_137 = 1;
x_138 = 0;
x_139 = 3;
x_140 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_139);
x_141 = l_Lake_OutStream_logEntry(x_55, x_140, x_137, x_138, x_135);
lean_dec_ref(x_140);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_141, 0);
lean_dec(x_143);
x_144 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_141, 1);
lean_ctor_set(x_141, 0, x_144);
return x_141;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_dec(x_141);
x_146 = l_Lake_setupFile___boxed__const__1;
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
else
{
lean_object* x_148; 
lean_dec(x_39);
x_148 = lean_ctor_get(x_3, 0);
lean_inc(x_148);
lean_dec_ref(x_3);
x_69 = x_148;
x_70 = x_68;
goto block_112;
}
}
else
{
uint8_t x_149; 
lean_dec(x_39);
lean_dec(x_3);
lean_dec_ref(x_2);
x_149 = !lean_is_exclusive(x_113);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_150 = lean_ctor_get(x_113, 0);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 2);
lean_inc(x_152);
x_153 = 1;
x_154 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_151, x_153);
x_155 = l_Lake_setupFile___closed__2;
x_156 = lean_string_append(x_154, x_155);
x_157 = l_Lake_Module_setupFacet;
lean_ctor_set_tag(x_113, 0);
lean_ctor_set(x_113, 0, x_152);
x_158 = l_Lake_Module_keyword;
x_159 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_159, 0, x_113);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_159, 2, x_150);
lean_ctor_set(x_159, 3, x_157);
x_160 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1), 8, 1);
lean_closure_set(x_160, 0, x_159);
x_161 = lean_box(x_50);
x_162 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2___boxed), 10, 3);
lean_closure_set(x_162, 0, x_160);
lean_closure_set(x_162, 1, x_156);
lean_closure_set(x_162, 2, x_161);
x_163 = l_Lake_Workspace_runFetchM___redArg(x_67, x_162, x_4, x_68);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec_ref(x_163);
x_166 = lean_ctor_get(x_164, 0);
lean_inc_ref(x_166);
lean_dec(x_164);
x_167 = lean_io_wait(x_166, x_165);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec_ref(x_167);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
lean_dec_ref(x_168);
x_171 = l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(x_170);
x_172 = l_Lean_Json_compress(x_171);
x_173 = l_IO_println___at___Lean_printImportsJson_spec__1(x_172, x_169);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
return x_173;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_173);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_178 = lean_ctor_get(x_173, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_173, 1);
lean_inc(x_179);
lean_dec_ref(x_173);
x_180 = lean_io_error_to_string(x_178);
x_181 = 1;
x_182 = 0;
x_183 = 3;
x_184 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_184, 0, x_180);
lean_ctor_set_uint8(x_184, sizeof(void*)*1, x_183);
x_185 = l_Lake_OutStream_logEntry(x_55, x_184, x_181, x_182, x_179);
lean_dec_ref(x_184);
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_185, 0);
lean_dec(x_187);
x_188 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_185, 1);
lean_ctor_set(x_185, 0, x_188);
return x_185;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
lean_dec(x_185);
x_190 = l_Lake_setupFile___boxed__const__1;
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec_ref(x_168);
x_192 = lean_ctor_get(x_167, 1);
lean_inc(x_192);
lean_dec_ref(x_167);
x_193 = l_Lake_setupFile___closed__1;
x_6 = x_193;
x_7 = x_192;
goto block_21;
}
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_163, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_163, 1);
lean_inc(x_195);
lean_dec_ref(x_163);
x_6 = x_194;
x_7 = x_195;
goto block_21;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_196 = lean_ctor_get(x_113, 0);
lean_inc(x_196);
lean_dec(x_113);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 2);
lean_inc(x_198);
x_199 = 1;
x_200 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_197, x_199);
x_201 = l_Lake_setupFile___closed__2;
x_202 = lean_string_append(x_200, x_201);
x_203 = l_Lake_Module_setupFacet;
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_198);
x_205 = l_Lake_Module_keyword;
x_206 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
lean_ctor_set(x_206, 2, x_196);
lean_ctor_set(x_206, 3, x_203);
x_207 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1), 8, 1);
lean_closure_set(x_207, 0, x_206);
x_208 = lean_box(x_50);
x_209 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2___boxed), 10, 3);
lean_closure_set(x_209, 0, x_207);
lean_closure_set(x_209, 1, x_202);
lean_closure_set(x_209, 2, x_208);
x_210 = l_Lake_Workspace_runFetchM___redArg(x_67, x_209, x_4, x_68);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec_ref(x_210);
x_213 = lean_ctor_get(x_211, 0);
lean_inc_ref(x_213);
lean_dec(x_211);
x_214 = lean_io_wait(x_213, x_212);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec_ref(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
lean_dec_ref(x_215);
x_218 = l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(x_217);
x_219 = l_Lean_Json_compress(x_218);
x_220 = l_IO_println___at___Lean_printImportsJson_spec__1(x_219, x_216);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_225 = lean_ctor_get(x_220, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_220, 1);
lean_inc(x_226);
lean_dec_ref(x_220);
x_227 = lean_io_error_to_string(x_225);
x_228 = 1;
x_229 = 0;
x_230 = 3;
x_231 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_231, 0, x_227);
lean_ctor_set_uint8(x_231, sizeof(void*)*1, x_230);
x_232 = l_Lake_OutStream_logEntry(x_55, x_231, x_228, x_229, x_226);
lean_dec_ref(x_231);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_234 = x_232;
} else {
 lean_dec_ref(x_232);
 x_234 = lean_box(0);
}
x_235 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_234;
 lean_ctor_set_tag(x_236, 1);
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_233);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; 
lean_dec_ref(x_215);
x_237 = lean_ctor_get(x_214, 1);
lean_inc(x_237);
lean_dec_ref(x_214);
x_238 = l_Lake_setupFile___closed__1;
x_6 = x_238;
x_7 = x_237;
goto block_21;
}
}
else
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_210, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_210, 1);
lean_inc(x_240);
lean_dec_ref(x_210);
x_6 = x_239;
x_7 = x_240;
goto block_21;
}
}
}
block_112:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_71, 3);
lean_inc_ref(x_72);
lean_dec_ref(x_71);
x_73 = lean_ctor_get(x_72, 1);
lean_inc_ref(x_73);
lean_dec_ref(x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_73, 4);
lean_inc_ref(x_75);
lean_dec_ref(x_73);
x_76 = l_Lean_LeanOptions_ofArray(x_74);
lean_dec_ref(x_74);
x_77 = l_Lean_LeanOptions_appendArray(x_76, x_75);
lean_dec_ref(x_75);
x_78 = lean_alloc_closure((void*)(l_Lake_setupExternalModule), 10, 3);
lean_closure_set(x_78, 0, x_2);
lean_closure_set(x_78, 1, x_69);
lean_closure_set(x_78, 2, x_77);
x_79 = l_Lake_Workspace_runFetchM___redArg(x_67, x_78, x_4, x_70);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc_ref(x_82);
lean_dec(x_80);
x_83 = lean_io_wait(x_82, x_81);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(x_86);
x_88 = l_Lean_Json_compress(x_87);
x_89 = l_IO_println___at___Lean_printImportsJson_spec__1(x_88, x_85);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_89);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_dec_ref(x_89);
x_96 = lean_io_error_to_string(x_94);
x_97 = 1;
x_98 = 0;
x_99 = 3;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
x_101 = l_Lake_OutStream_logEntry(x_55, x_100, x_97, x_98, x_95);
lean_dec_ref(x_100);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_dec(x_103);
x_104 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_101, 1);
lean_ctor_set(x_101, 0, x_104);
return x_101;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_dec(x_101);
x_106 = l_Lake_setupFile___boxed__const__1;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_84);
x_108 = lean_ctor_get(x_83, 1);
lean_inc(x_108);
lean_dec_ref(x_83);
x_109 = l_Lake_setupFile___closed__1;
x_22 = x_109;
x_23 = x_108;
goto block_37;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_79, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_79, 1);
lean_inc(x_111);
lean_dec_ref(x_79);
x_22 = x_110;
x_23 = x_111;
goto block_37;
}
}
}
else
{
lean_object* x_241; uint8_t x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_241 = lean_ctor_get(x_66, 1);
lean_inc(x_241);
lean_dec_ref(x_66);
x_242 = 1;
x_243 = 0;
x_244 = l_Lake_setupFile___closed__4;
x_245 = l_Lake_OutStream_logEntry(x_55, x_244, x_242, x_243, x_241);
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_245, 0);
lean_dec(x_247);
x_248 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_245, 1);
lean_ctor_set(x_245, 0, x_248);
return x_245;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_245, 1);
lean_inc(x_249);
lean_dec(x_245);
x_250 = l_Lake_setupFile___boxed__const__1;
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_252 = lean_ctor_get(x_52, 1);
lean_inc(x_252);
lean_dec_ref(x_52);
x_253 = lean_ctor_get(x_53, 0);
lean_inc(x_253);
lean_dec_ref(x_53);
x_254 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_253, x_252);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = l_Lake_setupFile___closed__5;
x_257 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_256, x_255);
if (lean_obj_tag(x_257) == 0)
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_257, 0);
lean_dec(x_259);
x_260 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_257, 1);
lean_ctor_set(x_257, 0, x_260);
return x_257;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_257, 1);
lean_inc(x_261);
lean_dec(x_257);
x_262 = l_Lake_setupFile___boxed__const__1;
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; uint8_t x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_264 = lean_ctor_get(x_257, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_257, 1);
lean_inc(x_265);
lean_dec_ref(x_257);
x_266 = lean_io_error_to_string(x_264);
x_267 = 1;
x_268 = 0;
x_269 = lean_box(1);
x_270 = 3;
x_271 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_271, 0, x_266);
lean_ctor_set_uint8(x_271, sizeof(void*)*1, x_270);
x_272 = l_Lake_OutStream_logEntry(x_269, x_271, x_267, x_268, x_265);
lean_dec_ref(x_271);
x_273 = !lean_is_exclusive(x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_272, 0);
lean_dec(x_274);
x_275 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_272, 1);
lean_ctor_set(x_272, 0, x_275);
return x_272;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_272, 1);
lean_inc(x_276);
lean_dec(x_272);
x_277 = l_Lake_setupFile___boxed__const__1;
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; uint8_t x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_279 = lean_ctor_get(x_254, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_254, 1);
lean_inc(x_280);
lean_dec_ref(x_254);
x_281 = lean_io_error_to_string(x_279);
x_282 = 1;
x_283 = 0;
x_284 = lean_box(1);
x_285 = 3;
x_286 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_286, 0, x_281);
lean_ctor_set_uint8(x_286, sizeof(void*)*1, x_285);
x_287 = l_Lake_OutStream_logEntry(x_284, x_286, x_282, x_283, x_280);
lean_dec_ref(x_286);
x_288 = !lean_is_exclusive(x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_287, 0);
lean_dec(x_289);
x_290 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_287, 1);
lean_ctor_set(x_287, 0, x_290);
return x_287;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_287, 1);
lean_inc(x_291);
lean_dec(x_287);
x_292 = l_Lake_setupFile___boxed__const__1;
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_294 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_294);
lean_dec_ref(x_41);
x_295 = lean_ctor_get(x_294, 4);
lean_inc_ref(x_295);
lean_dec_ref(x_294);
x_296 = lean_ctor_get(x_295, 0);
lean_inc_ref(x_296);
lean_dec_ref(x_295);
x_297 = l_Lake_configModuleName;
x_298 = lean_box(0);
x_299 = lean_box(1);
x_300 = l_Lake_setupFile___closed__6;
x_301 = l_Lake_setupFile___closed__7;
x_302 = lean_array_push(x_301, x_296);
x_303 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_303, 0, x_297);
lean_ctor_set(x_303, 1, x_298);
lean_ctor_set(x_303, 2, x_299);
lean_ctor_set(x_303, 3, x_300);
lean_ctor_set(x_303, 4, x_302);
lean_ctor_set(x_303, 5, x_299);
lean_ctor_set_uint8(x_303, sizeof(void*)*6, x_49);
x_304 = l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(x_303);
x_305 = l_Lean_Json_compress(x_304);
x_306 = l_IO_println___at___Lean_printImportsJson_spec__1(x_305, x_46);
if (lean_obj_tag(x_306) == 0)
{
uint8_t x_307; 
x_307 = !lean_is_exclusive(x_306);
if (x_307 == 0)
{
return x_306;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_306, 0);
x_309 = lean_ctor_get(x_306, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_306);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; uint8_t x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_311 = lean_ctor_get(x_306, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_306, 1);
lean_inc(x_312);
lean_dec_ref(x_306);
x_313 = lean_io_error_to_string(x_311);
x_314 = 1;
x_315 = 0;
x_316 = lean_box(1);
x_317 = 3;
x_318 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_318, 0, x_313);
lean_ctor_set_uint8(x_318, sizeof(void*)*1, x_317);
x_319 = l_Lake_OutStream_logEntry(x_316, x_318, x_314, x_315, x_312);
lean_dec_ref(x_318);
x_320 = !lean_is_exclusive(x_319);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_319, 0);
lean_dec(x_321);
x_322 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_319, 1);
lean_ctor_set(x_319, 0, x_322);
return x_319;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_319, 1);
lean_inc(x_323);
lean_dec(x_319);
x_324 = l_Lake_setupFile___boxed__const__1;
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
}
}
else
{
lean_object* x_326; 
lean_dec(x_45);
lean_dec_ref(x_41);
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_326 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 0, x_326);
return x_43;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_327 = lean_ctor_get(x_43, 0);
x_328 = lean_ctor_get(x_43, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_43);
x_329 = lean_string_utf8_byte_size(x_327);
x_330 = lean_unsigned_to_nat(0u);
x_331 = lean_nat_dec_eq(x_329, x_330);
lean_dec(x_329);
if (x_331 == 0)
{
uint8_t x_332; 
x_332 = lean_string_dec_eq(x_327, x_39);
lean_dec(x_327);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec_ref(x_41);
x_333 = l_Lake_invalidConfigEnvVar___closed__0;
x_334 = lean_io_getenv(x_333, x_328);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec_ref(x_334);
x_337 = lean_box(1);
x_338 = l_Lake_OutStream_get(x_337, x_336);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec_ref(x_338);
x_341 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_342 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
lean_inc(x_339);
x_343 = l_Lake_AnsiMode_isEnabled(x_339, x_342, x_340);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec_ref(x_343);
x_346 = lean_box(x_341);
x_347 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_347, 0, x_339);
lean_closure_set(x_347, 1, x_346);
lean_closure_set(x_347, 2, x_344);
x_348 = l_Lake_loadWorkspace(x_1, x_347, x_345);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_393; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec_ref(x_348);
lean_inc(x_39);
x_393 = l_Lake_Workspace_findModuleBySrc_x3f(x_39, x_349);
if (lean_obj_tag(x_393) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_394; 
x_394 = l_IO_FS_readFile(x_39, x_350);
lean_dec(x_39);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec_ref(x_394);
lean_inc_ref(x_2);
x_397 = l_Lean_parseImports_x27(x_395, x_2, x_396);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec_ref(x_397);
x_351 = x_398;
x_352 = x_399;
goto block_392;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; uint8_t x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_349);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_400 = lean_ctor_get(x_397, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_397, 1);
lean_inc(x_401);
lean_dec_ref(x_397);
x_402 = lean_io_error_to_string(x_400);
x_403 = 1;
x_404 = 0;
x_405 = 3;
x_406 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_406, 0, x_402);
lean_ctor_set_uint8(x_406, sizeof(void*)*1, x_405);
x_407 = l_Lake_OutStream_logEntry(x_337, x_406, x_403, x_404, x_401);
lean_dec_ref(x_406);
x_408 = lean_ctor_get(x_407, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 x_409 = x_407;
} else {
 lean_dec_ref(x_407);
 x_409 = lean_box(0);
}
x_410 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_409)) {
 x_411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_411 = x_409;
 lean_ctor_set_tag(x_411, 1);
}
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_408);
return x_411;
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; uint8_t x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_349);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_412 = lean_ctor_get(x_394, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_394, 1);
lean_inc(x_413);
lean_dec_ref(x_394);
x_414 = lean_io_error_to_string(x_412);
x_415 = 1;
x_416 = 0;
x_417 = 3;
x_418 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_418, 0, x_414);
lean_ctor_set_uint8(x_418, sizeof(void*)*1, x_417);
x_419 = l_Lake_OutStream_logEntry(x_337, x_418, x_415, x_416, x_413);
lean_dec_ref(x_418);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_421 = x_419;
} else {
 lean_dec_ref(x_419);
 x_421 = lean_box(0);
}
x_422 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_421)) {
 x_423 = lean_alloc_ctor(1, 2, 0);
} else {
 x_423 = x_421;
 lean_ctor_set_tag(x_423, 1);
}
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_420);
return x_423;
}
}
else
{
lean_object* x_424; 
lean_dec(x_39);
x_424 = lean_ctor_get(x_3, 0);
lean_inc(x_424);
lean_dec_ref(x_3);
x_351 = x_424;
x_352 = x_350;
goto block_392;
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_39);
lean_dec(x_3);
lean_dec_ref(x_2);
x_425 = lean_ctor_get(x_393, 0);
lean_inc(x_425);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 x_426 = x_393;
} else {
 lean_dec_ref(x_393);
 x_426 = lean_box(0);
}
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_425, 2);
lean_inc(x_428);
x_429 = 1;
x_430 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_427, x_429);
x_431 = l_Lake_setupFile___closed__2;
x_432 = lean_string_append(x_430, x_431);
x_433 = l_Lake_Module_setupFacet;
if (lean_is_scalar(x_426)) {
 x_434 = lean_alloc_ctor(0, 1, 0);
} else {
 x_434 = x_426;
 lean_ctor_set_tag(x_434, 0);
}
lean_ctor_set(x_434, 0, x_428);
x_435 = l_Lake_Module_keyword;
x_436 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
lean_ctor_set(x_436, 2, x_425);
lean_ctor_set(x_436, 3, x_433);
x_437 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1), 8, 1);
lean_closure_set(x_437, 0, x_436);
x_438 = lean_box(x_332);
x_439 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2___boxed), 10, 3);
lean_closure_set(x_439, 0, x_437);
lean_closure_set(x_439, 1, x_432);
lean_closure_set(x_439, 2, x_438);
x_440 = l_Lake_Workspace_runFetchM___redArg(x_349, x_439, x_4, x_350);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec_ref(x_440);
x_443 = lean_ctor_get(x_441, 0);
lean_inc_ref(x_443);
lean_dec(x_441);
x_444 = lean_io_wait(x_443, x_442);
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
lean_dec_ref(x_444);
x_447 = lean_ctor_get(x_445, 0);
lean_inc(x_447);
lean_dec_ref(x_445);
x_448 = l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(x_447);
x_449 = l_Lean_Json_compress(x_448);
x_450 = l_IO_println___at___Lean_printImportsJson_spec__1(x_449, x_446);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_453 = x_450;
} else {
 lean_dec_ref(x_450);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_451);
lean_ctor_set(x_454, 1, x_452);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; uint8_t x_459; uint8_t x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_455 = lean_ctor_get(x_450, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_450, 1);
lean_inc(x_456);
lean_dec_ref(x_450);
x_457 = lean_io_error_to_string(x_455);
x_458 = 1;
x_459 = 0;
x_460 = 3;
x_461 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_461, 0, x_457);
lean_ctor_set_uint8(x_461, sizeof(void*)*1, x_460);
x_462 = l_Lake_OutStream_logEntry(x_337, x_461, x_458, x_459, x_456);
lean_dec_ref(x_461);
x_463 = lean_ctor_get(x_462, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_464 = x_462;
} else {
 lean_dec_ref(x_462);
 x_464 = lean_box(0);
}
x_465 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 2, 0);
} else {
 x_466 = x_464;
 lean_ctor_set_tag(x_466, 1);
}
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_463);
return x_466;
}
}
else
{
lean_object* x_467; lean_object* x_468; 
lean_dec_ref(x_445);
x_467 = lean_ctor_get(x_444, 1);
lean_inc(x_467);
lean_dec_ref(x_444);
x_468 = l_Lake_setupFile___closed__1;
x_6 = x_468;
x_7 = x_467;
goto block_21;
}
}
else
{
lean_object* x_469; lean_object* x_470; 
x_469 = lean_ctor_get(x_440, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_440, 1);
lean_inc(x_470);
lean_dec_ref(x_440);
x_6 = x_469;
x_7 = x_470;
goto block_21;
}
}
block_392:
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_353 = lean_ctor_get(x_349, 0);
lean_inc_ref(x_353);
x_354 = lean_ctor_get(x_353, 3);
lean_inc_ref(x_354);
lean_dec_ref(x_353);
x_355 = lean_ctor_get(x_354, 1);
lean_inc_ref(x_355);
lean_dec_ref(x_354);
x_356 = lean_ctor_get(x_355, 0);
lean_inc_ref(x_356);
x_357 = lean_ctor_get(x_355, 4);
lean_inc_ref(x_357);
lean_dec_ref(x_355);
x_358 = l_Lean_LeanOptions_ofArray(x_356);
lean_dec_ref(x_356);
x_359 = l_Lean_LeanOptions_appendArray(x_358, x_357);
lean_dec_ref(x_357);
x_360 = lean_alloc_closure((void*)(l_Lake_setupExternalModule), 10, 3);
lean_closure_set(x_360, 0, x_2);
lean_closure_set(x_360, 1, x_351);
lean_closure_set(x_360, 2, x_359);
x_361 = l_Lake_Workspace_runFetchM___redArg(x_349, x_360, x_4, x_352);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec_ref(x_361);
x_364 = lean_ctor_get(x_362, 0);
lean_inc_ref(x_364);
lean_dec(x_362);
x_365 = lean_io_wait(x_364, x_363);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec_ref(x_365);
x_368 = lean_ctor_get(x_366, 0);
lean_inc(x_368);
lean_dec_ref(x_366);
x_369 = l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(x_368);
x_370 = l_Lean_Json_compress(x_369);
x_371 = l_IO_println___at___Lean_printImportsJson_spec__1(x_370, x_367);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_374 = x_371;
} else {
 lean_dec_ref(x_371);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; uint8_t x_380; uint8_t x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_376 = lean_ctor_get(x_371, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_371, 1);
lean_inc(x_377);
lean_dec_ref(x_371);
x_378 = lean_io_error_to_string(x_376);
x_379 = 1;
x_380 = 0;
x_381 = 3;
x_382 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_382, 0, x_378);
lean_ctor_set_uint8(x_382, sizeof(void*)*1, x_381);
x_383 = l_Lake_OutStream_logEntry(x_337, x_382, x_379, x_380, x_377);
lean_dec_ref(x_382);
x_384 = lean_ctor_get(x_383, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_385 = x_383;
} else {
 lean_dec_ref(x_383);
 x_385 = lean_box(0);
}
x_386 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_385)) {
 x_387 = lean_alloc_ctor(1, 2, 0);
} else {
 x_387 = x_385;
 lean_ctor_set_tag(x_387, 1);
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_384);
return x_387;
}
}
else
{
lean_object* x_388; lean_object* x_389; 
lean_dec_ref(x_366);
x_388 = lean_ctor_get(x_365, 1);
lean_inc(x_388);
lean_dec_ref(x_365);
x_389 = l_Lake_setupFile___closed__1;
x_22 = x_389;
x_23 = x_388;
goto block_37;
}
}
else
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_ctor_get(x_361, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_361, 1);
lean_inc(x_391);
lean_dec_ref(x_361);
x_22 = x_390;
x_23 = x_391;
goto block_37;
}
}
}
else
{
lean_object* x_471; uint8_t x_472; uint8_t x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_471 = lean_ctor_get(x_348, 1);
lean_inc(x_471);
lean_dec_ref(x_348);
x_472 = 1;
x_473 = 0;
x_474 = l_Lake_setupFile___closed__4;
x_475 = l_Lake_OutStream_logEntry(x_337, x_474, x_472, x_473, x_471);
x_476 = lean_ctor_get(x_475, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_477 = x_475;
} else {
 lean_dec_ref(x_475);
 x_477 = lean_box(0);
}
x_478 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(1, 2, 0);
} else {
 x_479 = x_477;
 lean_ctor_set_tag(x_479, 1);
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_476);
return x_479;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_480 = lean_ctor_get(x_334, 1);
lean_inc(x_480);
lean_dec_ref(x_334);
x_481 = lean_ctor_get(x_335, 0);
lean_inc(x_481);
lean_dec_ref(x_335);
x_482 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_481, x_480);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
lean_dec_ref(x_482);
x_484 = l_Lake_setupFile___closed__5;
x_485 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_484, x_483);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_486 = lean_ctor_get(x_485, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_487 = x_485;
} else {
 lean_dec_ref(x_485);
 x_487 = lean_box(0);
}
x_488 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_487)) {
 x_489 = lean_alloc_ctor(1, 2, 0);
} else {
 x_489 = x_487;
 lean_ctor_set_tag(x_489, 1);
}
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_486);
return x_489;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; uint8_t x_494; lean_object* x_495; uint8_t x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_490 = lean_ctor_get(x_485, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_485, 1);
lean_inc(x_491);
lean_dec_ref(x_485);
x_492 = lean_io_error_to_string(x_490);
x_493 = 1;
x_494 = 0;
x_495 = lean_box(1);
x_496 = 3;
x_497 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_497, 0, x_492);
lean_ctor_set_uint8(x_497, sizeof(void*)*1, x_496);
x_498 = l_Lake_OutStream_logEntry(x_495, x_497, x_493, x_494, x_491);
lean_dec_ref(x_497);
x_499 = lean_ctor_get(x_498, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_500 = x_498;
} else {
 lean_dec_ref(x_498);
 x_500 = lean_box(0);
}
x_501 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_500)) {
 x_502 = lean_alloc_ctor(1, 2, 0);
} else {
 x_502 = x_500;
 lean_ctor_set_tag(x_502, 1);
}
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_499);
return x_502;
}
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; uint8_t x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_503 = lean_ctor_get(x_482, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_482, 1);
lean_inc(x_504);
lean_dec_ref(x_482);
x_505 = lean_io_error_to_string(x_503);
x_506 = 1;
x_507 = 0;
x_508 = lean_box(1);
x_509 = 3;
x_510 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_510, 0, x_505);
lean_ctor_set_uint8(x_510, sizeof(void*)*1, x_509);
x_511 = l_Lake_OutStream_logEntry(x_508, x_510, x_506, x_507, x_504);
lean_dec_ref(x_510);
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
}
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_516 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_516);
lean_dec_ref(x_41);
x_517 = lean_ctor_get(x_516, 4);
lean_inc_ref(x_517);
lean_dec_ref(x_516);
x_518 = lean_ctor_get(x_517, 0);
lean_inc_ref(x_518);
lean_dec_ref(x_517);
x_519 = l_Lake_configModuleName;
x_520 = lean_box(0);
x_521 = lean_box(1);
x_522 = l_Lake_setupFile___closed__6;
x_523 = l_Lake_setupFile___closed__7;
x_524 = lean_array_push(x_523, x_518);
x_525 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_525, 0, x_519);
lean_ctor_set(x_525, 1, x_520);
lean_ctor_set(x_525, 2, x_521);
lean_ctor_set(x_525, 3, x_522);
lean_ctor_set(x_525, 4, x_524);
lean_ctor_set(x_525, 5, x_521);
lean_ctor_set_uint8(x_525, sizeof(void*)*6, x_331);
x_526 = l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(x_525);
x_527 = l_Lean_Json_compress(x_526);
x_528 = l_IO_println___at___Lean_printImportsJson_spec__1(x_527, x_328);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_531 = x_528;
} else {
 lean_dec_ref(x_528);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_529);
lean_ctor_set(x_532, 1, x_530);
return x_532;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; uint8_t x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_533 = lean_ctor_get(x_528, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_528, 1);
lean_inc(x_534);
lean_dec_ref(x_528);
x_535 = lean_io_error_to_string(x_533);
x_536 = 1;
x_537 = 0;
x_538 = lean_box(1);
x_539 = 3;
x_540 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set_uint8(x_540, sizeof(void*)*1, x_539);
x_541 = l_Lake_OutStream_logEntry(x_538, x_540, x_536, x_537, x_534);
lean_dec_ref(x_540);
x_542 = lean_ctor_get(x_541, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_543 = x_541;
} else {
 lean_dec_ref(x_541);
 x_543 = lean_box(0);
}
x_544 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_543)) {
 x_545 = lean_alloc_ctor(1, 2, 0);
} else {
 x_545 = x_543;
 lean_ctor_set_tag(x_545, 1);
}
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_542);
return x_545;
}
}
}
else
{
lean_object* x_546; lean_object* x_547; 
lean_dec(x_327);
lean_dec_ref(x_41);
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_546 = l_Lake_setupFile___boxed__const__2;
x_547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_328);
return x_547;
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
lean_dec_ref(x_13);
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
block_37:
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_24 = lean_io_error_to_string(x_22);
x_25 = 1;
x_26 = 0;
x_27 = lean_box(1);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = l_Lake_OutStream_logEntry(x_27, x_29, x_25, x_26, x_23);
lean_dec_ref(x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = l_Lake_setupFile___boxed__const__1;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = l_Lake_setupFile___lam__0(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_setupFile___lam__2(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_10 = lean_array_uget(x_4, x_5);
x_11 = l_Lake_OutStream_logEntry(x_1, x_10, x_2, x_3, x_8);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
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
x_2 = l_Lake_setupFile___closed__7;
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
lean_inc_ref(x_1);
x_27 = lean_alloc_closure((void*)(l_Lake_loadWorkspace), 3, 1);
lean_closure_set(x_27, 0, x_1);
x_28 = l_Lake_LoggerIO_captureLog___redArg(x_27, x_3);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
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
lean_dec_ref(x_66);
x_34 = x_67;
goto block_55;
}
}
block_26:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 7);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
x_10 = l_Lake_serve___closed__0;
x_11 = l_Lake_serve___closed__2;
x_12 = l_Array_append___redArg(x_11, x_5);
lean_dec_ref(x_5);
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
lean_dec_ref(x_18);
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
lean_dec_ref(x_36);
x_38 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_38);
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
x_45 = l_Lake_setupFile___closed__6;
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_31);
x_51 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_51, 3);
lean_inc_ref(x_52);
lean_dec_ref(x_51);
x_53 = lean_ctor_get(x_52, 4);
lean_inc_ref(x_53);
lean_dec_ref(x_52);
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
x_10 = lean_unbox(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(x_1, x_9, x_10, x_4, x_11, x_12, x_7, x_8);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_serve(x_1, x_2, x_3);
lean_dec_ref(x_2);
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
l_Lake_setupFile___closed__6 = _init_l_Lake_setupFile___closed__6();
lean_mark_persistent(l_Lake_setupFile___closed__6);
l_Lake_setupFile___closed__7 = _init_l_Lake_setupFile___closed__7();
lean_mark_persistent(l_Lake_setupFile___closed__7);
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
