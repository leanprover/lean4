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
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__0;
static lean_object* l_Lake_setupFile___closed__0;
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__1___boxed(lean_object*, lean_object*);
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
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_150 = lean_ctor_get(x_113, 0);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 2);
lean_inc(x_152);
x_153 = lean_box(x_50);
x_154 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_154, 0, x_153);
x_155 = 1;
x_156 = l_Lean_Name_toString(x_151, x_155, x_154);
x_157 = l_Lake_setupFile___closed__2;
x_158 = lean_string_append(x_156, x_157);
x_159 = l_Lake_Module_setupFacet;
lean_ctor_set_tag(x_113, 0);
lean_ctor_set(x_113, 0, x_152);
x_160 = l_Lake_Module_keyword;
x_161 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_161, 0, x_113);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_161, 2, x_150);
lean_ctor_set(x_161, 3, x_159);
x_162 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 8, 1);
lean_closure_set(x_162, 0, x_161);
x_163 = lean_box(x_50);
x_164 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 10, 3);
lean_closure_set(x_164, 0, x_162);
lean_closure_set(x_164, 1, x_158);
lean_closure_set(x_164, 2, x_163);
x_165 = l_Lake_Workspace_runFetchM___redArg(x_67, x_164, x_4, x_68);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec_ref(x_165);
x_168 = lean_ctor_get(x_166, 0);
lean_inc_ref(x_168);
lean_dec(x_166);
x_169 = lean_io_wait(x_168, x_167);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec_ref(x_169);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec_ref(x_170);
x_173 = l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(x_172);
x_174 = l_Lean_Json_compress(x_173);
x_175 = l_IO_println___at___Lean_printImportsJson_spec__1(x_174, x_171);
if (lean_obj_tag(x_175) == 0)
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
return x_175;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_175, 0);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_175);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_180 = lean_ctor_get(x_175, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_175, 1);
lean_inc(x_181);
lean_dec_ref(x_175);
x_182 = lean_io_error_to_string(x_180);
x_183 = 1;
x_184 = 0;
x_185 = 3;
x_186 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_185);
x_187 = l_Lake_OutStream_logEntry(x_55, x_186, x_183, x_184, x_181);
lean_dec_ref(x_186);
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_187, 0);
lean_dec(x_189);
x_190 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_187, 1);
lean_ctor_set(x_187, 0, x_190);
return x_187;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
lean_dec(x_187);
x_192 = l_Lake_setupFile___boxed__const__1;
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; 
lean_dec_ref(x_170);
x_194 = lean_ctor_get(x_169, 1);
lean_inc(x_194);
lean_dec_ref(x_169);
x_195 = l_Lake_setupFile___closed__1;
x_6 = x_195;
x_7 = x_194;
goto block_21;
}
}
else
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_165, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_165, 1);
lean_inc(x_197);
lean_dec_ref(x_165);
x_6 = x_196;
x_7 = x_197;
goto block_21;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_198 = lean_ctor_get(x_113, 0);
lean_inc(x_198);
lean_dec(x_113);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 2);
lean_inc(x_200);
x_201 = lean_box(x_50);
x_202 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_202, 0, x_201);
x_203 = 1;
x_204 = l_Lean_Name_toString(x_199, x_203, x_202);
x_205 = l_Lake_setupFile___closed__2;
x_206 = lean_string_append(x_204, x_205);
x_207 = l_Lake_Module_setupFacet;
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_200);
x_209 = l_Lake_Module_keyword;
x_210 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set(x_210, 2, x_198);
lean_ctor_set(x_210, 3, x_207);
x_211 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 8, 1);
lean_closure_set(x_211, 0, x_210);
x_212 = lean_box(x_50);
x_213 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 10, 3);
lean_closure_set(x_213, 0, x_211);
lean_closure_set(x_213, 1, x_206);
lean_closure_set(x_213, 2, x_212);
x_214 = l_Lake_Workspace_runFetchM___redArg(x_67, x_213, x_4, x_68);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec_ref(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc_ref(x_217);
lean_dec(x_215);
x_218 = lean_io_wait(x_217, x_216);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec_ref(x_218);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
lean_dec_ref(x_219);
x_222 = l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(x_221);
x_223 = l_Lean_Json_compress(x_222);
x_224 = l_IO_println___at___Lean_printImportsJson_spec__1(x_223, x_220);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_227 = x_224;
} else {
 lean_dec_ref(x_224);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_229 = lean_ctor_get(x_224, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_224, 1);
lean_inc(x_230);
lean_dec_ref(x_224);
x_231 = lean_io_error_to_string(x_229);
x_232 = 1;
x_233 = 0;
x_234 = 3;
x_235 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_235, 0, x_231);
lean_ctor_set_uint8(x_235, sizeof(void*)*1, x_234);
x_236 = l_Lake_OutStream_logEntry(x_55, x_235, x_232, x_233, x_230);
lean_dec_ref(x_235);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
x_239 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_238;
 lean_ctor_set_tag(x_240, 1);
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; 
lean_dec_ref(x_219);
x_241 = lean_ctor_get(x_218, 1);
lean_inc(x_241);
lean_dec_ref(x_218);
x_242 = l_Lake_setupFile___closed__1;
x_6 = x_242;
x_7 = x_241;
goto block_21;
}
}
else
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_214, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_214, 1);
lean_inc(x_244);
lean_dec_ref(x_214);
x_6 = x_243;
x_7 = x_244;
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
lean_object* x_245; uint8_t x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_245 = lean_ctor_get(x_66, 1);
lean_inc(x_245);
lean_dec_ref(x_66);
x_246 = 1;
x_247 = 0;
x_248 = l_Lake_setupFile___closed__4;
x_249 = l_Lake_OutStream_logEntry(x_55, x_248, x_246, x_247, x_245);
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
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_256 = lean_ctor_get(x_52, 1);
lean_inc(x_256);
lean_dec_ref(x_52);
x_257 = lean_ctor_get(x_53, 0);
lean_inc(x_257);
lean_dec_ref(x_53);
x_258 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_257, x_256);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec_ref(x_258);
x_260 = l_Lake_setupFile___closed__5;
x_261 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_260, x_259);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_261, 0);
lean_dec(x_263);
x_264 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_261, 1);
lean_ctor_set(x_261, 0, x_264);
return x_261;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_261, 1);
lean_inc(x_265);
lean_dec(x_261);
x_266 = l_Lake_setupFile___boxed__const__1;
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; uint8_t x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_268 = lean_ctor_get(x_261, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_261, 1);
lean_inc(x_269);
lean_dec_ref(x_261);
x_270 = lean_io_error_to_string(x_268);
x_271 = 1;
x_272 = 0;
x_273 = lean_box(1);
x_274 = 3;
x_275 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_275, 0, x_270);
lean_ctor_set_uint8(x_275, sizeof(void*)*1, x_274);
x_276 = l_Lake_OutStream_logEntry(x_273, x_275, x_271, x_272, x_269);
lean_dec_ref(x_275);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_276, 0);
lean_dec(x_278);
x_279 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_276, 1);
lean_ctor_set(x_276, 0, x_279);
return x_276;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_276, 1);
lean_inc(x_280);
lean_dec(x_276);
x_281 = l_Lake_setupFile___boxed__const__1;
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; uint8_t x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_283 = lean_ctor_get(x_258, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_258, 1);
lean_inc(x_284);
lean_dec_ref(x_258);
x_285 = lean_io_error_to_string(x_283);
x_286 = 1;
x_287 = 0;
x_288 = lean_box(1);
x_289 = 3;
x_290 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_290, 0, x_285);
lean_ctor_set_uint8(x_290, sizeof(void*)*1, x_289);
x_291 = l_Lake_OutStream_logEntry(x_288, x_290, x_286, x_287, x_284);
lean_dec_ref(x_290);
x_292 = !lean_is_exclusive(x_291);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_291, 0);
lean_dec(x_293);
x_294 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_291, 1);
lean_ctor_set(x_291, 0, x_294);
return x_291;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_291, 1);
lean_inc(x_295);
lean_dec(x_291);
x_296 = l_Lake_setupFile___boxed__const__1;
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_295);
return x_297;
}
}
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_298 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_298);
lean_dec_ref(x_41);
x_299 = lean_ctor_get(x_298, 4);
lean_inc_ref(x_299);
lean_dec_ref(x_298);
x_300 = lean_ctor_get(x_299, 0);
lean_inc_ref(x_300);
lean_dec_ref(x_299);
x_301 = l_Lake_configModuleName;
x_302 = lean_box(0);
x_303 = lean_box(1);
x_304 = l_Lake_setupFile___closed__6;
x_305 = l_Lake_setupFile___closed__7;
x_306 = lean_array_push(x_305, x_300);
x_307 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_307, 0, x_301);
lean_ctor_set(x_307, 1, x_302);
lean_ctor_set(x_307, 2, x_303);
lean_ctor_set(x_307, 3, x_304);
lean_ctor_set(x_307, 4, x_306);
lean_ctor_set(x_307, 5, x_303);
lean_ctor_set_uint8(x_307, sizeof(void*)*6, x_49);
x_308 = l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(x_307);
x_309 = l_Lean_Json_compress(x_308);
x_310 = l_IO_println___at___Lean_printImportsJson_spec__1(x_309, x_46);
if (lean_obj_tag(x_310) == 0)
{
uint8_t x_311; 
x_311 = !lean_is_exclusive(x_310);
if (x_311 == 0)
{
return x_310;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_310, 0);
x_313 = lean_ctor_get(x_310, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_310);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; uint8_t x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_315 = lean_ctor_get(x_310, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_310, 1);
lean_inc(x_316);
lean_dec_ref(x_310);
x_317 = lean_io_error_to_string(x_315);
x_318 = 1;
x_319 = 0;
x_320 = lean_box(1);
x_321 = 3;
x_322 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_322, 0, x_317);
lean_ctor_set_uint8(x_322, sizeof(void*)*1, x_321);
x_323 = l_Lake_OutStream_logEntry(x_320, x_322, x_318, x_319, x_316);
lean_dec_ref(x_322);
x_324 = !lean_is_exclusive(x_323);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_ctor_get(x_323, 0);
lean_dec(x_325);
x_326 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_323, 1);
lean_ctor_set(x_323, 0, x_326);
return x_323;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
lean_dec(x_323);
x_328 = l_Lake_setupFile___boxed__const__1;
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_327);
return x_329;
}
}
}
}
else
{
lean_object* x_330; 
lean_dec(x_45);
lean_dec_ref(x_41);
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_330 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 0, x_330);
return x_43;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_331 = lean_ctor_get(x_43, 0);
x_332 = lean_ctor_get(x_43, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_43);
x_333 = lean_string_utf8_byte_size(x_331);
x_334 = lean_unsigned_to_nat(0u);
x_335 = lean_nat_dec_eq(x_333, x_334);
lean_dec(x_333);
if (x_335 == 0)
{
uint8_t x_336; 
x_336 = lean_string_dec_eq(x_331, x_39);
lean_dec(x_331);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec_ref(x_41);
x_337 = l_Lake_invalidConfigEnvVar___closed__0;
x_338 = lean_io_getenv(x_337, x_332);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; uint8_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec_ref(x_338);
x_341 = lean_box(1);
x_342 = l_Lake_OutStream_get(x_341, x_340);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec_ref(x_342);
x_345 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_346 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
lean_inc(x_343);
x_347 = l_Lake_AnsiMode_isEnabled(x_343, x_346, x_344);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
lean_dec_ref(x_347);
x_350 = lean_box(x_345);
x_351 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_351, 0, x_343);
lean_closure_set(x_351, 1, x_350);
lean_closure_set(x_351, 2, x_348);
x_352 = l_Lake_loadWorkspace(x_1, x_351, x_349);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_397; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec_ref(x_352);
lean_inc(x_39);
x_397 = l_Lake_Workspace_findModuleBySrc_x3f(x_39, x_353);
if (lean_obj_tag(x_397) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_398; 
x_398 = l_IO_FS_readFile(x_39, x_354);
lean_dec(x_39);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec_ref(x_398);
lean_inc_ref(x_2);
x_401 = l_Lean_parseImports_x27(x_399, x_2, x_400);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec_ref(x_401);
x_355 = x_402;
x_356 = x_403;
goto block_396;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; uint8_t x_408; uint8_t x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_353);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_404 = lean_ctor_get(x_401, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_401, 1);
lean_inc(x_405);
lean_dec_ref(x_401);
x_406 = lean_io_error_to_string(x_404);
x_407 = 1;
x_408 = 0;
x_409 = 3;
x_410 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_410, 0, x_406);
lean_ctor_set_uint8(x_410, sizeof(void*)*1, x_409);
x_411 = l_Lake_OutStream_logEntry(x_341, x_410, x_407, x_408, x_405);
lean_dec_ref(x_410);
x_412 = lean_ctor_get(x_411, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_413 = x_411;
} else {
 lean_dec_ref(x_411);
 x_413 = lean_box(0);
}
x_414 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_413)) {
 x_415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_415 = x_413;
 lean_ctor_set_tag(x_415, 1);
}
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_412);
return x_415;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; uint8_t x_420; uint8_t x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_353);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_416 = lean_ctor_get(x_398, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_398, 1);
lean_inc(x_417);
lean_dec_ref(x_398);
x_418 = lean_io_error_to_string(x_416);
x_419 = 1;
x_420 = 0;
x_421 = 3;
x_422 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_422, 0, x_418);
lean_ctor_set_uint8(x_422, sizeof(void*)*1, x_421);
x_423 = l_Lake_OutStream_logEntry(x_341, x_422, x_419, x_420, x_417);
lean_dec_ref(x_422);
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_425 = x_423;
} else {
 lean_dec_ref(x_423);
 x_425 = lean_box(0);
}
x_426 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_425)) {
 x_427 = lean_alloc_ctor(1, 2, 0);
} else {
 x_427 = x_425;
 lean_ctor_set_tag(x_427, 1);
}
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_424);
return x_427;
}
}
else
{
lean_object* x_428; 
lean_dec(x_39);
x_428 = lean_ctor_get(x_3, 0);
lean_inc(x_428);
lean_dec_ref(x_3);
x_355 = x_428;
x_356 = x_354;
goto block_396;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_39);
lean_dec(x_3);
lean_dec_ref(x_2);
x_429 = lean_ctor_get(x_397, 0);
lean_inc(x_429);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 x_430 = x_397;
} else {
 lean_dec_ref(x_397);
 x_430 = lean_box(0);
}
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_429, 2);
lean_inc(x_432);
x_433 = lean_box(x_336);
x_434 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_434, 0, x_433);
x_435 = 1;
x_436 = l_Lean_Name_toString(x_431, x_435, x_434);
x_437 = l_Lake_setupFile___closed__2;
x_438 = lean_string_append(x_436, x_437);
x_439 = l_Lake_Module_setupFacet;
if (lean_is_scalar(x_430)) {
 x_440 = lean_alloc_ctor(0, 1, 0);
} else {
 x_440 = x_430;
 lean_ctor_set_tag(x_440, 0);
}
lean_ctor_set(x_440, 0, x_432);
x_441 = l_Lake_Module_keyword;
x_442 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
lean_ctor_set(x_442, 2, x_429);
lean_ctor_set(x_442, 3, x_439);
x_443 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 8, 1);
lean_closure_set(x_443, 0, x_442);
x_444 = lean_box(x_336);
x_445 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 10, 3);
lean_closure_set(x_445, 0, x_443);
lean_closure_set(x_445, 1, x_438);
lean_closure_set(x_445, 2, x_444);
x_446 = l_Lake_Workspace_runFetchM___redArg(x_353, x_445, x_4, x_354);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
lean_dec_ref(x_446);
x_449 = lean_ctor_get(x_447, 0);
lean_inc_ref(x_449);
lean_dec(x_447);
x_450 = lean_io_wait(x_449, x_448);
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec_ref(x_450);
x_453 = lean_ctor_get(x_451, 0);
lean_inc(x_453);
lean_dec_ref(x_451);
x_454 = l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(x_453);
x_455 = l_Lean_Json_compress(x_454);
x_456 = l_IO_println___at___Lean_printImportsJson_spec__1(x_455, x_452);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_459 = x_456;
} else {
 lean_dec_ref(x_456);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(0, 2, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_457);
lean_ctor_set(x_460, 1, x_458);
return x_460;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; uint8_t x_465; uint8_t x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_461 = lean_ctor_get(x_456, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_456, 1);
lean_inc(x_462);
lean_dec_ref(x_456);
x_463 = lean_io_error_to_string(x_461);
x_464 = 1;
x_465 = 0;
x_466 = 3;
x_467 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_467, 0, x_463);
lean_ctor_set_uint8(x_467, sizeof(void*)*1, x_466);
x_468 = l_Lake_OutStream_logEntry(x_341, x_467, x_464, x_465, x_462);
lean_dec_ref(x_467);
x_469 = lean_ctor_get(x_468, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_470 = x_468;
} else {
 lean_dec_ref(x_468);
 x_470 = lean_box(0);
}
x_471 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_470)) {
 x_472 = lean_alloc_ctor(1, 2, 0);
} else {
 x_472 = x_470;
 lean_ctor_set_tag(x_472, 1);
}
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_469);
return x_472;
}
}
else
{
lean_object* x_473; lean_object* x_474; 
lean_dec_ref(x_451);
x_473 = lean_ctor_get(x_450, 1);
lean_inc(x_473);
lean_dec_ref(x_450);
x_474 = l_Lake_setupFile___closed__1;
x_6 = x_474;
x_7 = x_473;
goto block_21;
}
}
else
{
lean_object* x_475; lean_object* x_476; 
x_475 = lean_ctor_get(x_446, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_446, 1);
lean_inc(x_476);
lean_dec_ref(x_446);
x_6 = x_475;
x_7 = x_476;
goto block_21;
}
}
block_396:
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_357 = lean_ctor_get(x_353, 0);
lean_inc_ref(x_357);
x_358 = lean_ctor_get(x_357, 3);
lean_inc_ref(x_358);
lean_dec_ref(x_357);
x_359 = lean_ctor_get(x_358, 1);
lean_inc_ref(x_359);
lean_dec_ref(x_358);
x_360 = lean_ctor_get(x_359, 0);
lean_inc_ref(x_360);
x_361 = lean_ctor_get(x_359, 4);
lean_inc_ref(x_361);
lean_dec_ref(x_359);
x_362 = l_Lean_LeanOptions_ofArray(x_360);
lean_dec_ref(x_360);
x_363 = l_Lean_LeanOptions_appendArray(x_362, x_361);
lean_dec_ref(x_361);
x_364 = lean_alloc_closure((void*)(l_Lake_setupExternalModule), 10, 3);
lean_closure_set(x_364, 0, x_2);
lean_closure_set(x_364, 1, x_355);
lean_closure_set(x_364, 2, x_363);
x_365 = l_Lake_Workspace_runFetchM___redArg(x_353, x_364, x_4, x_356);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec_ref(x_365);
x_368 = lean_ctor_get(x_366, 0);
lean_inc_ref(x_368);
lean_dec(x_366);
x_369 = lean_io_wait(x_368, x_367);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec_ref(x_369);
x_372 = lean_ctor_get(x_370, 0);
lean_inc(x_372);
lean_dec_ref(x_370);
x_373 = l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(x_372);
x_374 = l_Lean_Json_compress(x_373);
x_375 = l_IO_println___at___Lean_printImportsJson_spec__1(x_374, x_371);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_378 = x_375;
} else {
 lean_dec_ref(x_375);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_376);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; uint8_t x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_380 = lean_ctor_get(x_375, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_375, 1);
lean_inc(x_381);
lean_dec_ref(x_375);
x_382 = lean_io_error_to_string(x_380);
x_383 = 1;
x_384 = 0;
x_385 = 3;
x_386 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_386, 0, x_382);
lean_ctor_set_uint8(x_386, sizeof(void*)*1, x_385);
x_387 = l_Lake_OutStream_logEntry(x_341, x_386, x_383, x_384, x_381);
lean_dec_ref(x_386);
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_389 = x_387;
} else {
 lean_dec_ref(x_387);
 x_389 = lean_box(0);
}
x_390 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_389;
 lean_ctor_set_tag(x_391, 1);
}
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_388);
return x_391;
}
}
else
{
lean_object* x_392; lean_object* x_393; 
lean_dec_ref(x_370);
x_392 = lean_ctor_get(x_369, 1);
lean_inc(x_392);
lean_dec_ref(x_369);
x_393 = l_Lake_setupFile___closed__1;
x_22 = x_393;
x_23 = x_392;
goto block_37;
}
}
else
{
lean_object* x_394; lean_object* x_395; 
x_394 = lean_ctor_get(x_365, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_365, 1);
lean_inc(x_395);
lean_dec_ref(x_365);
x_22 = x_394;
x_23 = x_395;
goto block_37;
}
}
}
else
{
lean_object* x_477; uint8_t x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_477 = lean_ctor_get(x_352, 1);
lean_inc(x_477);
lean_dec_ref(x_352);
x_478 = 1;
x_479 = 0;
x_480 = l_Lake_setupFile___closed__4;
x_481 = l_Lake_OutStream_logEntry(x_341, x_480, x_478, x_479, x_477);
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
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_486 = lean_ctor_get(x_338, 1);
lean_inc(x_486);
lean_dec_ref(x_338);
x_487 = lean_ctor_get(x_339, 0);
lean_inc(x_487);
lean_dec_ref(x_339);
x_488 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_487, x_486);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_488, 1);
lean_inc(x_489);
lean_dec_ref(x_488);
x_490 = l_Lake_setupFile___closed__5;
x_491 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_490, x_489);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_492 = lean_ctor_get(x_491, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_493 = x_491;
} else {
 lean_dec_ref(x_491);
 x_493 = lean_box(0);
}
x_494 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_493)) {
 x_495 = lean_alloc_ctor(1, 2, 0);
} else {
 x_495 = x_493;
 lean_ctor_set_tag(x_495, 1);
}
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_492);
return x_495;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; uint8_t x_500; lean_object* x_501; uint8_t x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_496 = lean_ctor_get(x_491, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_491, 1);
lean_inc(x_497);
lean_dec_ref(x_491);
x_498 = lean_io_error_to_string(x_496);
x_499 = 1;
x_500 = 0;
x_501 = lean_box(1);
x_502 = 3;
x_503 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_503, 0, x_498);
lean_ctor_set_uint8(x_503, sizeof(void*)*1, x_502);
x_504 = l_Lake_OutStream_logEntry(x_501, x_503, x_499, x_500, x_497);
lean_dec_ref(x_503);
x_505 = lean_ctor_get(x_504, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 lean_ctor_release(x_504, 1);
 x_506 = x_504;
} else {
 lean_dec_ref(x_504);
 x_506 = lean_box(0);
}
x_507 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_506)) {
 x_508 = lean_alloc_ctor(1, 2, 0);
} else {
 x_508 = x_506;
 lean_ctor_set_tag(x_508, 1);
}
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_505);
return x_508;
}
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_509 = lean_ctor_get(x_488, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_488, 1);
lean_inc(x_510);
lean_dec_ref(x_488);
x_511 = lean_io_error_to_string(x_509);
x_512 = 1;
x_513 = 0;
x_514 = lean_box(1);
x_515 = 3;
x_516 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_516, 0, x_511);
lean_ctor_set_uint8(x_516, sizeof(void*)*1, x_515);
x_517 = l_Lake_OutStream_logEntry(x_514, x_516, x_512, x_513, x_510);
lean_dec_ref(x_516);
x_518 = lean_ctor_get(x_517, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 lean_ctor_release(x_517, 1);
 x_519 = x_517;
} else {
 lean_dec_ref(x_517);
 x_519 = lean_box(0);
}
x_520 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_519)) {
 x_521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_521 = x_519;
 lean_ctor_set_tag(x_521, 1);
}
lean_ctor_set(x_521, 0, x_520);
lean_ctor_set(x_521, 1, x_518);
return x_521;
}
}
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_522 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_522);
lean_dec_ref(x_41);
x_523 = lean_ctor_get(x_522, 4);
lean_inc_ref(x_523);
lean_dec_ref(x_522);
x_524 = lean_ctor_get(x_523, 0);
lean_inc_ref(x_524);
lean_dec_ref(x_523);
x_525 = l_Lake_configModuleName;
x_526 = lean_box(0);
x_527 = lean_box(1);
x_528 = l_Lake_setupFile___closed__6;
x_529 = l_Lake_setupFile___closed__7;
x_530 = lean_array_push(x_529, x_524);
x_531 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_531, 0, x_525);
lean_ctor_set(x_531, 1, x_526);
lean_ctor_set(x_531, 2, x_527);
lean_ctor_set(x_531, 3, x_528);
lean_ctor_set(x_531, 4, x_530);
lean_ctor_set(x_531, 5, x_527);
lean_ctor_set_uint8(x_531, sizeof(void*)*6, x_335);
x_532 = l_Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_2299_(x_531);
x_533 = l_Lean_Json_compress(x_532);
x_534 = l_IO_println___at___Lean_printImportsJson_spec__1(x_533, x_332);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_537 = x_534;
} else {
 lean_dec_ref(x_534);
 x_537 = lean_box(0);
}
if (lean_is_scalar(x_537)) {
 x_538 = lean_alloc_ctor(0, 2, 0);
} else {
 x_538 = x_537;
}
lean_ctor_set(x_538, 0, x_535);
lean_ctor_set(x_538, 1, x_536);
return x_538;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; uint8_t x_543; lean_object* x_544; uint8_t x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_539 = lean_ctor_get(x_534, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_534, 1);
lean_inc(x_540);
lean_dec_ref(x_534);
x_541 = lean_io_error_to_string(x_539);
x_542 = 1;
x_543 = 0;
x_544 = lean_box(1);
x_545 = 3;
x_546 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_546, 0, x_541);
lean_ctor_set_uint8(x_546, sizeof(void*)*1, x_545);
x_547 = l_Lake_OutStream_logEntry(x_544, x_546, x_542, x_543, x_540);
lean_dec_ref(x_546);
x_548 = lean_ctor_get(x_547, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_549 = x_547;
} else {
 lean_dec_ref(x_547);
 x_549 = lean_box(0);
}
x_550 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_549)) {
 x_551 = lean_alloc_ctor(1, 2, 0);
} else {
 x_551 = x_549;
 lean_ctor_set_tag(x_551, 1);
}
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_548);
return x_551;
}
}
}
else
{
lean_object* x_552; lean_object* x_553; 
lean_dec(x_331);
lean_dec_ref(x_41);
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_552 = l_Lake_setupFile___boxed__const__2;
x_553 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_332);
return x_553;
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
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_setupFile___lam__1(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
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
