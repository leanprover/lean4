// Lean compiler output
// Module: Lake.Config.Env
// Imports: Init Lake.Util.Name Lake.Util.NativeLib Lake.Config.InstallPath
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
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__16;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__8;
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__10;
lean_object* l_Lean_Json_compress(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__23;
static lean_object* l_Lake_Env_baseVars___closed__1;
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object*);
lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__22;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__20;
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__15;
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_instInhabitedEnv___closed__2;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__3;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__18;
static lean_object* l_Lake_Env_noToolchainVars___closed__6;
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_toolchain;
static lean_object* l_Lake_Env_noToolchainVars___closed__14;
static lean_object* l_Lake_Env_noToolchainVars___closed__4;
static lean_object* l_Lake_Env_noToolchainVars___closed__5;
static lean_object* l_Lake_Env_compute___closed__9;
LEAN_EXPORT lean_object* l_Lake_Env_compute_getUrlD___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__11;
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___lambda__1(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__2;
static lean_object* l_Lake_Env_noToolchainVars___closed__17;
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__13;
static lean_object* l_Lake_instInhabitedEnv___closed__4;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_noToolchainVars;
static lean_object* l_Lake_Env_noToolchainVars___closed__9;
LEAN_EXPORT lean_object* l_Lake_Env_compute_computePkgUrlMap(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute_getUrlD(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lake_getSearchPath(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute_computePkgUrlMap___closed__2;
static lean_object* l_Lake_Env_noToolchainVars___closed__19;
LEAN_EXPORT lean_object* l_Lake_Env_toolchain___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute___closed__8;
static lean_object* l_Lake_Env_noToolchainVars___closed__1;
static lean_object* l_Lake_Env_compute___closed__2;
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
static lean_object* l_Lake_Env_compute___closed__4;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lake_envToBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__7;
static lean_object* l_Lake_Env_baseVars___closed__3;
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute___closed__5;
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object*);
lean_object* l_Lean_Json_Parser_any(lean_object*);
extern lean_object* l_Lake_sharedLibPathEnvVar;
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedEnv;
static lean_object* l_Lake_instInhabitedEnv___closed__1;
static lean_object* l_Lake_Env_compute_computePkgUrlMap___closed__1;
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_Env_compute___closed__1;
static lean_object* l_Lake_Env_compute___closed__3;
LEAN_EXPORT lean_object* l_Lake_Env_toolchain(lean_object*);
static lean_object* l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__21;
static lean_object* l_Lake_instInhabitedEnv___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_Env_baseVars___closed__2;
static lean_object* l_Lake_Env_compute___closed__6;
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object*);
static lean_object* l_Lake_Env_compute___closed__7;
static lean_object* l_Lake_Env_compute___closed__10;
static lean_object* l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__2;
lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute_computePkgUrlMap___closed__3;
lean_object* l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object*);
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_Env_noToolchainVars___closed__12;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___closed__1;
static lean_object* _init_l_Lake_instInhabitedEnv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instInhabitedEnv___closed__1;
x_2 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedEnv___closed__1;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
lean_ctor_set(x_3, 9, x_1);
lean_ctor_set(x_3, 10, x_1);
lean_ctor_set(x_3, 11, x_1);
lean_ctor_set(x_3, 12, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*13, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lake_instInhabitedEnv___closed__2;
x_5 = l_Lake_instInhabitedEnv___closed__3;
x_6 = l_Lake_instInhabitedEnv___closed__1;
x_7 = 0;
x_8 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 5, x_2);
lean_ctor_set(x_8, 6, x_6);
lean_ctor_set(x_8, 7, x_3);
lean_ctor_set(x_8, 8, x_3);
lean_ctor_set(x_8, 9, x_3);
lean_ctor_set(x_8, 10, x_3);
lean_ctor_set_uint8(x_8, sizeof(void*)*11, x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedEnv___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected name", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_String_toName(x_5);
x_14 = l_Lean_Name_isAnonymous(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_12, x_13, x_19);
x_1 = x_20;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_22 = l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__2;
return x_22;
}
}
}
}
}
static lean_object* _init_l_Lake_Env_compute_computePkgUrlMap___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_PKG_URL_MAP", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute_computePkgUrlMap___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute_computePkgUrlMap___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'LAKE_PKG_URL_MAP' has invalid JSON: ", 37, 37);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute_computePkgUrlMap(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_Env_compute_computePkgUrlMap___closed__1;
x_3 = lean_io_getenv(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = l_Lake_Env_compute_computePkgUrlMap___closed__2;
x_15 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lake_Env_compute_computePkgUrlMap___closed__3;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lake_instInhabitedEnv___closed__1;
x_20 = lean_string_append(x_18, x_19);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_20);
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = l_Lean_Json_getObj_x3f(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lake_Env_compute_computePkgUrlMap___closed__3;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lake_instInhabitedEnv___closed__1;
x_27 = lean_string_append(x_25, x_26);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_box(0);
x_30 = l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(x_29, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lake_Env_compute_computePkgUrlMap___closed__3;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lake_instInhabitedEnv___closed__1;
x_35 = lean_string_append(x_33, x_34);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_35);
return x_3;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
lean_ctor_set(x_3, 0, x_36);
return x_3;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_dec(x_3);
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
lean_dec(x_4);
x_39 = l_Lake_Env_compute_computePkgUrlMap___closed__2;
x_40 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_39, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lake_Env_compute_computePkgUrlMap___closed__3;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_44 = l_Lake_instInhabitedEnv___closed__1;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
x_48 = l_Lean_Json_getObj_x3f(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lake_Env_compute_computePkgUrlMap___closed__3;
x_51 = lean_string_append(x_50, x_49);
lean_dec(x_49);
x_52 = l_Lake_instInhabitedEnv___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_37);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_box(0);
x_57 = l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(x_56, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lake_Env_compute_computePkgUrlMap___closed__3;
x_60 = lean_string_append(x_59, x_58);
lean_dec(x_58);
x_61 = l_Lake_instInhabitedEnv___closed__1;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_37);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
lean_dec(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_37);
return x_65;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute_getUrlD(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_io_getenv(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; uint32_t x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_4, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_string_utf8_byte_size(x_12);
x_14 = lean_string_utf8_prev(x_12, x_13);
x_15 = lean_string_utf8_get(x_12, x_14);
lean_dec(x_14);
x_16 = 47;
x_17 = lean_uint32_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_13);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_13);
lean_inc(x_12);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_13);
x_20 = lean_nat_sub(x_13, x_18);
lean_dec(x_13);
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Substring_prevn(x_19, x_21, x_20);
lean_dec(x_19);
x_23 = lean_nat_add(x_18, x_22);
lean_dec(x_22);
x_24 = lean_string_utf8_extract(x_12, x_18, x_23);
lean_dec(x_23);
lean_dec(x_12);
lean_ctor_set(x_4, 0, x_24);
return x_4;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint32_t x_29; uint32_t x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_string_utf8_byte_size(x_26);
x_28 = lean_string_utf8_prev(x_26, x_27);
x_29 = lean_string_utf8_get(x_26, x_28);
lean_dec(x_28);
x_30 = 47;
x_31 = lean_uint32_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_unsigned_to_nat(0u);
lean_inc(x_27);
lean_inc(x_26);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_27);
x_35 = lean_nat_sub(x_27, x_33);
lean_dec(x_27);
x_36 = lean_unsigned_to_nat(1u);
x_37 = l_Substring_prevn(x_34, x_36, x_35);
lean_dec(x_34);
x_38 = lean_nat_add(x_33, x_37);
lean_dec(x_37);
x_39 = lean_string_utf8_extract(x_26, x_33, x_38);
lean_dec(x_38);
lean_dec(x_26);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_25);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute_getUrlD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Env_compute_getUrlD(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_NO_CACHE", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_GITHASH", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ELAN_TOOLCHAIN", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_PATH", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SRC_PATH", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PATH", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("RESERVOIR_API_URL", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/v1", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("RESERVOIR_API_BASE_URL", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("https://reservoir.lean-lang.org/api", 35, 35);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = l_Lake_Env_compute___closed__9;
x_262 = lean_io_getenv(x_261, x_5);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = l_Lake_Env_compute___closed__10;
x_6 = x_265;
x_7 = x_264;
goto block_260;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint32_t x_270; uint32_t x_271; uint8_t x_272; 
x_266 = lean_ctor_get(x_262, 1);
lean_inc(x_266);
lean_dec(x_262);
x_267 = lean_ctor_get(x_263, 0);
lean_inc(x_267);
lean_dec(x_263);
x_268 = lean_string_utf8_byte_size(x_267);
x_269 = lean_string_utf8_prev(x_267, x_268);
x_270 = lean_string_utf8_get(x_267, x_269);
lean_dec(x_269);
x_271 = 47;
x_272 = lean_uint32_dec_eq(x_270, x_271);
if (x_272 == 0)
{
lean_dec(x_268);
x_6 = x_267;
x_7 = x_266;
goto block_260;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_273 = lean_unsigned_to_nat(0u);
lean_inc(x_268);
lean_inc(x_267);
x_274 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_274, 0, x_267);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set(x_274, 2, x_268);
x_275 = lean_nat_sub(x_268, x_273);
lean_dec(x_268);
x_276 = lean_unsigned_to_nat(1u);
x_277 = l_Substring_prevn(x_274, x_276, x_275);
lean_dec(x_274);
x_278 = lean_nat_add(x_273, x_277);
lean_dec(x_277);
x_279 = lean_string_utf8_extract(x_267, x_273, x_278);
lean_dec(x_278);
lean_dec(x_267);
x_6 = x_279;
x_7 = x_266;
goto block_260;
}
}
block_260:
{
lean_object* x_8; 
x_8 = l_Lake_Env_compute_computePkgUrlMap(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_234 = l_Lake_Env_compute___closed__7;
x_235 = lean_io_getenv(x_234, x_10);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = l_Lake_instInhabitedEnv___closed__1;
x_239 = lean_string_append(x_238, x_6);
lean_dec(x_6);
x_240 = l_Lake_Env_compute___closed__8;
x_241 = lean_string_append(x_239, x_240);
x_11 = x_241;
x_12 = x_237;
goto block_233;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint32_t x_246; uint32_t x_247; uint8_t x_248; 
lean_dec(x_6);
x_242 = lean_ctor_get(x_235, 1);
lean_inc(x_242);
lean_dec(x_235);
x_243 = lean_ctor_get(x_236, 0);
lean_inc(x_243);
lean_dec(x_236);
x_244 = lean_string_utf8_byte_size(x_243);
x_245 = lean_string_utf8_prev(x_243, x_244);
x_246 = lean_string_utf8_get(x_243, x_245);
lean_dec(x_245);
x_247 = 47;
x_248 = lean_uint32_dec_eq(x_246, x_247);
if (x_248 == 0)
{
lean_dec(x_244);
x_11 = x_243;
x_12 = x_242;
goto block_233;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_249 = lean_unsigned_to_nat(0u);
lean_inc(x_244);
lean_inc(x_243);
x_250 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_250, 0, x_243);
lean_ctor_set(x_250, 1, x_249);
lean_ctor_set(x_250, 2, x_244);
x_251 = lean_nat_sub(x_244, x_249);
lean_dec(x_244);
x_252 = lean_unsigned_to_nat(1u);
x_253 = l_Substring_prevn(x_250, x_252, x_251);
lean_dec(x_250);
x_254 = lean_nat_add(x_249, x_253);
lean_dec(x_253);
x_255 = lean_string_utf8_extract(x_243, x_249, x_254);
lean_dec(x_254);
lean_dec(x_243);
x_11 = x_255;
x_12 = x_242;
goto block_233;
}
}
block_233:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_13 = l_Lake_Env_compute___closed__1;
x_14 = lean_io_getenv(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lake_Env_compute___closed__2;
x_18 = lean_io_getenv(x_17, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lake_Env_compute___closed__3;
x_22 = lean_io_getenv(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lake_Env_compute___closed__4;
x_26 = l_Lake_getSearchPath(x_25, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lake_Env_compute___closed__5;
x_30 = l_Lake_getSearchPath(x_29, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lake_sharedLibPathEnvVar;
x_34 = l_Lake_getSearchPath(x_33, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lake_Env_compute___closed__6;
x_38 = l_Lake_getSearchPath(x_37, x_36);
if (lean_obj_tag(x_19) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = l_Lake_instInhabitedEnv___closed__1;
x_42 = 0;
x_43 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_2);
lean_ctor_set(x_43, 2, x_3);
lean_ctor_set(x_43, 3, x_11);
lean_ctor_set(x_43, 4, x_41);
lean_ctor_set(x_43, 5, x_9);
lean_ctor_set(x_43, 6, x_41);
lean_ctor_set(x_43, 7, x_27);
lean_ctor_set(x_43, 8, x_31);
lean_ctor_set(x_43, 9, x_35);
lean_ctor_set(x_43, 10, x_40);
lean_ctor_set_uint8(x_43, sizeof(void*)*11, x_42);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = l_Lake_instInhabitedEnv___closed__1;
x_47 = 0;
x_48 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_2);
lean_ctor_set(x_48, 2, x_3);
lean_ctor_set(x_48, 3, x_11);
lean_ctor_set(x_48, 4, x_46);
lean_ctor_set(x_48, 5, x_9);
lean_ctor_set(x_48, 6, x_46);
lean_ctor_set(x_48, 7, x_27);
lean_ctor_set(x_48, 8, x_31);
lean_ctor_set(x_48, 9, x_35);
lean_ctor_set(x_48, 10, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*11, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_38);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get(x_23, 0);
lean_inc(x_52);
lean_dec(x_23);
x_53 = l_Lake_instInhabitedEnv___closed__1;
x_54 = 0;
x_55 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_2);
lean_ctor_set(x_55, 2, x_3);
lean_ctor_set(x_55, 3, x_11);
lean_ctor_set(x_55, 4, x_53);
lean_ctor_set(x_55, 5, x_9);
lean_ctor_set(x_55, 6, x_52);
lean_ctor_set(x_55, 7, x_27);
lean_ctor_set(x_55, 8, x_31);
lean_ctor_set(x_55, 9, x_35);
lean_ctor_set(x_55, 10, x_51);
lean_ctor_set_uint8(x_55, sizeof(void*)*11, x_54);
lean_ctor_set(x_38, 0, x_55);
return x_38;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_38, 0);
x_57 = lean_ctor_get(x_38, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_38);
x_58 = lean_ctor_get(x_23, 0);
lean_inc(x_58);
lean_dec(x_23);
x_59 = l_Lake_instInhabitedEnv___closed__1;
x_60 = 0;
x_61 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_2);
lean_ctor_set(x_61, 2, x_3);
lean_ctor_set(x_61, 3, x_11);
lean_ctor_set(x_61, 4, x_59);
lean_ctor_set(x_61, 5, x_9);
lean_ctor_set(x_61, 6, x_58);
lean_ctor_set(x_61, 7, x_27);
lean_ctor_set(x_61, 8, x_31);
lean_ctor_set(x_61, 9, x_35);
lean_ctor_set(x_61, 10, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*11, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_38, 0);
x_65 = lean_ctor_get(x_15, 0);
lean_inc(x_65);
lean_dec(x_15);
x_66 = l_Lake_envToBool_x3f(x_65);
if (lean_obj_tag(x_66) == 0)
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_67 = l_Lake_instInhabitedEnv___closed__1;
x_68 = 0;
x_69 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_2);
lean_ctor_set(x_69, 2, x_3);
lean_ctor_set(x_69, 3, x_11);
lean_ctor_set(x_69, 4, x_67);
lean_ctor_set(x_69, 5, x_9);
lean_ctor_set(x_69, 6, x_67);
lean_ctor_set(x_69, 7, x_27);
lean_ctor_set(x_69, 8, x_31);
lean_ctor_set(x_69, 9, x_35);
lean_ctor_set(x_69, 10, x_64);
lean_ctor_set_uint8(x_69, sizeof(void*)*11, x_68);
lean_ctor_set(x_38, 0, x_69);
return x_38;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_23, 0);
lean_inc(x_70);
lean_dec(x_23);
x_71 = l_Lake_instInhabitedEnv___closed__1;
x_72 = 0;
x_73 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_2);
lean_ctor_set(x_73, 2, x_3);
lean_ctor_set(x_73, 3, x_11);
lean_ctor_set(x_73, 4, x_71);
lean_ctor_set(x_73, 5, x_9);
lean_ctor_set(x_73, 6, x_70);
lean_ctor_set(x_73, 7, x_27);
lean_ctor_set(x_73, 8, x_31);
lean_ctor_set(x_73, 9, x_35);
lean_ctor_set(x_73, 10, x_64);
lean_ctor_set_uint8(x_73, sizeof(void*)*11, x_72);
lean_ctor_set(x_38, 0, x_73);
return x_38;
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
lean_dec(x_66);
x_75 = l_Lake_instInhabitedEnv___closed__1;
x_76 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_2);
lean_ctor_set(x_76, 2, x_3);
lean_ctor_set(x_76, 3, x_11);
lean_ctor_set(x_76, 4, x_75);
lean_ctor_set(x_76, 5, x_9);
lean_ctor_set(x_76, 6, x_75);
lean_ctor_set(x_76, 7, x_27);
lean_ctor_set(x_76, 8, x_31);
lean_ctor_set(x_76, 9, x_35);
lean_ctor_set(x_76, 10, x_64);
x_77 = lean_unbox(x_74);
lean_dec(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*11, x_77);
lean_ctor_set(x_38, 0, x_76);
return x_38;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_66, 0);
lean_inc(x_78);
lean_dec(x_66);
x_79 = lean_ctor_get(x_23, 0);
lean_inc(x_79);
lean_dec(x_23);
x_80 = l_Lake_instInhabitedEnv___closed__1;
x_81 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_2);
lean_ctor_set(x_81, 2, x_3);
lean_ctor_set(x_81, 3, x_11);
lean_ctor_set(x_81, 4, x_80);
lean_ctor_set(x_81, 5, x_9);
lean_ctor_set(x_81, 6, x_79);
lean_ctor_set(x_81, 7, x_27);
lean_ctor_set(x_81, 8, x_31);
lean_ctor_set(x_81, 9, x_35);
lean_ctor_set(x_81, 10, x_64);
x_82 = lean_unbox(x_78);
lean_dec(x_78);
lean_ctor_set_uint8(x_81, sizeof(void*)*11, x_82);
lean_ctor_set(x_38, 0, x_81);
return x_38;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_38, 0);
x_84 = lean_ctor_get(x_38, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_38);
x_85 = lean_ctor_get(x_15, 0);
lean_inc(x_85);
lean_dec(x_15);
x_86 = l_Lake_envToBool_x3f(x_85);
if (lean_obj_tag(x_86) == 0)
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_87 = l_Lake_instInhabitedEnv___closed__1;
x_88 = 0;
x_89 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_2);
lean_ctor_set(x_89, 2, x_3);
lean_ctor_set(x_89, 3, x_11);
lean_ctor_set(x_89, 4, x_87);
lean_ctor_set(x_89, 5, x_9);
lean_ctor_set(x_89, 6, x_87);
lean_ctor_set(x_89, 7, x_27);
lean_ctor_set(x_89, 8, x_31);
lean_ctor_set(x_89, 9, x_35);
lean_ctor_set(x_89, 10, x_83);
lean_ctor_set_uint8(x_89, sizeof(void*)*11, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_23, 0);
lean_inc(x_91);
lean_dec(x_23);
x_92 = l_Lake_instInhabitedEnv___closed__1;
x_93 = 0;
x_94 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_2);
lean_ctor_set(x_94, 2, x_3);
lean_ctor_set(x_94, 3, x_11);
lean_ctor_set(x_94, 4, x_92);
lean_ctor_set(x_94, 5, x_9);
lean_ctor_set(x_94, 6, x_91);
lean_ctor_set(x_94, 7, x_27);
lean_ctor_set(x_94, 8, x_31);
lean_ctor_set(x_94, 9, x_35);
lean_ctor_set(x_94, 10, x_83);
lean_ctor_set_uint8(x_94, sizeof(void*)*11, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_84);
return x_95;
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_86, 0);
lean_inc(x_96);
lean_dec(x_86);
x_97 = l_Lake_instInhabitedEnv___closed__1;
x_98 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_2);
lean_ctor_set(x_98, 2, x_3);
lean_ctor_set(x_98, 3, x_11);
lean_ctor_set(x_98, 4, x_97);
lean_ctor_set(x_98, 5, x_9);
lean_ctor_set(x_98, 6, x_97);
lean_ctor_set(x_98, 7, x_27);
lean_ctor_set(x_98, 8, x_31);
lean_ctor_set(x_98, 9, x_35);
lean_ctor_set(x_98, 10, x_83);
x_99 = lean_unbox(x_96);
lean_dec(x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*11, x_99);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_84);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_86, 0);
lean_inc(x_101);
lean_dec(x_86);
x_102 = lean_ctor_get(x_23, 0);
lean_inc(x_102);
lean_dec(x_23);
x_103 = l_Lake_instInhabitedEnv___closed__1;
x_104 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_2);
lean_ctor_set(x_104, 2, x_3);
lean_ctor_set(x_104, 3, x_11);
lean_ctor_set(x_104, 4, x_103);
lean_ctor_set(x_104, 5, x_9);
lean_ctor_set(x_104, 6, x_102);
lean_ctor_set(x_104, 7, x_27);
lean_ctor_set(x_104, 8, x_31);
lean_ctor_set(x_104, 9, x_35);
lean_ctor_set(x_104, 10, x_83);
x_105 = lean_unbox(x_101);
lean_dec(x_101);
lean_ctor_set_uint8(x_104, sizeof(void*)*11, x_105);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_84);
return x_106;
}
}
}
}
}
else
{
lean_dec(x_15);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_38);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_38, 0);
x_109 = lean_ctor_get(x_4, 0);
x_110 = l_Lake_instInhabitedEnv___closed__1;
x_111 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_2);
lean_ctor_set(x_111, 2, x_3);
lean_ctor_set(x_111, 3, x_11);
lean_ctor_set(x_111, 4, x_110);
lean_ctor_set(x_111, 5, x_9);
lean_ctor_set(x_111, 6, x_110);
lean_ctor_set(x_111, 7, x_27);
lean_ctor_set(x_111, 8, x_31);
lean_ctor_set(x_111, 9, x_35);
lean_ctor_set(x_111, 10, x_108);
x_112 = lean_unbox(x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*11, x_112);
lean_ctor_set(x_38, 0, x_111);
return x_38;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_113 = lean_ctor_get(x_38, 0);
x_114 = lean_ctor_get(x_38, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_38);
x_115 = lean_ctor_get(x_4, 0);
x_116 = l_Lake_instInhabitedEnv___closed__1;
x_117 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_117, 0, x_1);
lean_ctor_set(x_117, 1, x_2);
lean_ctor_set(x_117, 2, x_3);
lean_ctor_set(x_117, 3, x_11);
lean_ctor_set(x_117, 4, x_116);
lean_ctor_set(x_117, 5, x_9);
lean_ctor_set(x_117, 6, x_116);
lean_ctor_set(x_117, 7, x_27);
lean_ctor_set(x_117, 8, x_31);
lean_ctor_set(x_117, 9, x_35);
lean_ctor_set(x_117, 10, x_113);
x_118 = lean_unbox(x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*11, x_118);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_114);
return x_119;
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_38);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_38, 0);
x_122 = lean_ctor_get(x_4, 0);
x_123 = lean_ctor_get(x_23, 0);
lean_inc(x_123);
lean_dec(x_23);
x_124 = l_Lake_instInhabitedEnv___closed__1;
x_125 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_125, 0, x_1);
lean_ctor_set(x_125, 1, x_2);
lean_ctor_set(x_125, 2, x_3);
lean_ctor_set(x_125, 3, x_11);
lean_ctor_set(x_125, 4, x_124);
lean_ctor_set(x_125, 5, x_9);
lean_ctor_set(x_125, 6, x_123);
lean_ctor_set(x_125, 7, x_27);
lean_ctor_set(x_125, 8, x_31);
lean_ctor_set(x_125, 9, x_35);
lean_ctor_set(x_125, 10, x_121);
x_126 = lean_unbox(x_122);
lean_ctor_set_uint8(x_125, sizeof(void*)*11, x_126);
lean_ctor_set(x_38, 0, x_125);
return x_38;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; 
x_127 = lean_ctor_get(x_38, 0);
x_128 = lean_ctor_get(x_38, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_38);
x_129 = lean_ctor_get(x_4, 0);
x_130 = lean_ctor_get(x_23, 0);
lean_inc(x_130);
lean_dec(x_23);
x_131 = l_Lake_instInhabitedEnv___closed__1;
x_132 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_132, 0, x_1);
lean_ctor_set(x_132, 1, x_2);
lean_ctor_set(x_132, 2, x_3);
lean_ctor_set(x_132, 3, x_11);
lean_ctor_set(x_132, 4, x_131);
lean_ctor_set(x_132, 5, x_9);
lean_ctor_set(x_132, 6, x_130);
lean_ctor_set(x_132, 7, x_27);
lean_ctor_set(x_132, 8, x_31);
lean_ctor_set(x_132, 9, x_35);
lean_ctor_set(x_132, 10, x_127);
x_133 = lean_unbox(x_129);
lean_ctor_set_uint8(x_132, sizeof(void*)*11, x_133);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_128);
return x_134;
}
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_38);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_38, 0);
x_137 = lean_ctor_get(x_19, 0);
lean_inc(x_137);
lean_dec(x_19);
x_138 = 0;
x_139 = l_Lake_instInhabitedEnv___closed__1;
x_140 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_140, 0, x_1);
lean_ctor_set(x_140, 1, x_2);
lean_ctor_set(x_140, 2, x_3);
lean_ctor_set(x_140, 3, x_11);
lean_ctor_set(x_140, 4, x_137);
lean_ctor_set(x_140, 5, x_9);
lean_ctor_set(x_140, 6, x_139);
lean_ctor_set(x_140, 7, x_27);
lean_ctor_set(x_140, 8, x_31);
lean_ctor_set(x_140, 9, x_35);
lean_ctor_set(x_140, 10, x_136);
lean_ctor_set_uint8(x_140, sizeof(void*)*11, x_138);
lean_ctor_set(x_38, 0, x_140);
return x_38;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = lean_ctor_get(x_38, 0);
x_142 = lean_ctor_get(x_38, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_38);
x_143 = lean_ctor_get(x_19, 0);
lean_inc(x_143);
lean_dec(x_19);
x_144 = 0;
x_145 = l_Lake_instInhabitedEnv___closed__1;
x_146 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_146, 0, x_1);
lean_ctor_set(x_146, 1, x_2);
lean_ctor_set(x_146, 2, x_3);
lean_ctor_set(x_146, 3, x_11);
lean_ctor_set(x_146, 4, x_143);
lean_ctor_set(x_146, 5, x_9);
lean_ctor_set(x_146, 6, x_145);
lean_ctor_set(x_146, 7, x_27);
lean_ctor_set(x_146, 8, x_31);
lean_ctor_set(x_146, 9, x_35);
lean_ctor_set(x_146, 10, x_141);
lean_ctor_set_uint8(x_146, sizeof(void*)*11, x_144);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_142);
return x_147;
}
}
else
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_38);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; 
x_149 = lean_ctor_get(x_38, 0);
x_150 = lean_ctor_get(x_19, 0);
lean_inc(x_150);
lean_dec(x_19);
x_151 = lean_ctor_get(x_23, 0);
lean_inc(x_151);
lean_dec(x_23);
x_152 = 0;
x_153 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_153, 0, x_1);
lean_ctor_set(x_153, 1, x_2);
lean_ctor_set(x_153, 2, x_3);
lean_ctor_set(x_153, 3, x_11);
lean_ctor_set(x_153, 4, x_150);
lean_ctor_set(x_153, 5, x_9);
lean_ctor_set(x_153, 6, x_151);
lean_ctor_set(x_153, 7, x_27);
lean_ctor_set(x_153, 8, x_31);
lean_ctor_set(x_153, 9, x_35);
lean_ctor_set(x_153, 10, x_149);
lean_ctor_set_uint8(x_153, sizeof(void*)*11, x_152);
lean_ctor_set(x_38, 0, x_153);
return x_38;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; 
x_154 = lean_ctor_get(x_38, 0);
x_155 = lean_ctor_get(x_38, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_38);
x_156 = lean_ctor_get(x_19, 0);
lean_inc(x_156);
lean_dec(x_19);
x_157 = lean_ctor_get(x_23, 0);
lean_inc(x_157);
lean_dec(x_23);
x_158 = 0;
x_159 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_159, 0, x_1);
lean_ctor_set(x_159, 1, x_2);
lean_ctor_set(x_159, 2, x_3);
lean_ctor_set(x_159, 3, x_11);
lean_ctor_set(x_159, 4, x_156);
lean_ctor_set(x_159, 5, x_9);
lean_ctor_set(x_159, 6, x_157);
lean_ctor_set(x_159, 7, x_27);
lean_ctor_set(x_159, 8, x_31);
lean_ctor_set(x_159, 9, x_35);
lean_ctor_set(x_159, 10, x_154);
lean_ctor_set_uint8(x_159, sizeof(void*)*11, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_155);
return x_160;
}
}
}
else
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_38);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_38, 0);
x_163 = lean_ctor_get(x_19, 0);
lean_inc(x_163);
lean_dec(x_19);
x_164 = lean_ctor_get(x_15, 0);
lean_inc(x_164);
lean_dec(x_15);
x_165 = l_Lake_envToBool_x3f(x_164);
if (lean_obj_tag(x_165) == 0)
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_166; lean_object* x_167; lean_object* x_168; 
x_166 = 0;
x_167 = l_Lake_instInhabitedEnv___closed__1;
x_168 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_168, 0, x_1);
lean_ctor_set(x_168, 1, x_2);
lean_ctor_set(x_168, 2, x_3);
lean_ctor_set(x_168, 3, x_11);
lean_ctor_set(x_168, 4, x_163);
lean_ctor_set(x_168, 5, x_9);
lean_ctor_set(x_168, 6, x_167);
lean_ctor_set(x_168, 7, x_27);
lean_ctor_set(x_168, 8, x_31);
lean_ctor_set(x_168, 9, x_35);
lean_ctor_set(x_168, 10, x_162);
lean_ctor_set_uint8(x_168, sizeof(void*)*11, x_166);
lean_ctor_set(x_38, 0, x_168);
return x_38;
}
else
{
lean_object* x_169; uint8_t x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_23, 0);
lean_inc(x_169);
lean_dec(x_23);
x_170 = 0;
x_171 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_171, 0, x_1);
lean_ctor_set(x_171, 1, x_2);
lean_ctor_set(x_171, 2, x_3);
lean_ctor_set(x_171, 3, x_11);
lean_ctor_set(x_171, 4, x_163);
lean_ctor_set(x_171, 5, x_9);
lean_ctor_set(x_171, 6, x_169);
lean_ctor_set(x_171, 7, x_27);
lean_ctor_set(x_171, 8, x_31);
lean_ctor_set(x_171, 9, x_35);
lean_ctor_set(x_171, 10, x_162);
lean_ctor_set_uint8(x_171, sizeof(void*)*11, x_170);
lean_ctor_set(x_38, 0, x_171);
return x_38;
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_172 = lean_ctor_get(x_165, 0);
lean_inc(x_172);
lean_dec(x_165);
x_173 = l_Lake_instInhabitedEnv___closed__1;
x_174 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_174, 0, x_1);
lean_ctor_set(x_174, 1, x_2);
lean_ctor_set(x_174, 2, x_3);
lean_ctor_set(x_174, 3, x_11);
lean_ctor_set(x_174, 4, x_163);
lean_ctor_set(x_174, 5, x_9);
lean_ctor_set(x_174, 6, x_173);
lean_ctor_set(x_174, 7, x_27);
lean_ctor_set(x_174, 8, x_31);
lean_ctor_set(x_174, 9, x_35);
lean_ctor_set(x_174, 10, x_162);
x_175 = lean_unbox(x_172);
lean_dec(x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*11, x_175);
lean_ctor_set(x_38, 0, x_174);
return x_38;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_176 = lean_ctor_get(x_165, 0);
lean_inc(x_176);
lean_dec(x_165);
x_177 = lean_ctor_get(x_23, 0);
lean_inc(x_177);
lean_dec(x_23);
x_178 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_178, 0, x_1);
lean_ctor_set(x_178, 1, x_2);
lean_ctor_set(x_178, 2, x_3);
lean_ctor_set(x_178, 3, x_11);
lean_ctor_set(x_178, 4, x_163);
lean_ctor_set(x_178, 5, x_9);
lean_ctor_set(x_178, 6, x_177);
lean_ctor_set(x_178, 7, x_27);
lean_ctor_set(x_178, 8, x_31);
lean_ctor_set(x_178, 9, x_35);
lean_ctor_set(x_178, 10, x_162);
x_179 = lean_unbox(x_176);
lean_dec(x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*11, x_179);
lean_ctor_set(x_38, 0, x_178);
return x_38;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_38, 0);
x_181 = lean_ctor_get(x_38, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_38);
x_182 = lean_ctor_get(x_19, 0);
lean_inc(x_182);
lean_dec(x_19);
x_183 = lean_ctor_get(x_15, 0);
lean_inc(x_183);
lean_dec(x_15);
x_184 = l_Lake_envToBool_x3f(x_183);
if (lean_obj_tag(x_184) == 0)
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = 0;
x_186 = l_Lake_instInhabitedEnv___closed__1;
x_187 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_187, 0, x_1);
lean_ctor_set(x_187, 1, x_2);
lean_ctor_set(x_187, 2, x_3);
lean_ctor_set(x_187, 3, x_11);
lean_ctor_set(x_187, 4, x_182);
lean_ctor_set(x_187, 5, x_9);
lean_ctor_set(x_187, 6, x_186);
lean_ctor_set(x_187, 7, x_27);
lean_ctor_set(x_187, 8, x_31);
lean_ctor_set(x_187, 9, x_35);
lean_ctor_set(x_187, 10, x_180);
lean_ctor_set_uint8(x_187, sizeof(void*)*11, x_185);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_181);
return x_188;
}
else
{
lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_23, 0);
lean_inc(x_189);
lean_dec(x_23);
x_190 = 0;
x_191 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_191, 0, x_1);
lean_ctor_set(x_191, 1, x_2);
lean_ctor_set(x_191, 2, x_3);
lean_ctor_set(x_191, 3, x_11);
lean_ctor_set(x_191, 4, x_182);
lean_ctor_set(x_191, 5, x_9);
lean_ctor_set(x_191, 6, x_189);
lean_ctor_set(x_191, 7, x_27);
lean_ctor_set(x_191, 8, x_31);
lean_ctor_set(x_191, 9, x_35);
lean_ctor_set(x_191, 10, x_180);
lean_ctor_set_uint8(x_191, sizeof(void*)*11, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_181);
return x_192;
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; 
x_193 = lean_ctor_get(x_184, 0);
lean_inc(x_193);
lean_dec(x_184);
x_194 = l_Lake_instInhabitedEnv___closed__1;
x_195 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_195, 0, x_1);
lean_ctor_set(x_195, 1, x_2);
lean_ctor_set(x_195, 2, x_3);
lean_ctor_set(x_195, 3, x_11);
lean_ctor_set(x_195, 4, x_182);
lean_ctor_set(x_195, 5, x_9);
lean_ctor_set(x_195, 6, x_194);
lean_ctor_set(x_195, 7, x_27);
lean_ctor_set(x_195, 8, x_31);
lean_ctor_set(x_195, 9, x_35);
lean_ctor_set(x_195, 10, x_180);
x_196 = lean_unbox(x_193);
lean_dec(x_193);
lean_ctor_set_uint8(x_195, sizeof(void*)*11, x_196);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_181);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; 
x_198 = lean_ctor_get(x_184, 0);
lean_inc(x_198);
lean_dec(x_184);
x_199 = lean_ctor_get(x_23, 0);
lean_inc(x_199);
lean_dec(x_23);
x_200 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_200, 0, x_1);
lean_ctor_set(x_200, 1, x_2);
lean_ctor_set(x_200, 2, x_3);
lean_ctor_set(x_200, 3, x_11);
lean_ctor_set(x_200, 4, x_182);
lean_ctor_set(x_200, 5, x_9);
lean_ctor_set(x_200, 6, x_199);
lean_ctor_set(x_200, 7, x_27);
lean_ctor_set(x_200, 8, x_31);
lean_ctor_set(x_200, 9, x_35);
lean_ctor_set(x_200, 10, x_180);
x_201 = lean_unbox(x_198);
lean_dec(x_198);
lean_ctor_set_uint8(x_200, sizeof(void*)*11, x_201);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_181);
return x_202;
}
}
}
}
}
else
{
lean_dec(x_15);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_38);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_204 = lean_ctor_get(x_38, 0);
x_205 = lean_ctor_get(x_19, 0);
lean_inc(x_205);
lean_dec(x_19);
x_206 = lean_ctor_get(x_4, 0);
x_207 = l_Lake_instInhabitedEnv___closed__1;
x_208 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_208, 0, x_1);
lean_ctor_set(x_208, 1, x_2);
lean_ctor_set(x_208, 2, x_3);
lean_ctor_set(x_208, 3, x_11);
lean_ctor_set(x_208, 4, x_205);
lean_ctor_set(x_208, 5, x_9);
lean_ctor_set(x_208, 6, x_207);
lean_ctor_set(x_208, 7, x_27);
lean_ctor_set(x_208, 8, x_31);
lean_ctor_set(x_208, 9, x_35);
lean_ctor_set(x_208, 10, x_204);
x_209 = lean_unbox(x_206);
lean_ctor_set_uint8(x_208, sizeof(void*)*11, x_209);
lean_ctor_set(x_38, 0, x_208);
return x_38;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_210 = lean_ctor_get(x_38, 0);
x_211 = lean_ctor_get(x_38, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_38);
x_212 = lean_ctor_get(x_19, 0);
lean_inc(x_212);
lean_dec(x_19);
x_213 = lean_ctor_get(x_4, 0);
x_214 = l_Lake_instInhabitedEnv___closed__1;
x_215 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_215, 0, x_1);
lean_ctor_set(x_215, 1, x_2);
lean_ctor_set(x_215, 2, x_3);
lean_ctor_set(x_215, 3, x_11);
lean_ctor_set(x_215, 4, x_212);
lean_ctor_set(x_215, 5, x_9);
lean_ctor_set(x_215, 6, x_214);
lean_ctor_set(x_215, 7, x_27);
lean_ctor_set(x_215, 8, x_31);
lean_ctor_set(x_215, 9, x_35);
lean_ctor_set(x_215, 10, x_210);
x_216 = lean_unbox(x_213);
lean_ctor_set_uint8(x_215, sizeof(void*)*11, x_216);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_211);
return x_217;
}
}
else
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_38);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_219 = lean_ctor_get(x_38, 0);
x_220 = lean_ctor_get(x_19, 0);
lean_inc(x_220);
lean_dec(x_19);
x_221 = lean_ctor_get(x_4, 0);
x_222 = lean_ctor_get(x_23, 0);
lean_inc(x_222);
lean_dec(x_23);
x_223 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_223, 0, x_1);
lean_ctor_set(x_223, 1, x_2);
lean_ctor_set(x_223, 2, x_3);
lean_ctor_set(x_223, 3, x_11);
lean_ctor_set(x_223, 4, x_220);
lean_ctor_set(x_223, 5, x_9);
lean_ctor_set(x_223, 6, x_222);
lean_ctor_set(x_223, 7, x_27);
lean_ctor_set(x_223, 8, x_31);
lean_ctor_set(x_223, 9, x_35);
lean_ctor_set(x_223, 10, x_219);
x_224 = lean_unbox(x_221);
lean_ctor_set_uint8(x_223, sizeof(void*)*11, x_224);
lean_ctor_set(x_38, 0, x_223);
return x_38;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; 
x_225 = lean_ctor_get(x_38, 0);
x_226 = lean_ctor_get(x_38, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_38);
x_227 = lean_ctor_get(x_19, 0);
lean_inc(x_227);
lean_dec(x_19);
x_228 = lean_ctor_get(x_4, 0);
x_229 = lean_ctor_get(x_23, 0);
lean_inc(x_229);
lean_dec(x_23);
x_230 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_230, 0, x_1);
lean_ctor_set(x_230, 1, x_2);
lean_ctor_set(x_230, 2, x_3);
lean_ctor_set(x_230, 3, x_11);
lean_ctor_set(x_230, 4, x_227);
lean_ctor_set(x_230, 5, x_9);
lean_ctor_set(x_230, 6, x_229);
lean_ctor_set(x_230, 7, x_27);
lean_ctor_set(x_230, 8, x_31);
lean_ctor_set(x_230, 9, x_35);
lean_ctor_set(x_230, 10, x_225);
x_231 = lean_unbox(x_228);
lean_ctor_set_uint8(x_230, sizeof(void*)*11, x_231);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_226);
return x_232;
}
}
}
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_256 = !lean_is_exclusive(x_8);
if (x_256 == 0)
{
return x_8;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_8, 0);
x_258 = lean_ctor_get(x_8, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_8);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Env_compute(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_leanGithash(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_toolchain(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 6);
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_toolchain;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_toolchain___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_toolchain(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_4, 6);
x_6 = lean_string_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 10);
lean_inc(x_7);
lean_inc(x_5);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_inc(x_3);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 10);
lean_inc(x_10);
lean_inc(x_5);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_path(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_ctor_get(x_1, 7);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_leanPath(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_1, 8);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_leanSrcPath(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lake_LeanInstall_sharedLibPath(x_2);
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 9);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_List_appendTR___rarg(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_compute___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_noToolchainVars___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_OVERRIDE_LEAN", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_noToolchainVars___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_HOME", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_noToolchainVars___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_noToolchainVars___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_compute___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SYSROOT", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_noToolchainVars___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_AR", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_noToolchainVars___closed__13;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_noToolchainVars___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__12;
x_2 = l_Lake_Env_noToolchainVars___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__10;
x_2 = l_Lake_Env_noToolchainVars___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__9;
x_2 = l_Lake_Env_noToolchainVars___closed__17;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__7;
x_2 = l_Lake_Env_noToolchainVars___closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__5;
x_2 = l_Lake_Env_noToolchainVars___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__3;
x_2 = l_Lake_Env_noToolchainVars___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__1;
x_2 = l_Lake_Env_noToolchainVars___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Env_noToolchainVars___closed__22;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Env_noToolchainVars___closed__23;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(x_1, x_3);
x_8 = 1;
x_9 = l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___closed__1;
x_10 = l_Lean_Name_toString(x_4, x_8, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_12 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_7, x_10, x_11);
x_1 = x_12;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_CC", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ELAN", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ELAN_HOME", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_3 = l_Lake_Env_toolchain(x_1);
x_4 = lean_string_utf8_byte_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 4);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lake_Env_noToolchainVars___closed__2;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_14 = l_Lake_Env_noToolchainVars___closed__6;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
x_17 = lean_box(0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 7);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 11);
lean_inc(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = l_Lake_Env_noToolchainVars___closed__8;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lake_Env_leanGithash(x_1);
lean_dec(x_1);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lake_Env_compute___closed__2;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_19);
x_30 = l_Lake_Env_noToolchainVars___closed__11;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_21);
x_33 = l_Lake_Env_noToolchainVars___closed__13;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lake_LeanInstall_leanCc_x3f(x_18);
lean_dec(x_18);
x_36 = l_Lake_Env_baseVars___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_42);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_89; 
x_89 = lean_box(0);
x_44 = x_89;
goto block_88;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_2, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_44 = x_92;
goto block_88;
}
block_88:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = l_Lake_Env_baseVars___closed__2;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_81; 
x_81 = lean_box(0);
x_47 = x_81;
goto block_80;
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_2);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_2, 0);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
lean_ctor_set(x_2, 0, x_84);
x_47 = x_2;
goto block_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_2, 0);
lean_inc(x_85);
lean_dec(x_2);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_47 = x_87;
goto block_80;
}
}
block_80:
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lake_Env_baseVars___closed__3;
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
if (x_6 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_3);
x_51 = l_Lake_Env_compute___closed__3;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(x_17, x_16);
x_54 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_Json_compress(x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lake_Env_compute_computePkgUrlMap___closed__1;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_43);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_15);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_12);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_46);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_array_mk(x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_3);
x_66 = l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(x_17, x_16);
x_67 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lean_Json_compress(x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lake_Env_compute_computePkgUrlMap___closed__1;
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_43);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_15);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_12);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lake_Env_noToolchainVars___closed__1;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_49);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_46);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_array_mk(x_78);
return x_79;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_1);
x_2 = l_Lake_Env_baseVars(x_1);
x_3 = l_Lake_Env_leanPath(x_1);
x_4 = l_System_SearchPath_toString(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lake_Env_compute___closed__4;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lake_Env_leanSrcPath(x_1);
x_9 = l_System_SearchPath_toString(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lake_Env_compute___closed__5;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lake_Env_path(x_1);
x_14 = l_System_SearchPath_toString(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lake_Env_compute___closed__6;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_mk(x_21);
x_23 = l_Array_append___rarg(x_2, x_22);
lean_dec(x_22);
x_24 = l_System_Platform_isWindows;
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = l_Lake_Env_sharedLibPath(x_1);
x_26 = l_System_SearchPath_toString(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lake_sharedLibPathEnvVar;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_array_push(x_23, x_29);
return x_30;
}
else
{
lean_dec(x_1);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_4, 3);
x_6 = l_Lake_Env_leanPath(x_1);
lean_inc(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_3);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_leanSearchPath(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Env(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_NativeLib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InstallPath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedEnv___closed__1 = _init_l_Lake_instInhabitedEnv___closed__1();
lean_mark_persistent(l_Lake_instInhabitedEnv___closed__1);
l_Lake_instInhabitedEnv___closed__2 = _init_l_Lake_instInhabitedEnv___closed__2();
lean_mark_persistent(l_Lake_instInhabitedEnv___closed__2);
l_Lake_instInhabitedEnv___closed__3 = _init_l_Lake_instInhabitedEnv___closed__3();
lean_mark_persistent(l_Lake_instInhabitedEnv___closed__3);
l_Lake_instInhabitedEnv___closed__4 = _init_l_Lake_instInhabitedEnv___closed__4();
lean_mark_persistent(l_Lake_instInhabitedEnv___closed__4);
l_Lake_instInhabitedEnv = _init_l_Lake_instInhabitedEnv();
lean_mark_persistent(l_Lake_instInhabitedEnv);
l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__1 = _init_l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__1();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__1);
l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__2 = _init_l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__2();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__2);
l_Lake_Env_compute_computePkgUrlMap___closed__1 = _init_l_Lake_Env_compute_computePkgUrlMap___closed__1();
lean_mark_persistent(l_Lake_Env_compute_computePkgUrlMap___closed__1);
l_Lake_Env_compute_computePkgUrlMap___closed__2 = _init_l_Lake_Env_compute_computePkgUrlMap___closed__2();
lean_mark_persistent(l_Lake_Env_compute_computePkgUrlMap___closed__2);
l_Lake_Env_compute_computePkgUrlMap___closed__3 = _init_l_Lake_Env_compute_computePkgUrlMap___closed__3();
lean_mark_persistent(l_Lake_Env_compute_computePkgUrlMap___closed__3);
l_Lake_Env_compute___closed__1 = _init_l_Lake_Env_compute___closed__1();
lean_mark_persistent(l_Lake_Env_compute___closed__1);
l_Lake_Env_compute___closed__2 = _init_l_Lake_Env_compute___closed__2();
lean_mark_persistent(l_Lake_Env_compute___closed__2);
l_Lake_Env_compute___closed__3 = _init_l_Lake_Env_compute___closed__3();
lean_mark_persistent(l_Lake_Env_compute___closed__3);
l_Lake_Env_compute___closed__4 = _init_l_Lake_Env_compute___closed__4();
lean_mark_persistent(l_Lake_Env_compute___closed__4);
l_Lake_Env_compute___closed__5 = _init_l_Lake_Env_compute___closed__5();
lean_mark_persistent(l_Lake_Env_compute___closed__5);
l_Lake_Env_compute___closed__6 = _init_l_Lake_Env_compute___closed__6();
lean_mark_persistent(l_Lake_Env_compute___closed__6);
l_Lake_Env_compute___closed__7 = _init_l_Lake_Env_compute___closed__7();
lean_mark_persistent(l_Lake_Env_compute___closed__7);
l_Lake_Env_compute___closed__8 = _init_l_Lake_Env_compute___closed__8();
lean_mark_persistent(l_Lake_Env_compute___closed__8);
l_Lake_Env_compute___closed__9 = _init_l_Lake_Env_compute___closed__9();
lean_mark_persistent(l_Lake_Env_compute___closed__9);
l_Lake_Env_compute___closed__10 = _init_l_Lake_Env_compute___closed__10();
lean_mark_persistent(l_Lake_Env_compute___closed__10);
l_Lake_Env_noToolchainVars___closed__1 = _init_l_Lake_Env_noToolchainVars___closed__1();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__1);
l_Lake_Env_noToolchainVars___closed__2 = _init_l_Lake_Env_noToolchainVars___closed__2();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__2);
l_Lake_Env_noToolchainVars___closed__3 = _init_l_Lake_Env_noToolchainVars___closed__3();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__3);
l_Lake_Env_noToolchainVars___closed__4 = _init_l_Lake_Env_noToolchainVars___closed__4();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__4);
l_Lake_Env_noToolchainVars___closed__5 = _init_l_Lake_Env_noToolchainVars___closed__5();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__5);
l_Lake_Env_noToolchainVars___closed__6 = _init_l_Lake_Env_noToolchainVars___closed__6();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__6);
l_Lake_Env_noToolchainVars___closed__7 = _init_l_Lake_Env_noToolchainVars___closed__7();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__7);
l_Lake_Env_noToolchainVars___closed__8 = _init_l_Lake_Env_noToolchainVars___closed__8();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__8);
l_Lake_Env_noToolchainVars___closed__9 = _init_l_Lake_Env_noToolchainVars___closed__9();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__9);
l_Lake_Env_noToolchainVars___closed__10 = _init_l_Lake_Env_noToolchainVars___closed__10();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__10);
l_Lake_Env_noToolchainVars___closed__11 = _init_l_Lake_Env_noToolchainVars___closed__11();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__11);
l_Lake_Env_noToolchainVars___closed__12 = _init_l_Lake_Env_noToolchainVars___closed__12();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__12);
l_Lake_Env_noToolchainVars___closed__13 = _init_l_Lake_Env_noToolchainVars___closed__13();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__13);
l_Lake_Env_noToolchainVars___closed__14 = _init_l_Lake_Env_noToolchainVars___closed__14();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__14);
l_Lake_Env_noToolchainVars___closed__15 = _init_l_Lake_Env_noToolchainVars___closed__15();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__15);
l_Lake_Env_noToolchainVars___closed__16 = _init_l_Lake_Env_noToolchainVars___closed__16();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__16);
l_Lake_Env_noToolchainVars___closed__17 = _init_l_Lake_Env_noToolchainVars___closed__17();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__17);
l_Lake_Env_noToolchainVars___closed__18 = _init_l_Lake_Env_noToolchainVars___closed__18();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__18);
l_Lake_Env_noToolchainVars___closed__19 = _init_l_Lake_Env_noToolchainVars___closed__19();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__19);
l_Lake_Env_noToolchainVars___closed__20 = _init_l_Lake_Env_noToolchainVars___closed__20();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__20);
l_Lake_Env_noToolchainVars___closed__21 = _init_l_Lake_Env_noToolchainVars___closed__21();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__21);
l_Lake_Env_noToolchainVars___closed__22 = _init_l_Lake_Env_noToolchainVars___closed__22();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__22);
l_Lake_Env_noToolchainVars___closed__23 = _init_l_Lake_Env_noToolchainVars___closed__23();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__23);
l_Lake_Env_noToolchainVars = _init_l_Lake_Env_noToolchainVars();
lean_mark_persistent(l_Lake_Env_noToolchainVars);
l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___closed__1 = _init_l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___closed__1();
lean_mark_persistent(l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___closed__1);
l_Lake_Env_baseVars___closed__1 = _init_l_Lake_Env_baseVars___closed__1();
lean_mark_persistent(l_Lake_Env_baseVars___closed__1);
l_Lake_Env_baseVars___closed__2 = _init_l_Lake_Env_baseVars___closed__2();
lean_mark_persistent(l_Lake_Env_baseVars___closed__2);
l_Lake_Env_baseVars___closed__3 = _init_l_Lake_Env_baseVars___closed__3();
lean_mark_persistent(l_Lake_Env_baseVars___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
