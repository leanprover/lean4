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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_Env_baseVars___closed__1;
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object*);
lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_Env_baseVars___closed__7;
static lean_object* l_Lake_instInhabitedEnv___closed__2;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_toolchain;
static lean_object* l_Lake_Env_compute___closed__9;
LEAN_EXPORT lean_object* l_Lake_Env_compute_getUrlD___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___lambda__1(lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedEnv___closed__4;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute_computePkgUrlMap(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute_getUrlD(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lake_getSearchPath(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute_computePkgUrlMap___closed__2;
LEAN_EXPORT lean_object* l_Lake_Env_toolchain___boxed(lean_object*);
static lean_object* l_Lake_Env_compute___closed__8;
static lean_object* l_Lake_Env_compute___closed__2;
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
static lean_object* l_Lake_Env_compute___closed__4;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object*);
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
static lean_object* l_Lake_Env_baseVars___closed__5;
static lean_object* l_Lake_Env_compute___closed__1;
static lean_object* l_Lake_Env_compute___closed__3;
LEAN_EXPORT lean_object* l_Lake_Env_toolchain(lean_object*);
static lean_object* l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object*);
static lean_object* l_Lake_instInhabitedEnv___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_Env_baseVars___closed__2;
static lean_object* l_Lake_Env_compute___closed__6;
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object*);
static lean_object* l_Lake_Env_compute___closed__7;
static lean_object* l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1___closed__2;
lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute_computePkgUrlMap___closed__3;
lean_object* l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object*);
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_Env_baseVars___closed__6;
static lean_object* l_Lake_Env_baseVars___closed__4;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lake_instInhabitedEnv___closed__2;
x_5 = l_Lake_instInhabitedEnv___closed__3;
x_6 = l_Lake_instInhabitedEnv___closed__1;
x_7 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set(x_7, 4, x_6);
lean_ctor_set(x_7, 5, x_2);
lean_ctor_set(x_7, 6, x_6);
lean_ctor_set(x_7, 7, x_3);
lean_ctor_set(x_7, 8, x_3);
lean_ctor_set(x_7, 9, x_3);
lean_ctor_set(x_7, 10, x_3);
return x_7;
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
x_1 = lean_mk_string_unchecked("LEAN_GITHASH", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ELAN_TOOLCHAIN", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_PATH", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SRC_PATH", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PATH", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("RESERVOIR_API_URL", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/v1", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("RESERVOIR_API_BASE_URL", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("https://reservoir.lean-lang.org/api", 35, 35);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = l_Lake_Env_compute___closed__8;
x_105 = lean_io_getenv(x_104, x_4);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lake_Env_compute___closed__9;
x_5 = x_108;
x_6 = x_107;
goto block_103;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint32_t x_113; uint32_t x_114; uint8_t x_115; 
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec(x_105);
x_110 = lean_ctor_get(x_106, 0);
lean_inc(x_110);
lean_dec(x_106);
x_111 = lean_string_utf8_byte_size(x_110);
x_112 = lean_string_utf8_prev(x_110, x_111);
x_113 = lean_string_utf8_get(x_110, x_112);
lean_dec(x_112);
x_114 = 47;
x_115 = lean_uint32_dec_eq(x_113, x_114);
if (x_115 == 0)
{
lean_dec(x_111);
x_5 = x_110;
x_6 = x_109;
goto block_103;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_unsigned_to_nat(0u);
lean_inc(x_111);
lean_inc(x_110);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_110);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_111);
x_118 = lean_nat_sub(x_111, x_116);
lean_dec(x_111);
x_119 = lean_unsigned_to_nat(1u);
x_120 = l_Substring_prevn(x_117, x_119, x_118);
lean_dec(x_117);
x_121 = lean_nat_add(x_116, x_120);
lean_dec(x_120);
x_122 = lean_string_utf8_extract(x_110, x_116, x_121);
lean_dec(x_121);
lean_dec(x_110);
x_5 = x_122;
x_6 = x_109;
goto block_103;
}
}
block_103:
{
lean_object* x_7; 
x_7 = l_Lake_Env_compute_computePkgUrlMap(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_77 = l_Lake_Env_compute___closed__6;
x_78 = lean_io_getenv(x_77, x_9);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lake_instInhabitedEnv___closed__1;
x_82 = lean_string_append(x_81, x_5);
lean_dec(x_5);
x_83 = l_Lake_Env_compute___closed__7;
x_84 = lean_string_append(x_82, x_83);
x_10 = x_84;
x_11 = x_80;
goto block_76;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint32_t x_89; uint32_t x_90; uint8_t x_91; 
lean_dec(x_5);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = lean_ctor_get(x_79, 0);
lean_inc(x_86);
lean_dec(x_79);
x_87 = lean_string_utf8_byte_size(x_86);
x_88 = lean_string_utf8_prev(x_86, x_87);
x_89 = lean_string_utf8_get(x_86, x_88);
lean_dec(x_88);
x_90 = 47;
x_91 = lean_uint32_dec_eq(x_89, x_90);
if (x_91 == 0)
{
lean_dec(x_87);
x_10 = x_86;
x_11 = x_85;
goto block_76;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_unsigned_to_nat(0u);
lean_inc(x_87);
lean_inc(x_86);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_86);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_87);
x_94 = lean_nat_sub(x_87, x_92);
lean_dec(x_87);
x_95 = lean_unsigned_to_nat(1u);
x_96 = l_Substring_prevn(x_93, x_95, x_94);
lean_dec(x_93);
x_97 = lean_nat_add(x_92, x_96);
lean_dec(x_96);
x_98 = lean_string_utf8_extract(x_86, x_92, x_97);
lean_dec(x_97);
lean_dec(x_86);
x_10 = x_98;
x_11 = x_85;
goto block_76;
}
}
block_76:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_12 = l_Lake_Env_compute___closed__1;
x_13 = lean_io_getenv(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lake_Env_compute___closed__2;
x_17 = lean_io_getenv(x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lake_Env_compute___closed__3;
x_21 = l_Lake_getSearchPath(x_20, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lake_Env_compute___closed__4;
x_25 = l_Lake_getSearchPath(x_24, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lake_sharedLibPathEnvVar;
x_29 = l_Lake_getSearchPath(x_28, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lake_Env_compute___closed__5;
x_33 = l_Lake_getSearchPath(x_32, x_31);
if (lean_obj_tag(x_14) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = l_Lake_instInhabitedEnv___closed__1;
x_37 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_2);
lean_ctor_set(x_37, 2, x_3);
lean_ctor_set(x_37, 3, x_10);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_8);
lean_ctor_set(x_37, 6, x_36);
lean_ctor_set(x_37, 7, x_22);
lean_ctor_set(x_37, 8, x_26);
lean_ctor_set(x_37, 9, x_30);
lean_ctor_set(x_37, 10, x_35);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = l_Lake_instInhabitedEnv___closed__1;
x_41 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_2);
lean_ctor_set(x_41, 2, x_3);
lean_ctor_set(x_41, 3, x_10);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set(x_41, 5, x_8);
lean_ctor_set(x_41, 6, x_40);
lean_ctor_set(x_41, 7, x_22);
lean_ctor_set(x_41, 8, x_26);
lean_ctor_set(x_41, 9, x_30);
lean_ctor_set(x_41, 10, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_18, 0);
lean_inc(x_45);
lean_dec(x_18);
x_46 = l_Lake_instInhabitedEnv___closed__1;
x_47 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_2);
lean_ctor_set(x_47, 2, x_3);
lean_ctor_set(x_47, 3, x_10);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_47, 5, x_8);
lean_ctor_set(x_47, 6, x_45);
lean_ctor_set(x_47, 7, x_22);
lean_ctor_set(x_47, 8, x_26);
lean_ctor_set(x_47, 9, x_30);
lean_ctor_set(x_47, 10, x_44);
lean_ctor_set(x_33, 0, x_47);
return x_33;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_33, 0);
x_49 = lean_ctor_get(x_33, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_33);
x_50 = lean_ctor_get(x_18, 0);
lean_inc(x_50);
lean_dec(x_18);
x_51 = l_Lake_instInhabitedEnv___closed__1;
x_52 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_2);
lean_ctor_set(x_52, 2, x_3);
lean_ctor_set(x_52, 3, x_10);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_52, 5, x_8);
lean_ctor_set(x_52, 6, x_50);
lean_ctor_set(x_52, 7, x_22);
lean_ctor_set(x_52, 8, x_26);
lean_ctor_set(x_52, 9, x_30);
lean_ctor_set(x_52, 10, x_48);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_33);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_33, 0);
x_56 = lean_ctor_get(x_14, 0);
lean_inc(x_56);
lean_dec(x_14);
x_57 = l_Lake_instInhabitedEnv___closed__1;
x_58 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_2);
lean_ctor_set(x_58, 2, x_3);
lean_ctor_set(x_58, 3, x_10);
lean_ctor_set(x_58, 4, x_56);
lean_ctor_set(x_58, 5, x_8);
lean_ctor_set(x_58, 6, x_57);
lean_ctor_set(x_58, 7, x_22);
lean_ctor_set(x_58, 8, x_26);
lean_ctor_set(x_58, 9, x_30);
lean_ctor_set(x_58, 10, x_55);
lean_ctor_set(x_33, 0, x_58);
return x_33;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_33, 0);
x_60 = lean_ctor_get(x_33, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_33);
x_61 = lean_ctor_get(x_14, 0);
lean_inc(x_61);
lean_dec(x_14);
x_62 = l_Lake_instInhabitedEnv___closed__1;
x_63 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_2);
lean_ctor_set(x_63, 2, x_3);
lean_ctor_set(x_63, 3, x_10);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_8);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_63, 7, x_22);
lean_ctor_set(x_63, 8, x_26);
lean_ctor_set(x_63, 9, x_30);
lean_ctor_set(x_63, 10, x_59);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_33);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_33, 0);
x_67 = lean_ctor_get(x_14, 0);
lean_inc(x_67);
lean_dec(x_14);
x_68 = lean_ctor_get(x_18, 0);
lean_inc(x_68);
lean_dec(x_18);
x_69 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_2);
lean_ctor_set(x_69, 2, x_3);
lean_ctor_set(x_69, 3, x_10);
lean_ctor_set(x_69, 4, x_67);
lean_ctor_set(x_69, 5, x_8);
lean_ctor_set(x_69, 6, x_68);
lean_ctor_set(x_69, 7, x_22);
lean_ctor_set(x_69, 8, x_26);
lean_ctor_set(x_69, 9, x_30);
lean_ctor_set(x_69, 10, x_66);
lean_ctor_set(x_33, 0, x_69);
return x_33;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_33, 0);
x_71 = lean_ctor_get(x_33, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_33);
x_72 = lean_ctor_get(x_14, 0);
lean_inc(x_72);
lean_dec(x_14);
x_73 = lean_ctor_get(x_18, 0);
lean_inc(x_73);
lean_dec(x_18);
x_74 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_2);
lean_ctor_set(x_74, 2, x_3);
lean_ctor_set(x_74, 3, x_10);
lean_ctor_set(x_74, 4, x_72);
lean_ctor_set(x_74, 5, x_8);
lean_ctor_set(x_74, 6, x_73);
lean_ctor_set(x_74, 7, x_22);
lean_ctor_set(x_74, 8, x_26);
lean_ctor_set(x_74, 9, x_30);
lean_ctor_set(x_74, 10, x_70);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_7);
if (x_99 == 0)
{
return x_7;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_7, 0);
x_101 = lean_ctor_get(x_7, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_7);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
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
x_1 = lean_mk_string_unchecked("LAKE", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_HOME", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SYSROOT", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_AR", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_CC", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ELAN_HOME", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__7() {
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
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
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
x_11 = l_Lake_Env_baseVars___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_14 = l_Lake_Env_baseVars___closed__2;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
x_17 = lean_box(0);
x_18 = l_Lake_Env_leanGithash(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lake_Env_compute___closed__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 11);
lean_inc(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_Lake_Env_baseVars___closed__3;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_24);
x_29 = l_Lake_Env_baseVars___closed__4;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lake_LeanInstall_leanCc_x3f(x_22);
lean_dec(x_22);
x_32 = l_Lake_Env_baseVars___closed__5;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_71; 
x_71 = lean_box(0);
x_39 = x_71;
goto block_70;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_2);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
lean_ctor_set(x_2, 0, x_74);
x_39 = x_2;
goto block_70;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_2, 0);
lean_inc(x_75);
lean_dec(x_2);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_39 = x_77;
goto block_70;
}
}
block_70:
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lake_Env_baseVars___closed__6;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
if (x_6 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_3);
x_43 = l_Lake_Env_compute___closed__2;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(x_17, x_16);
x_46 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_Json_compress(x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_Lake_Env_compute_computePkgUrlMap___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_38);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_15);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_array_mk(x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_3);
x_57 = l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(x_17, x_16);
x_58 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l_Lean_Json_compress(x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lake_Env_compute_computePkgUrlMap___closed__1;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_38);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_15);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_12);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lake_Env_baseVars___closed__7;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_41);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_array_mk(x_68);
return x_69;
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
x_6 = l_Lake_Env_compute___closed__3;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lake_Env_leanSrcPath(x_1);
x_9 = l_System_SearchPath_toString(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lake_Env_compute___closed__4;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lake_Env_path(x_1);
x_14 = l_System_SearchPath_toString(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lake_Env_compute___closed__5;
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
l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___closed__1 = _init_l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___closed__1();
lean_mark_persistent(l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1___closed__1);
l_Lake_Env_baseVars___closed__1 = _init_l_Lake_Env_baseVars___closed__1();
lean_mark_persistent(l_Lake_Env_baseVars___closed__1);
l_Lake_Env_baseVars___closed__2 = _init_l_Lake_Env_baseVars___closed__2();
lean_mark_persistent(l_Lake_Env_baseVars___closed__2);
l_Lake_Env_baseVars___closed__3 = _init_l_Lake_Env_baseVars___closed__3();
lean_mark_persistent(l_Lake_Env_baseVars___closed__3);
l_Lake_Env_baseVars___closed__4 = _init_l_Lake_Env_baseVars___closed__4();
lean_mark_persistent(l_Lake_Env_baseVars___closed__4);
l_Lake_Env_baseVars___closed__5 = _init_l_Lake_Env_baseVars___closed__5();
lean_mark_persistent(l_Lake_Env_baseVars___closed__5);
l_Lake_Env_baseVars___closed__6 = _init_l_Lake_Env_baseVars___closed__6();
lean_mark_persistent(l_Lake_Env_baseVars___closed__6);
l_Lake_Env_baseVars___closed__7 = _init_l_Lake_Env_baseVars___closed__7();
lean_mark_persistent(l_Lake_Env_baseVars___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
