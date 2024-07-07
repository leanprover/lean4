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
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Env_baseVars___closed__1;
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object*);
lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Env_baseVars___closed__7;
static lean_object* l_Lake_instInhabitedEnv___closed__2;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
uint8_t l_String_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_toolchain;
lean_object* l_String_dropRight(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute___closed__9;
LEAN_EXPORT lean_object* l_Lake_Env_compute_getUrlD___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Env_vars___closed__1;
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedEnv___closed__4;
LEAN_EXPORT lean_object* l_Lake_Env_compute_computePkgUrlMap(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute_getUrlD(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lake_getSearchPath(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute_computePkgUrlMap___closed__2;
LEAN_EXPORT lean_object* l_Lake_Env_toolchain___boxed(lean_object*);
static lean_object* l_Lake_Env_compute___closed__8;
static lean_object* l_Lake_Env_compute___closed__2;
lean_object* l_System_SearchPath_toString(lean_object*);
static lean_object* l_Lake_Env_compute___closed__4;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object*);
uint32_t l_String_back(lean_object*);
static lean_object* l_Lake_Env_baseVars___closed__3;
lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute___closed__5;
static lean_object* l_Lake_Env_baseVars___closed__8;
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object*);
extern lean_object* l_Lake_sharedLibPathEnvVar;
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedEnv;
static lean_object* l_Lake_instInhabitedEnv___closed__1;
static lean_object* l_Lake_Env_compute_computePkgUrlMap___closed__1;
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object*);
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
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object*);
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_Env_baseVars___closed__6;
static lean_object* l_Lake_Env_baseVars___closed__4;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = l_Lean_Json_parse(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lake_Env_compute_computePkgUrlMap___closed__2;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lake_instInhabitedEnv___closed__1;
x_19 = lean_string_append(x_17, x_18);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_19);
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Lean_Json_getObj_x3f(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lake_Env_compute_computePkgUrlMap___closed__2;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lake_instInhabitedEnv___closed__1;
x_26 = lean_string_append(x_24, x_25);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_26);
return x_3;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(x_28, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lake_Env_compute_computePkgUrlMap___closed__2;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Lake_instInhabitedEnv___closed__1;
x_34 = lean_string_append(x_32, x_33);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_34);
return x_3;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
lean_ctor_set(x_3, 0, x_35);
return x_3;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
lean_dec(x_3);
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
lean_dec(x_4);
x_38 = l_Lean_Json_parse(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lake_Env_compute_computePkgUrlMap___closed__2;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lake_instInhabitedEnv___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_36);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
x_46 = l_Lean_Json_getObj_x3f(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lake_Env_compute_computePkgUrlMap___closed__2;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = l_Lake_instInhabitedEnv___closed__1;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_36);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_box(0);
x_55 = l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(x_54, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lake_Env_compute_computePkgUrlMap___closed__2;
x_58 = lean_string_append(x_57, x_56);
lean_dec(x_56);
x_59 = l_Lake_instInhabitedEnv___closed__1;
x_60 = lean_string_append(x_58, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_36);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_55, 0);
lean_inc(x_62);
lean_dec(x_55);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_36);
return x_63;
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
lean_object* x_11; lean_object* x_12; uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_4, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_String_back(x_12);
x_14 = 47;
x_15 = lean_uint32_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_String_dropRight(x_12, x_16);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint32_t x_20; uint32_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = l_String_back(x_19);
x_21 = 47;
x_22 = lean_uint32_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_String_dropRight(x_19, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_18);
return x_26;
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
lean_object* x_5; lean_object* x_6; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = l_Lake_Env_compute___closed__8;
x_98 = lean_io_getenv(x_97, x_4);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lake_Env_compute___closed__9;
x_5 = x_101;
x_6 = x_100;
goto block_96;
}
else
{
lean_object* x_102; lean_object* x_103; uint32_t x_104; uint32_t x_105; uint8_t x_106; 
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_dec(x_98);
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
lean_dec(x_99);
x_104 = l_String_back(x_103);
x_105 = 47;
x_106 = lean_uint32_dec_eq(x_104, x_105);
if (x_106 == 0)
{
x_5 = x_103;
x_6 = x_102;
goto block_96;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_unsigned_to_nat(1u);
x_108 = l_String_dropRight(x_103, x_107);
x_5 = x_108;
x_6 = x_102;
goto block_96;
}
}
block_96:
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
lean_object* x_85; lean_object* x_86; uint32_t x_87; uint32_t x_88; uint8_t x_89; 
lean_dec(x_5);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = lean_ctor_get(x_79, 0);
lean_inc(x_86);
lean_dec(x_79);
x_87 = l_String_back(x_86);
x_88 = 47;
x_89 = lean_uint32_dec_eq(x_87, x_88);
if (x_89 == 0)
{
x_10 = x_86;
x_11 = x_85;
goto block_76;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_unsigned_to_nat(1u);
x_91 = l_String_dropRight(x_86, x_90);
x_10 = x_91;
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
uint8_t x_92; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_7);
if (x_92 == 0)
{
return x_7;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_7, 0);
x_94 = lean_ctor_get(x_7, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_7);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = l_String_isEmpty(x_2);
if (x_3 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
return x_5;
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
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 6);
x_3 = l_String_isEmpty(x_2);
if (x_3 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; 
x_4 = l_Lean_toolchain;
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
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
x_9 = l_Lean_Name_toString(x_4, x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_11 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_7, x_9, x_10);
x_1 = x_11;
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ELAN_HOME", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__8() {
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
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_3 = l_Lake_Env_toolchain(x_1);
x_4 = l_String_isEmpty(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 4);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lake_Env_baseVars___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
x_12 = l_Lake_Env_baseVars___closed__2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_ctor_get(x_1, 5);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = l_Lake_Env_leanGithash(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lake_Env_compute___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 11);
lean_inc(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = l_Lake_Env_baseVars___closed__3;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_22);
x_27 = l_Lake_Env_baseVars___closed__4;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lake_LeanInstall_leanCc_x3f(x_20);
lean_dec(x_20);
x_30 = l_Lake_Env_baseVars___closed__5;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_70; 
x_70 = lean_box(0);
x_32 = x_70;
goto block_69;
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_2);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_2, 0);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
lean_ctor_set(x_2, 0, x_73);
x_32 = x_2;
goto block_69;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_2, 0);
lean_inc(x_74);
lean_dec(x_2);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_32 = x_76;
goto block_69;
}
}
block_69:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = l_Lake_Env_baseVars___closed__7;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lake_Env_baseVars___closed__6;
x_36 = lean_array_push(x_35, x_34);
if (x_4 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_3);
x_38 = l_Lake_Env_compute___closed__2;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_array_push(x_36, x_39);
x_41 = lean_array_push(x_40, x_10);
x_42 = lean_array_push(x_41, x_13);
x_43 = l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(x_15, x_14);
x_44 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_Json_compress(x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lake_Env_compute_computePkgUrlMap___closed__1;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_array_push(x_42, x_48);
x_50 = lean_array_push(x_49, x_19);
x_51 = lean_array_push(x_50, x_25);
x_52 = lean_array_push(x_51, x_28);
x_53 = lean_array_push(x_52, x_31);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_3);
x_54 = l_Lake_Env_baseVars___closed__8;
x_55 = lean_array_push(x_36, x_54);
x_56 = lean_array_push(x_55, x_10);
x_57 = lean_array_push(x_56, x_13);
x_58 = l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(x_15, x_14);
x_59 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_Json_compress(x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lake_Env_compute_computePkgUrlMap___closed__1;
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_array_push(x_57, x_63);
x_65 = lean_array_push(x_64, x_19);
x_66 = lean_array_push(x_65, x_25);
x_67 = lean_array_push(x_66, x_28);
x_68 = lean_array_push(x_67, x_31);
return x_68;
}
}
}
}
static lean_object* _init_l_Lake_Env_vars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
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
x_18 = l_Lake_Env_vars___closed__1;
x_19 = lean_array_push(x_18, x_7);
x_20 = lean_array_push(x_19, x_12);
x_21 = lean_array_push(x_20, x_17);
x_22 = l_Array_append___rarg(x_2, x_21);
lean_dec(x_21);
x_23 = l_System_Platform_isWindows;
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = l_Lake_Env_sharedLibPath(x_1);
x_25 = l_System_SearchPath_toString(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lake_sharedLibPathEnvVar;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_array_push(x_22, x_28);
return x_29;
}
else
{
lean_dec(x_1);
return x_22;
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
l_Lake_Env_baseVars___closed__8 = _init_l_Lake_Env_baseVars___closed__8();
lean_mark_persistent(l_Lake_Env_baseVars___closed__8);
l_Lake_Env_vars___closed__1 = _init_l_Lake_Env_vars___closed__1();
lean_mark_persistent(l_Lake_Env_vars___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
