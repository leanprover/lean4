// Lean compiler output
// Module: Lake.Config.Env
// Imports: Lake.Util.Name Lake.Util.NativeLib Lake.Config.InstallPath Lake.Config.Cache
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
static lean_object* l_Lake_Env_noToolchainVars___closed__10;
lean_object* l_Lean_Json_compress(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__23;
static lean_object* l_Lake_Env_baseVars___closed__1;
static lean_object* l_Lake_Env_noToolchainVars___closed__24;
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object*);
static lean_object* l_Lake_Env_compute_getCache_x3f___closed__0;
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
static lean_object* l_Lake_Env_noToolchainVars___closed__0;
static lean_object* l_Lake_Env_noToolchainVars___closed__3;
static lean_object* l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1;
static lean_object* l_Lake_Env_noToolchainVars___closed__18;
static lean_object* l_Lake_Env_noToolchainVars___closed__6;
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute___closed__0;
extern lean_object* l_Lean_toolchain;
static lean_object* l_Lake_Env_baseVars___closed__0;
static lean_object* l_Lake_Env_noToolchainVars___closed__14;
lean_object* l_Lake_toolchain2Dir_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_getUserHome_x3f___closed__1;
static lean_object* l_Lake_Env_noToolchainVars___closed__4;
static lean_object* l_Lake_Env_noToolchainVars___closed__5;
static lean_object* l_Lake_Env_compute___closed__9;
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___Lake_Env_baseVars_spec__0(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__11;
static lean_object* l_Lake_Env_noToolchainVars___closed__2;
static lean_object* l_Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0___closed__0;
uint8_t l_Lake_Cache_isDisabled(lean_object*);
static lean_object* l_Lake_getUserHome_x3f___closed__0;
static lean_object* l_Lake_Env_noToolchainVars___closed__17;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__13;
static lean_object* l_Lake_instInhabitedEnv___closed__4;
static lean_object* l_Lake_getUserHome_x3f___closed__2;
static lean_object* l_Lake_instInhabitedEnv___closed__5;
static lean_object* l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f(lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_noToolchainVars;
static lean_object* l_Lake_Env_noToolchainVars___closed__9;
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute_computePkgUrlMap(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute_getCache_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_getSearchPath(lean_object*, lean_object*);
static lean_object* l_Lake_Env_vars___closed__0;
static lean_object* l_Lake_Env_noToolchainVars___closed__19;
static lean_object* l_Lake_Env_compute___closed__8;
static lean_object* l_Lake_Env_noToolchainVars___closed__1;
static lean_object* l_Lake_Env_compute___closed__2;
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___Lake_Env_baseVars_spec__0___lam__0___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_getSystemCacheHome_x3f___closed__0;
lean_object* l_System_SearchPath_toString(lean_object*);
static lean_object* l_Lake_getSystemCacheHome_x3f___closed__2;
static lean_object* l_Lake_Env_compute___closed__4;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lake_envToBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object*);
static lean_object* l_Lake_Env_compute_computePkgUrlMap___closed__0;
static lean_object* l_Lake_Env_noToolchainVars___closed__7;
static lean_object* l_Lake_instInhabitedEnv___closed__0;
static lean_object* l_Lake_Env_baseVars___closed__3;
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute___closed__5;
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object*);
extern lean_object* l_Lake_sharedLibPathEnvVar;
static lean_object* l_Lake_Env_compute_getCache_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedEnv;
static lean_object* l_Lake_instInhabitedEnv___closed__1;
static lean_object* l_Lake_Env_compute_computePkgUrlMap___closed__1;
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object*);
static lean_object* l_Lake_Env_compute___closed__1;
static lean_object* l_Lake_Env_compute___closed__3;
lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__21;
static lean_object* l_Lake_instInhabitedEnv___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_NameMap_toJson___at___Lake_Env_baseVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Env_baseVars___closed__2;
static lean_object* l_Lake_Env_compute___closed__6;
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object*);
static lean_object* l_Lake_Env_compute___closed__7;
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
static lean_object* l_Lake_getSystemCacheHome_x3f___closed__1;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameMap_toJson___at___Lake_Env_baseVars_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object*);
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_Env_noToolchainVars___closed__12;
LEAN_EXPORT lean_object* l_Lake_Env_compute_getCache_x3f___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_instInhabitedEnv___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = l_Lake_instInhabitedEnv___closed__1;
x_2 = lean_box(0);
x_3 = l_Lake_instInhabitedEnv___closed__0;
x_4 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*3, x_5);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedEnv___closed__2;
x_2 = l_Lake_instInhabitedEnv___closed__0;
x_3 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = l_Lake_instInhabitedEnv___closed__1;
x_2 = lean_box(0);
x_3 = l_Lake_instInhabitedEnv___closed__0;
x_4 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_3);
lean_ctor_set(x_4, 5, x_3);
lean_ctor_set(x_4, 6, x_3);
lean_ctor_set(x_4, 7, x_3);
lean_ctor_set(x_4, 8, x_3);
lean_ctor_set(x_4, 9, x_3);
lean_ctor_set(x_4, 10, x_3);
lean_ctor_set(x_4, 11, x_3);
lean_ctor_set(x_4, 12, x_3);
lean_ctor_set(x_4, 13, x_1);
lean_ctor_set(x_4, 14, x_1);
lean_ctor_set(x_4, 15, x_1);
lean_ctor_set(x_4, 16, x_1);
lean_ctor_set(x_4, 17, x_1);
lean_ctor_set(x_4, 18, x_1);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*19, x_5);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lake_instInhabitedEnv___closed__0;
x_5 = lean_box(0);
x_6 = l_Lake_instInhabitedEnv___closed__4;
x_7 = l_Lake_instInhabitedEnv___closed__3;
x_8 = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_4);
lean_ctor_set(x_8, 5, x_3);
lean_ctor_set(x_8, 6, x_4);
lean_ctor_set(x_8, 7, x_4);
lean_ctor_set(x_8, 8, x_1);
lean_ctor_set(x_8, 9, x_1);
lean_ctor_set(x_8, 10, x_1);
lean_ctor_set(x_8, 11, x_1);
lean_ctor_set(x_8, 12, x_4);
x_9 = lean_unbox(x_2);
lean_ctor_set_uint8(x_8, sizeof(void*)*13, x_9);
return x_8;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedEnv___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lake_getUserHome_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HOME", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_getUserHome_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HOMEDRIVE", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_getUserHome_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HOMEPATH", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_getUserHome_x3f___closed__0;
x_4 = lean_io_getenv(x_3, x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_19 = x_5;
} else {
 lean_dec_ref(x_5);
 x_19 = lean_box(0);
}
if (lean_is_scalar(x_19)) {
 x_20 = lean_alloc_ctor(1, 1, 0);
} else {
 x_20 = x_19;
}
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lake_getUserHome_x3f___closed__1;
x_23 = lean_io_getenv(x_22, x_1);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = l_Lake_getUserHome_x3f___closed__2;
x_34 = lean_io_getenv(x_33, x_31);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_34, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_35, 0);
x_46 = lean_string_append(x_32, x_45);
lean_dec(x_45);
lean_ctor_set(x_35, 0, x_46);
return x_34;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
lean_dec(x_35);
x_48 = lean_string_append(x_32, x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_34, 0, x_49);
return x_34;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_dec(x_34);
x_51 = lean_ctor_get(x_35, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_52 = x_35;
} else {
 lean_dec_ref(x_35);
 x_52 = lean_box(0);
}
x_53 = lean_string_append(x_32, x_51);
lean_dec(x_51);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
}
}
}
}
}
static lean_object* _init_l_Lake_getSystemCacheHome_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("XDG_CACHE_HOME", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_getSystemCacheHome_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".cache", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_getSystemCacheHome_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lake", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_getSystemCacheHome_x3f___closed__0;
x_3 = lean_io_getenv(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lake_getUserHome_x3f(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
return x_6;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = l_Lake_getSystemCacheHome_x3f___closed__1;
x_13 = l_System_FilePath_join(x_11, x_12);
x_14 = l_Lake_getSystemCacheHome_x3f___closed__2;
x_15 = l_System_FilePath_join(x_13, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_6;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l_Lake_getSystemCacheHome_x3f___closed__1;
x_18 = l_System_FilePath_join(x_16, x_17);
x_19 = l_Lake_getSystemCacheHome_x3f___closed__2;
x_20 = l_System_FilePath_join(x_18, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_6, 0, x_21);
return x_6;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_24 = x_7;
} else {
 lean_dec_ref(x_7);
 x_24 = lean_box(0);
}
x_25 = l_Lake_getSystemCacheHome_x3f___closed__1;
x_26 = l_System_FilePath_join(x_23, x_25);
x_27 = l_Lake_getSystemCacheHome_x3f___closed__2;
x_28 = l_System_FilePath_join(x_26, x_27);
if (lean_is_scalar(x_24)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_24;
}
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_3);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_3, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = l_Lake_getSystemCacheHome_x3f___closed__2;
x_36 = l_System_FilePath_join(x_34, x_35);
lean_ctor_set(x_4, 0, x_36);
return x_3;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
lean_dec(x_4);
x_38 = l_Lake_getSystemCacheHome_x3f___closed__2;
x_39 = l_System_FilePath_join(x_37, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_3, 0, x_40);
return x_3;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
lean_dec(x_3);
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_43 = x_4;
} else {
 lean_dec_ref(x_4);
 x_43 = lean_box(0);
}
x_44 = l_Lake_getSystemCacheHome_x3f___closed__2;
x_45 = l_System_FilePath_join(x_42, x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
}
}
}
static lean_object* _init_l_Lake_Env_compute_getCache_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_CACHE_DIR", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute_getCache_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cache", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute_getCache_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lake_Env_compute_getCache_x3f___closed__0;
x_5 = lean_io_getenv(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lake_getSystemCacheHome_x3f(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l_Lake_instInhabitedEnv___closed__0;
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lake_instInhabitedEnv___closed__0;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_22, 3);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lake_instInhabitedEnv___closed__0;
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lake_toolchain2Dir_go(x_2, x_26, x_27);
x_29 = l_System_FilePath_join(x_25, x_28);
lean_dec(x_28);
x_30 = l_Lake_getSystemCacheHome_x3f___closed__2;
x_31 = l_System_FilePath_join(x_29, x_30);
x_32 = l_Lake_Env_compute_getCache_x3f___closed__1;
x_33 = l_System_FilePath_join(x_31, x_32);
lean_ctor_set(x_5, 0, x_33);
return x_5;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_dec(x_5);
x_35 = lean_ctor_get(x_22, 3);
lean_inc(x_35);
lean_dec(x_22);
x_36 = l_Lake_instInhabitedEnv___closed__0;
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lake_toolchain2Dir_go(x_2, x_36, x_37);
x_39 = l_System_FilePath_join(x_35, x_38);
lean_dec(x_38);
x_40 = l_Lake_getSystemCacheHome_x3f___closed__2;
x_41 = l_System_FilePath_join(x_39, x_40);
x_42 = l_Lake_Env_compute_getCache_x3f___closed__1;
x_43 = l_System_FilePath_join(x_41, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_34);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_5);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_5, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_6, 0);
lean_inc(x_47);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_47);
return x_5;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_5, 1);
lean_inc(x_48);
lean_dec(x_5);
x_49 = lean_ctor_get(x_6, 0);
lean_inc(x_49);
lean_dec(x_6);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute_getCache_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Env_compute_getCache_x3f(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[anonymous]", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0;
x_12 = lean_string_dec_eq(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_5);
x_13 = l_String_toName(x_5);
x_14 = l_Lean_Name_isAnonymous(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_free_object(x_8);
lean_dec(x_5);
x_15 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_10);
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
x_20 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_10, x_13, x_19);
x_1 = x_20;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_22 = l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1;
x_23 = lean_string_append(x_22, x_5);
lean_dec(x_5);
x_24 = l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2;
x_25 = lean_string_append(x_23, x_24);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
}
else
{
lean_object* x_26; 
lean_free_object(x_8);
lean_dec(x_5);
x_26 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_7);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_10, x_31, x_30);
x_1 = x_32;
x_2 = x_7;
goto _start;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_34);
lean_dec(x_8);
x_35 = l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0;
x_36 = lean_string_dec_eq(x_5, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
lean_inc(x_5);
x_37 = l_String_toName(x_5);
x_38 = l_Lean_Name_isAnonymous(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_5);
x_39 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_34, x_37, x_43);
x_1 = x_44;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_6);
x_46 = l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1;
x_47 = lean_string_append(x_46, x_5);
lean_dec(x_5);
x_48 = l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_5);
x_51 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_34);
lean_dec(x_7);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_box(0);
x_57 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_34, x_56, x_55);
x_1 = x_57;
x_2 = x_7;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected a `NameMap`, got '", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0___closed__0;
x_6 = lean_unsigned_to_nat(80u);
x_7 = l_Lean_Json_pretty(x_1, x_6);
x_8 = lean_string_append(x_5, x_7);
lean_dec(x_7);
x_9 = l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
static lean_object* _init_l_Lake_Env_compute_computePkgUrlMap___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_PKG_URL_MAP", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute_computePkgUrlMap___closed__1() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lake_Env_compute_computePkgUrlMap___closed__0;
x_3 = lean_io_getenv(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_6 = x_3;
} else {
 lean_dec_ref(x_3);
 x_6 = lean_box(0);
}
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = l_Lean_Json_parse(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_7 = x_16;
goto block_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_7 = x_19;
goto block_11;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Env_compute_computePkgUrlMap___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
if (lean_is_scalar(x_6)) {
 x_10 = lean_alloc_ctor(1, 2, 0);
} else {
 x_10 = x_6;
 lean_ctor_set_tag(x_10, 1);
}
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
}
static lean_object* _init_l_Lake_Env_compute___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_NO_CACHE", 13, 13);
return x_1;
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
x_1 = lean_mk_string_unchecked("LEAN_PATH", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SRC_PATH", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PATH", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("RESERVOIR_API_URL", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/v1", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("RESERVOIR_API_BASE_URL", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ELAN_TOOLCHAIN", 14, 14);
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
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = l_Lake_Env_compute___closed__7;
x_130 = lean_io_getenv(x_129, x_5);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_142; 
x_142 = l_Lake_Env_compute___closed__9;
x_133 = x_142;
goto block_141;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint32_t x_146; uint32_t x_147; uint8_t x_148; 
x_143 = lean_ctor_get(x_131, 0);
lean_inc(x_143);
lean_dec(x_131);
x_144 = lean_string_utf8_byte_size(x_143);
x_145 = lean_string_utf8_prev(x_143, x_144);
x_146 = lean_string_utf8_get(x_143, x_145);
lean_dec(x_145);
x_147 = 47;
x_148 = lean_uint32_dec_eq(x_146, x_147);
if (x_148 == 0)
{
lean_dec(x_144);
x_133 = x_143;
goto block_141;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_unsigned_to_nat(0u);
lean_inc(x_144);
lean_inc(x_143);
x_151 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_151, 0, x_143);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_151, 2, x_144);
x_152 = l_Substring_prevn(x_151, x_149, x_144);
lean_dec(x_151);
x_153 = lean_string_utf8_extract(x_143, x_150, x_152);
lean_dec(x_152);
lean_dec(x_143);
x_133 = x_153;
goto block_141;
}
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_3);
lean_ctor_set(x_18, 3, x_9);
lean_ctor_set(x_18, 4, x_12);
lean_ctor_set(x_18, 5, x_14);
lean_ctor_set(x_18, 6, x_11);
lean_ctor_set(x_18, 7, x_16);
lean_ctor_set(x_18, 8, x_7);
lean_ctor_set(x_18, 9, x_10);
lean_ctor_set(x_18, 10, x_8);
lean_ctor_set(x_18, 11, x_15);
lean_ctor_set(x_18, 12, x_6);
lean_ctor_set_uint8(x_18, sizeof(void*)*13, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
block_34:
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_box(0);
x_33 = lean_unbox(x_32);
x_6 = x_22;
x_7 = x_21;
x_8 = x_23;
x_9 = x_24;
x_10 = x_25;
x_11 = x_27;
x_12 = x_26;
x_13 = x_29;
x_14 = x_28;
x_15 = x_31;
x_16 = x_30;
x_17 = x_33;
goto block_20;
}
block_53:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_37) == 0)
{
x_21 = x_35;
x_22 = x_36;
x_23 = x_38;
x_24 = x_39;
x_25 = x_40;
x_26 = x_46;
x_27 = x_41;
x_28 = x_42;
x_29 = x_43;
x_30 = x_44;
x_31 = x_45;
goto block_34;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
lean_dec(x_37);
x_48 = l_Lake_envToBool_x3f(x_47);
if (lean_obj_tag(x_48) == 0)
{
x_21 = x_35;
x_22 = x_36;
x_23 = x_38;
x_24 = x_39;
x_25 = x_40;
x_26 = x_46;
x_27 = x_41;
x_28 = x_42;
x_29 = x_43;
x_30 = x_44;
x_31 = x_45;
goto block_34;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
x_6 = x_36;
x_7 = x_35;
x_8 = x_38;
x_9 = x_39;
x_10 = x_40;
x_11 = x_41;
x_12 = x_46;
x_13 = x_43;
x_14 = x_42;
x_15 = x_45;
x_16 = x_44;
x_17 = x_50;
goto block_20;
}
}
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_dec(x_37);
x_51 = lean_ctor_get(x_4, 0);
lean_inc(x_51);
lean_dec(x_4);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
x_6 = x_36;
x_7 = x_35;
x_8 = x_38;
x_9 = x_39;
x_10 = x_40;
x_11 = x_41;
x_12 = x_46;
x_13 = x_43;
x_14 = x_42;
x_15 = x_45;
x_16 = x_44;
x_17 = x_52;
goto block_20;
}
}
block_90:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_59 = l_Lake_Env_compute___closed__0;
x_60 = lean_io_getenv(x_59, x_58);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_3);
x_63 = l_Lake_Env_compute_getCache_x3f(x_3, x_54, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lake_Env_compute___closed__1;
x_67 = lean_io_getenv(x_66, x_65);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lake_Env_compute___closed__2;
x_71 = l_Lake_getSearchPath(x_70, x_69);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lake_Env_compute___closed__3;
x_75 = l_Lake_getSearchPath(x_74, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lake_sharedLibPathEnvVar;
x_79 = l_Lake_getSearchPath(x_78, x_77);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lake_Env_compute___closed__4;
x_83 = l_Lake_getSearchPath(x_82, x_81);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lake_instInhabitedEnv___closed__0;
x_35 = x_72;
x_36 = x_54;
x_37 = x_61;
x_38 = x_80;
x_39 = x_57;
x_40 = x_76;
x_41 = x_64;
x_42 = x_55;
x_43 = x_85;
x_44 = x_56;
x_45 = x_84;
x_46 = x_86;
goto block_53;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_dec(x_83);
x_89 = lean_ctor_get(x_68, 0);
lean_inc(x_89);
lean_dec(x_68);
x_35 = x_72;
x_36 = x_54;
x_37 = x_61;
x_38 = x_80;
x_39 = x_57;
x_40 = x_76;
x_41 = x_64;
x_42 = x_55;
x_43 = x_88;
x_44 = x_56;
x_45 = x_87;
x_46 = x_89;
goto block_53;
}
}
block_120:
{
lean_object* x_95; 
x_95 = l_Lake_Env_compute_computePkgUrlMap(x_91);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lake_Env_compute___closed__5;
x_99 = lean_io_getenv(x_98, x_97);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lake_Env_compute___closed__6;
x_103 = lean_string_append(x_92, x_102);
x_54 = x_94;
x_55 = x_96;
x_56 = x_93;
x_57 = x_103;
x_58 = x_101;
goto block_90;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint32_t x_108; uint32_t x_109; uint8_t x_110; 
lean_dec(x_92);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_dec(x_99);
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
lean_dec(x_100);
x_106 = lean_string_utf8_byte_size(x_105);
x_107 = lean_string_utf8_prev(x_105, x_106);
x_108 = lean_string_utf8_get(x_105, x_107);
lean_dec(x_107);
x_109 = 47;
x_110 = lean_uint32_dec_eq(x_108, x_109);
if (x_110 == 0)
{
lean_dec(x_106);
x_54 = x_94;
x_55 = x_96;
x_56 = x_93;
x_57 = x_105;
x_58 = x_104;
goto block_90;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_unsigned_to_nat(0u);
lean_inc(x_106);
lean_inc(x_105);
x_113 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_113, 0, x_105);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_106);
x_114 = l_Substring_prevn(x_113, x_111, x_106);
lean_dec(x_113);
x_115 = lean_string_utf8_extract(x_105, x_112, x_114);
lean_dec(x_114);
lean_dec(x_105);
x_54 = x_94;
x_55 = x_96;
x_56 = x_93;
x_57 = x_115;
x_58 = x_104;
goto block_90;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_95);
if (x_116 == 0)
{
return x_95;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_95, 0);
x_118 = lean_ctor_get(x_95, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_95);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
block_128:
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_124 = lean_string_utf8_byte_size(x_123);
x_125 = lean_unsigned_to_nat(0u);
x_126 = lean_nat_dec_eq(x_124, x_125);
lean_dec(x_124);
if (x_126 == 0)
{
lean_inc(x_123);
x_91 = x_121;
x_92 = x_122;
x_93 = x_123;
x_94 = x_123;
goto block_120;
}
else
{
lean_object* x_127; 
x_127 = l_Lean_toolchain;
x_91 = x_121;
x_92 = x_122;
x_93 = x_123;
x_94 = x_127;
goto block_120;
}
}
block_141:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = l_Lake_Env_compute___closed__8;
x_135 = lean_io_getenv(x_134, x_132);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lake_instInhabitedEnv___closed__0;
x_121 = x_137;
x_122 = x_133;
x_123 = x_138;
goto block_128;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
lean_dec(x_135);
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
lean_dec(x_136);
x_121 = x_139;
x_122 = x_133;
x_123 = x_140;
goto block_128;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 4);
x_4 = lean_string_utf8_byte_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
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
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 11);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_3, 6);
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
lean_inc(x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_4);
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_inc(x_4);
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_4);
return x_10;
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
x_3 = lean_ctor_get(x_1, 8);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
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
x_3 = lean_ctor_get(x_1, 9);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
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
x_3 = lean_ctor_get(x_1, 10);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lake_LeanInstall_sharedLibPath(x_2);
lean_dec(x_2);
x_5 = l_List_appendTR___redArg(x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_compute___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_noToolchainVars___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_OVERRIDE_LEAN", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_noToolchainVars___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_HOME", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_noToolchainVars___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_compute_getCache_x3f___closed__0;
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
x_2 = l_Lake_Env_compute___closed__1;
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__0;
x_2 = l_Lake_Env_noToolchainVars___closed__15;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__2;
x_2 = l_Lake_Env_noToolchainVars___closed__16;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__4;
x_2 = l_Lake_Env_noToolchainVars___closed__17;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__6;
x_2 = l_Lake_Env_noToolchainVars___closed__18;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__7;
x_2 = l_Lake_Env_noToolchainVars___closed__19;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__9;
x_2 = l_Lake_Env_noToolchainVars___closed__20;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__10;
x_2 = l_Lake_Env_noToolchainVars___closed__21;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__12;
x_2 = l_Lake_Env_noToolchainVars___closed__22;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__14;
x_2 = l_Lake_Env_noToolchainVars___closed__23;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Env_noToolchainVars___closed__24;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_NameMap_toJson___at___Lake_Env_baseVars_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_1);
x_8 = l_Lean_RBNode_fold___at___Lean_NameMap_toJson___at___Lake_Env_baseVars_spec__0_spec__0(x_1, x_2, x_4);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
lean_inc(x_1);
x_11 = l_Lean_Name_toString(x_5, x_10, x_1);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_6);
x_13 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_8, x_11, x_12);
x_2 = x_13;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lean_NameMap_toJson___at___Lake_Env_baseVars_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___Lake_Env_baseVars_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_NameMap_toJson___at___Lake_Env_baseVars_spec__0___lam__0___boxed), 1, 0);
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_fold___at___Lean_NameMap_toJson___at___Lake_Env_baseVars_spec__0_spec__0(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_CC", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_84; lean_object* x_85; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 6);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 12);
lean_inc(x_7);
x_84 = l_Lake_Env_baseVars___closed__2;
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_96; 
x_96 = lean_box(0);
x_85 = x_96;
goto block_95;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_4, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_85 = x_99;
goto block_95;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 11);
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_15);
x_20 = l_Lake_Env_noToolchainVars___closed__8;
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lake_Env_compute___closed__1;
x_24 = l_Lake_Env_leanGithash(x_1);
lean_dec(x_1);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lake_Env_noToolchainVars___closed__11;
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_16);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lake_Env_noToolchainVars___closed__13;
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_18);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lake_Env_baseVars___closed__0;
x_34 = l_Lake_LeanInstall_leanCc_x3f(x_3);
lean_dec(x_3);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lake_Env_baseVars___closed__1;
x_37 = lean_array_push(x_36, x_9);
x_38 = lean_array_push(x_37, x_8);
x_39 = lean_array_push(x_38, x_11);
x_40 = lean_array_push(x_39, x_14);
x_41 = lean_array_push(x_40, x_13);
x_42 = lean_array_push(x_41, x_12);
x_43 = lean_array_push(x_42, x_19);
x_44 = lean_array_push(x_43, x_22);
x_45 = lean_array_push(x_44, x_26);
x_46 = lean_array_push(x_45, x_29);
x_47 = lean_array_push(x_46, x_32);
x_48 = lean_array_push(x_47, x_35);
return x_48;
}
block_72:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 5);
lean_inc(x_55);
lean_dec(x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_53);
x_57 = l_Lake_Env_noToolchainVars___closed__1;
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lake_Env_noToolchainVars___closed__5;
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_54);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lake_Env_compute_computePkgUrlMap___closed__0;
x_64 = l_Lean_NameMap_toJson___at___Lake_Env_baseVars_spec__0(x_5);
x_65 = l_Lean_Json_compress(x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lake_Env_compute_getCache_x3f___closed__0;
x_69 = l_Lake_Cache_isDisabled(x_6);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_6);
x_8 = x_51;
x_9 = x_50;
x_10 = x_68;
x_11 = x_56;
x_12 = x_67;
x_13 = x_62;
x_14 = x_59;
x_15 = x_70;
goto block_49;
}
else
{
lean_object* x_71; 
lean_dec(x_6);
x_71 = lean_box(0);
x_8 = x_51;
x_9 = x_50;
x_10 = x_68;
x_11 = x_56;
x_12 = x_67;
x_13 = x_62;
x_14 = x_59;
x_15 = x_71;
goto block_49;
}
}
block_83:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lake_Env_compute___closed__8;
x_78 = lean_string_utf8_byte_size(x_7);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_eq(x_78, x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_7);
x_50 = x_73;
x_51 = x_76;
x_52 = x_77;
x_53 = x_81;
goto block_72;
}
else
{
lean_object* x_82; 
lean_dec(x_7);
x_82 = lean_box(0);
x_50 = x_73;
x_51 = x_76;
x_52 = x_77;
x_53 = x_82;
goto block_72;
}
}
block_95:
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lake_Env_baseVars___closed__3;
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_88; 
x_88 = lean_box(0);
x_73 = x_86;
x_74 = x_87;
x_75 = x_88;
goto block_83;
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_4);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_4, 0);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec(x_90);
lean_ctor_set(x_4, 0, x_91);
x_73 = x_86;
x_74 = x_87;
x_75 = x_4;
goto block_83;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_4, 0);
lean_inc(x_92);
lean_dec(x_4);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_73 = x_86;
x_74 = x_87;
x_75 = x_94;
goto block_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___Lake_Env_baseVars_spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_NameMap_toJson___at___Lake_Env_baseVars_spec__0___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_vars___closed__0() {
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
x_3 = l_Lake_Env_compute___closed__2;
x_4 = l_Lake_Env_leanPath(x_1);
x_5 = l_System_SearchPath_toString(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lake_Env_compute___closed__3;
x_9 = l_Lake_Env_leanSrcPath(x_1);
x_10 = l_System_SearchPath_toString(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lake_Env_compute___closed__4;
x_14 = l_Lake_Env_path(x_1);
x_15 = l_System_SearchPath_toString(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lake_Env_vars___closed__0;
x_19 = lean_array_push(x_18, x_7);
x_20 = lean_array_push(x_19, x_12);
x_21 = lean_array_push(x_20, x_17);
x_22 = l_Array_append___redArg(x_2, x_21);
lean_dec(x_21);
x_23 = l_System_Platform_isWindows;
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = l_Lake_sharedLibPathEnvVar;
x_25 = l_Lake_Env_sharedLibPath(x_1);
x_26 = l_System_SearchPath_toString(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
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
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_3, 3);
x_6 = l_Lake_Env_leanPath(x_1);
lean_inc(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_4);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_4);
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
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Cache(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Env(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_NativeLib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InstallPath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Cache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedEnv___closed__0 = _init_l_Lake_instInhabitedEnv___closed__0();
lean_mark_persistent(l_Lake_instInhabitedEnv___closed__0);
l_Lake_instInhabitedEnv___closed__1 = _init_l_Lake_instInhabitedEnv___closed__1();
lean_mark_persistent(l_Lake_instInhabitedEnv___closed__1);
l_Lake_instInhabitedEnv___closed__2 = _init_l_Lake_instInhabitedEnv___closed__2();
lean_mark_persistent(l_Lake_instInhabitedEnv___closed__2);
l_Lake_instInhabitedEnv___closed__3 = _init_l_Lake_instInhabitedEnv___closed__3();
lean_mark_persistent(l_Lake_instInhabitedEnv___closed__3);
l_Lake_instInhabitedEnv___closed__4 = _init_l_Lake_instInhabitedEnv___closed__4();
lean_mark_persistent(l_Lake_instInhabitedEnv___closed__4);
l_Lake_instInhabitedEnv___closed__5 = _init_l_Lake_instInhabitedEnv___closed__5();
lean_mark_persistent(l_Lake_instInhabitedEnv___closed__5);
l_Lake_instInhabitedEnv = _init_l_Lake_instInhabitedEnv();
lean_mark_persistent(l_Lake_instInhabitedEnv);
l_Lake_getUserHome_x3f___closed__0 = _init_l_Lake_getUserHome_x3f___closed__0();
lean_mark_persistent(l_Lake_getUserHome_x3f___closed__0);
l_Lake_getUserHome_x3f___closed__1 = _init_l_Lake_getUserHome_x3f___closed__1();
lean_mark_persistent(l_Lake_getUserHome_x3f___closed__1);
l_Lake_getUserHome_x3f___closed__2 = _init_l_Lake_getUserHome_x3f___closed__2();
lean_mark_persistent(l_Lake_getUserHome_x3f___closed__2);
l_Lake_getSystemCacheHome_x3f___closed__0 = _init_l_Lake_getSystemCacheHome_x3f___closed__0();
lean_mark_persistent(l_Lake_getSystemCacheHome_x3f___closed__0);
l_Lake_getSystemCacheHome_x3f___closed__1 = _init_l_Lake_getSystemCacheHome_x3f___closed__1();
lean_mark_persistent(l_Lake_getSystemCacheHome_x3f___closed__1);
l_Lake_getSystemCacheHome_x3f___closed__2 = _init_l_Lake_getSystemCacheHome_x3f___closed__2();
lean_mark_persistent(l_Lake_getSystemCacheHome_x3f___closed__2);
l_Lake_Env_compute_getCache_x3f___closed__0 = _init_l_Lake_Env_compute_getCache_x3f___closed__0();
lean_mark_persistent(l_Lake_Env_compute_getCache_x3f___closed__0);
l_Lake_Env_compute_getCache_x3f___closed__1 = _init_l_Lake_Env_compute_getCache_x3f___closed__1();
lean_mark_persistent(l_Lake_Env_compute_getCache_x3f___closed__1);
l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0 = _init_l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0);
l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1 = _init_l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1);
l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2 = _init_l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_RBNode_foldM___at___Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2);
l_Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0___closed__0 = _init_l_Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0___closed__0();
lean_mark_persistent(l_Lean_NameMap_fromJson_x3f___at___Lake_Env_compute_computePkgUrlMap_spec__0___closed__0);
l_Lake_Env_compute_computePkgUrlMap___closed__0 = _init_l_Lake_Env_compute_computePkgUrlMap___closed__0();
lean_mark_persistent(l_Lake_Env_compute_computePkgUrlMap___closed__0);
l_Lake_Env_compute_computePkgUrlMap___closed__1 = _init_l_Lake_Env_compute_computePkgUrlMap___closed__1();
lean_mark_persistent(l_Lake_Env_compute_computePkgUrlMap___closed__1);
l_Lake_Env_compute___closed__0 = _init_l_Lake_Env_compute___closed__0();
lean_mark_persistent(l_Lake_Env_compute___closed__0);
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
l_Lake_Env_noToolchainVars___closed__0 = _init_l_Lake_Env_noToolchainVars___closed__0();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__0);
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
l_Lake_Env_noToolchainVars___closed__24 = _init_l_Lake_Env_noToolchainVars___closed__24();
lean_mark_persistent(l_Lake_Env_noToolchainVars___closed__24);
l_Lake_Env_noToolchainVars = _init_l_Lake_Env_noToolchainVars();
lean_mark_persistent(l_Lake_Env_noToolchainVars);
l_Lake_Env_baseVars___closed__0 = _init_l_Lake_Env_baseVars___closed__0();
lean_mark_persistent(l_Lake_Env_baseVars___closed__0);
l_Lake_Env_baseVars___closed__1 = _init_l_Lake_Env_baseVars___closed__1();
lean_mark_persistent(l_Lake_Env_baseVars___closed__1);
l_Lake_Env_baseVars___closed__2 = _init_l_Lake_Env_baseVars___closed__2();
lean_mark_persistent(l_Lake_Env_baseVars___closed__2);
l_Lake_Env_baseVars___closed__3 = _init_l_Lake_Env_baseVars___closed__3();
lean_mark_persistent(l_Lake_Env_baseVars___closed__3);
l_Lake_Env_vars___closed__0 = _init_l_Lake_Env_vars___closed__0();
lean_mark_persistent(l_Lake_Env_vars___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
