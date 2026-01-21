// Lean compiler output
// Module: Lake.Config.Env
// Imports: public import Lake.Config.Cache public import Lake.Config.InstallPath
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeSystemCache_x3f();
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(lean_object*);
static lean_object* l_Lake_Env_baseVars___closed__1;
lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object*);
lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lake_instInhabitedEnv_default;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_io_getenv(lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__15;
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___boxed(lean_object*);
static lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1;
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f___boxed(lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__0;
static lean_object* l_Lake_Env_noToolchainVars___closed__3;
static lean_object* l_Lake_Env_compute___closed__11;
static lean_object* l_Lake_Env_noToolchainVars___closed__6;
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute___closed__12;
extern lean_object* l_Lean_toolchain;
static lean_object* l_Lake_Env_baseVars___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__14;
extern lean_object* l_Lake_instInhabitedLakeInstall_default;
static lean_object* l_Lake_getUserHome_x3f___closed__1;
static lean_object* l_Lake_Env_noToolchainVars___closed__4;
static lean_object* l_Lake_Env_noToolchainVars___closed__5;
static lean_object* l_Lake_Env_compute___closed__9;
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2;
extern lean_object* l_Lake_instInhabitedLeanInstall_default;
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___boxed(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__11;
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__2;
static lean_object* l_Lake_instInhabitedEnv_default___closed__0;
static lean_object* l_Lake_getUserHome_x3f___closed__0;
static lean_object* l_Lake_Env_noToolchainVars___closed__17;
static lean_object* l_Lake_Env_vars___closed__2;
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(lean_object*, lean_object*);
static lean_object* l_Lake_Env_vars___closed__1;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__13;
static lean_object* l_Lake_getUserHome_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f();
LEAN_EXPORT lean_object* l_Lake_Env_noToolchainVars(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___boxed(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4;
static lean_object* l_Lake_Env_noToolchainVars___closed__9;
static lean_object* l_Lake_Env_computeToolchain___closed__0;
static lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f();
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Lake_getSearchPath(lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5;
static lean_object* l_Lake_Env_vars___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Env_compute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain___boxed(lean_object*);
static lean_object* l_Lake_Env_compute___closed__8;
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0;
static lean_object* l_Lake_Env_noToolchainVars___closed__1;
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute___closed__2;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_getSystemCacheHome_x3f___closed__0;
lean_object* l_System_SearchPath_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f();
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeToolchainCache_x3f(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lake_envToBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object*);
static lean_object* l_Lake_Env_noToolchainVars___closed__7;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeSystemCache_x3f___boxed(lean_object*);
static lean_object* l_Lake_Env_baseVars___closed__3;
lean_object* l_String_toName(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1;
static lean_object* l_Lake_Env_compute___closed__5;
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object*);
extern lean_object* l_Lake_sharedLibPathEnvVar;
static lean_object* l_Lake_instInhabitedEnv_default___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedEnv;
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object*);
static lean_object* l_Lake_Env_baseVars___closed__5;
static lean_object* l_Lake_Env_compute___closed__1;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute___closed__3;
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain();
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_Env_baseVars___closed__2;
static lean_object* l_Lake_Env_compute___closed__6;
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeToolchainCache_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Env_compute___closed__7;
static lean_object* l_Lake_Env_compute___closed__10;
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_getSystemCacheHome_x3f___closed__1;
static lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object*);
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_Env_baseVars___closed__4;
static lean_object* l_Lake_Env_noToolchainVars___closed__12;
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lake_instInhabitedEnv_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv_default___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(1);
x_4 = l_Lake_instInhabitedEnv_default___closed__0;
x_5 = lean_box(0);
x_6 = l_Lake_instInhabitedLeanInstall_default;
x_7 = l_Lake_instInhabitedLakeInstall_default;
x_8 = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_4);
lean_ctor_set(x_8, 5, x_3);
lean_ctor_set(x_8, 6, x_5);
lean_ctor_set(x_8, 7, x_5);
lean_ctor_set(x_8, 8, x_5);
lean_ctor_set(x_8, 9, x_5);
lean_ctor_set(x_8, 10, x_5);
lean_ctor_set(x_8, 11, x_5);
lean_ctor_set(x_8, 12, x_1);
lean_ctor_set(x_8, 13, x_1);
lean_ctor_set(x_8, 14, x_1);
lean_ctor_set(x_8, 15, x_1);
lean_ctor_set(x_8, 16, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*17, x_2);
lean_ctor_set_uint8(x_8, sizeof(void*)*17 + 1, x_2);
return x_8;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedEnv_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedEnv_default;
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
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f() {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_getUserHome_x3f___closed__0;
x_4 = lean_io_getenv(x_3);
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lake_getUserHome_x3f___closed__1;
x_10 = lean_io_getenv(x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lake_getUserHome_x3f___closed__2;
x_13 = lean_io_getenv(x_12);
if (lean_obj_tag(x_13) == 1)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_string_append(x_11, x_15);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_string_append(x_11, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_11);
x_20 = lean_box(0);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_10);
x_21 = lean_box(0);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getUserHome_x3f();
return x_2;
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
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_getSystemCacheHome_x3f___closed__0;
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = l_Lake_getUserHome_x3f();
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lake_getSystemCacheHome_x3f___closed__1;
x_11 = l_System_FilePath_join(x_9, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lake_getSystemCacheHome_x3f___closed__1;
x_14 = l_System_FilePath_join(x_12, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_7);
x_16 = lean_box(0);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getSystemCacheHome_x3f();
return x_2;
}
}
static lean_object* _init_l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cache", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Lake_instInhabitedEnv_default___closed__0;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(x_2, x_4, x_5);
x_7 = l_System_FilePath_join(x_3, x_6);
x_8 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0;
x_9 = l_System_FilePath_join(x_7, x_8);
x_10 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1;
x_11 = l_System_FilePath_join(x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_1, x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec_ref(x_1);
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_computeToolchain___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ELAN_TOOLCHAIN", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_Env_computeToolchain___closed__0;
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_toolchain;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_computeToolchain();
return x_2;
}
}
static lean_object* _init_l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_CACHE_DIR", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0;
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_string_utf8_byte_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_free_object(x_3);
lean_dec(x_6);
x_10 = lean_box(0);
return x_10;
}
else
{
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_string_utf8_byte_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeSystemCache_x3f() {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getSystemCacheHome_x3f();
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0;
x_7 = l_System_FilePath_join(x_5, x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0;
x_10 = l_System_FilePath_join(x_8, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeSystemCache_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_Env_0__Lake_Env_computeSystemCache_x3f();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeToolchainCache_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_string_utf8_byte_size(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_5, x_2);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_10; 
lean_free_object(x_1);
lean_dec(x_5);
x_10 = lean_box(0);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_string_utf8_byte_size(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(x_11, x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_11);
x_17 = lean_box(0);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeToolchainCache_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Env_0__Lake_Env_computeToolchainCache_x3f(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_8; 
x_8 = l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f();
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_4 = x_9;
x_5 = lean_box(0);
goto block_7;
}
else
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = l___private_Lake_Config_Env_0__Lake_Env_computeToolchainCache_x3f(x_1, x_2);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_4 = x_11;
x_5 = lean_box(0);
goto block_7;
}
else
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = l___private_Lake_Config_Env_0__Lake_Env_computeSystemCache_x3f();
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_4 = x_13;
x_5 = lean_box(0);
goto block_7;
}
else
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
}
}
block_7:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Env_computeCache_x3f(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0;
x_6 = lean_io_getenv(x_5);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_string_utf8_byte_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 8);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 7);
lean_dec(x_14);
lean_inc_ref(x_6);
lean_ctor_set(x_3, 8, x_6);
lean_ctor_set(x_3, 7, x_6);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get(x_3, 3);
x_20 = lean_ctor_get(x_3, 4);
x_21 = lean_ctor_get(x_3, 5);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*17);
x_23 = lean_ctor_get(x_3, 6);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*17 + 1);
x_25 = lean_ctor_get(x_3, 9);
x_26 = lean_ctor_get(x_3, 10);
x_27 = lean_ctor_get(x_3, 11);
x_28 = lean_ctor_get(x_3, 12);
x_29 = lean_ctor_get(x_3, 13);
x_30 = lean_ctor_get(x_3, 14);
x_31 = lean_ctor_get(x_3, 15);
x_32 = lean_ctor_get(x_3, 16);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
lean_inc_ref(x_6);
x_33 = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_17);
lean_ctor_set(x_33, 2, x_18);
lean_ctor_set(x_33, 3, x_19);
lean_ctor_set(x_33, 4, x_20);
lean_ctor_set(x_33, 5, x_21);
lean_ctor_set(x_33, 6, x_23);
lean_ctor_set(x_33, 7, x_6);
lean_ctor_set(x_33, 8, x_6);
lean_ctor_set(x_33, 9, x_25);
lean_ctor_set(x_33, 10, x_26);
lean_ctor_set(x_33, 11, x_27);
lean_ctor_set(x_33, 12, x_28);
lean_ctor_set(x_33, 13, x_29);
lean_ctor_set(x_33, 14, x_30);
lean_ctor_set(x_33, 15, x_31);
lean_ctor_set(x_33, 16, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*17, x_22);
lean_ctor_set_uint8(x_33, sizeof(void*)*17 + 1, x_24);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_6);
lean_dec(x_8);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
lean_object* x_36; 
lean_ctor_set_uint8(x_3, sizeof(void*)*17 + 1, x_11);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_3);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_3, 1);
x_39 = lean_ctor_get(x_3, 2);
x_40 = lean_ctor_get(x_3, 3);
x_41 = lean_ctor_get(x_3, 4);
x_42 = lean_ctor_get(x_3, 5);
x_43 = lean_ctor_get_uint8(x_3, sizeof(void*)*17);
x_44 = lean_ctor_get(x_3, 6);
x_45 = lean_ctor_get(x_3, 7);
x_46 = lean_ctor_get(x_3, 8);
x_47 = lean_ctor_get(x_3, 9);
x_48 = lean_ctor_get(x_3, 10);
x_49 = lean_ctor_get(x_3, 11);
x_50 = lean_ctor_get(x_3, 12);
x_51 = lean_ctor_get(x_3, 13);
x_52 = lean_ctor_get(x_3, 14);
x_53 = lean_ctor_get(x_3, 15);
x_54 = lean_ctor_get(x_3, 16);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_3);
x_55 = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(x_55, 0, x_37);
lean_ctor_set(x_55, 1, x_38);
lean_ctor_set(x_55, 2, x_39);
lean_ctor_set(x_55, 3, x_40);
lean_ctor_set(x_55, 4, x_41);
lean_ctor_set(x_55, 5, x_42);
lean_ctor_set(x_55, 6, x_44);
lean_ctor_set(x_55, 7, x_45);
lean_ctor_set(x_55, 8, x_46);
lean_ctor_set(x_55, 9, x_47);
lean_ctor_set(x_55, 10, x_48);
lean_ctor_set(x_55, 11, x_49);
lean_ctor_set(x_55, 12, x_50);
lean_ctor_set(x_55, 13, x_51);
lean_ctor_set(x_55, 14, x_52);
lean_ctor_set(x_55, 15, x_53);
lean_ctor_set(x_55, 16, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*17, x_43);
lean_ctor_set_uint8(x_55, sizeof(void*)*17 + 1, x_11);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_6, 0);
lean_inc(x_57);
lean_dec(x_6);
x_58 = lean_string_utf8_byte_size(x_57);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_eq(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_61 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_3, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_3, 5);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_3, sizeof(void*)*17);
x_68 = lean_ctor_get(x_3, 6);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_3, sizeof(void*)*17 + 1);
x_70 = lean_ctor_get(x_3, 9);
lean_inc(x_70);
x_71 = lean_ctor_get(x_3, 10);
lean_inc(x_71);
x_72 = lean_ctor_get(x_3, 11);
lean_inc(x_72);
x_73 = lean_ctor_get(x_3, 12);
lean_inc(x_73);
x_74 = lean_ctor_get(x_3, 13);
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 14);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 15);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 16);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 lean_ctor_release(x_3, 10);
 lean_ctor_release(x_3, 11);
 lean_ctor_release(x_3, 12);
 lean_ctor_release(x_3, 13);
 lean_ctor_release(x_3, 14);
 lean_ctor_release(x_3, 15);
 lean_ctor_release(x_3, 16);
 x_78 = x_3;
} else {
 lean_dec_ref(x_3);
 x_78 = lean_box(0);
}
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_57);
lean_inc_ref(x_79);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 17, 2);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_61);
lean_ctor_set(x_80, 1, x_62);
lean_ctor_set(x_80, 2, x_63);
lean_ctor_set(x_80, 3, x_64);
lean_ctor_set(x_80, 4, x_65);
lean_ctor_set(x_80, 5, x_66);
lean_ctor_set(x_80, 6, x_68);
lean_ctor_set(x_80, 7, x_79);
lean_ctor_set(x_80, 8, x_79);
lean_ctor_set(x_80, 9, x_70);
lean_ctor_set(x_80, 10, x_71);
lean_ctor_set(x_80, 11, x_72);
lean_ctor_set(x_80, 12, x_73);
lean_ctor_set(x_80, 13, x_74);
lean_ctor_set(x_80, 14, x_75);
lean_ctor_set(x_80, 15, x_76);
lean_ctor_set(x_80, 16, x_77);
lean_ctor_set_uint8(x_80, sizeof(void*)*17, x_67);
lean_ctor_set_uint8(x_80, sizeof(void*)*17 + 1, x_69);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_57);
x_82 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_3, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_3, 5);
lean_inc(x_87);
x_88 = lean_ctor_get_uint8(x_3, sizeof(void*)*17);
x_89 = lean_ctor_get(x_3, 6);
lean_inc(x_89);
x_90 = lean_ctor_get(x_3, 7);
lean_inc(x_90);
x_91 = lean_ctor_get(x_3, 8);
lean_inc(x_91);
x_92 = lean_ctor_get(x_3, 9);
lean_inc(x_92);
x_93 = lean_ctor_get(x_3, 10);
lean_inc(x_93);
x_94 = lean_ctor_get(x_3, 11);
lean_inc(x_94);
x_95 = lean_ctor_get(x_3, 12);
lean_inc(x_95);
x_96 = lean_ctor_get(x_3, 13);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 14);
lean_inc(x_97);
x_98 = lean_ctor_get(x_3, 15);
lean_inc(x_98);
x_99 = lean_ctor_get(x_3, 16);
lean_inc_ref(x_99);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 lean_ctor_release(x_3, 10);
 lean_ctor_release(x_3, 11);
 lean_ctor_release(x_3, 12);
 lean_ctor_release(x_3, 13);
 lean_ctor_release(x_3, 14);
 lean_ctor_release(x_3, 15);
 lean_ctor_release(x_3, 16);
 x_100 = x_3;
} else {
 lean_dec_ref(x_3);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 17, 2);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_82);
lean_ctor_set(x_101, 1, x_83);
lean_ctor_set(x_101, 2, x_84);
lean_ctor_set(x_101, 3, x_85);
lean_ctor_set(x_101, 4, x_86);
lean_ctor_set(x_101, 5, x_87);
lean_ctor_set(x_101, 6, x_89);
lean_ctor_set(x_101, 7, x_90);
lean_ctor_set(x_101, 8, x_91);
lean_ctor_set(x_101, 9, x_92);
lean_ctor_set(x_101, 10, x_93);
lean_ctor_set(x_101, 11, x_94);
lean_ctor_set(x_101, 12, x_95);
lean_ctor_set(x_101, 13, x_96);
lean_ctor_set(x_101, 14, x_97);
lean_ctor_set(x_101, 15, x_98);
lean_ctor_set(x_101, 16, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*17, x_88);
lean_ctor_set_uint8(x_101, sizeof(void*)*17 + 1, x_60);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; 
lean_dec(x_6);
x_103 = l___private_Lake_Config_Env_0__Lake_Env_computeToolchainCache_x3f(x_1, x_2);
if (lean_obj_tag(x_103) == 1)
{
lean_object* x_104; uint8_t x_105; 
x_104 = l___private_Lake_Config_Env_0__Lake_Env_computeSystemCache_x3f();
x_105 = !lean_is_exclusive(x_3);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_3, 8);
lean_dec(x_106);
x_107 = lean_ctor_get(x_3, 7);
lean_dec(x_107);
lean_inc_ref(x_103);
lean_ctor_set(x_3, 8, x_104);
lean_ctor_set(x_3, 7, x_103);
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_103, 0);
lean_dec(x_109);
lean_ctor_set_tag(x_103, 0);
lean_ctor_set(x_103, 0, x_3);
return x_103;
}
else
{
lean_object* x_110; 
lean_dec(x_103);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_3);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_111 = lean_ctor_get(x_3, 0);
x_112 = lean_ctor_get(x_3, 1);
x_113 = lean_ctor_get(x_3, 2);
x_114 = lean_ctor_get(x_3, 3);
x_115 = lean_ctor_get(x_3, 4);
x_116 = lean_ctor_get(x_3, 5);
x_117 = lean_ctor_get_uint8(x_3, sizeof(void*)*17);
x_118 = lean_ctor_get(x_3, 6);
x_119 = lean_ctor_get_uint8(x_3, sizeof(void*)*17 + 1);
x_120 = lean_ctor_get(x_3, 9);
x_121 = lean_ctor_get(x_3, 10);
x_122 = lean_ctor_get(x_3, 11);
x_123 = lean_ctor_get(x_3, 12);
x_124 = lean_ctor_get(x_3, 13);
x_125 = lean_ctor_get(x_3, 14);
x_126 = lean_ctor_get(x_3, 15);
x_127 = lean_ctor_get(x_3, 16);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_118);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_3);
lean_inc_ref(x_103);
x_128 = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(x_128, 0, x_111);
lean_ctor_set(x_128, 1, x_112);
lean_ctor_set(x_128, 2, x_113);
lean_ctor_set(x_128, 3, x_114);
lean_ctor_set(x_128, 4, x_115);
lean_ctor_set(x_128, 5, x_116);
lean_ctor_set(x_128, 6, x_118);
lean_ctor_set(x_128, 7, x_103);
lean_ctor_set(x_128, 8, x_104);
lean_ctor_set(x_128, 9, x_120);
lean_ctor_set(x_128, 10, x_121);
lean_ctor_set(x_128, 11, x_122);
lean_ctor_set(x_128, 12, x_123);
lean_ctor_set(x_128, 13, x_124);
lean_ctor_set(x_128, 14, x_125);
lean_ctor_set(x_128, 15, x_126);
lean_ctor_set(x_128, 16, x_127);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_129 = x_103;
} else {
 lean_dec_ref(x_103);
 x_129 = lean_box(0);
}
lean_ctor_set_uint8(x_128, sizeof(void*)*17, x_117);
lean_ctor_set_uint8(x_128, sizeof(void*)*17 + 1, x_119);
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 1, 0);
} else {
 x_130 = x_129;
 lean_ctor_set_tag(x_130, 0);
}
lean_ctor_set(x_130, 0, x_128);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_103);
x_131 = l___private_Lake_Config_Env_0__Lake_Env_computeSystemCache_x3f();
if (lean_obj_tag(x_131) == 1)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_3);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_3, 8);
lean_dec(x_133);
x_134 = lean_ctor_get(x_3, 7);
lean_dec(x_134);
lean_inc_ref_n(x_131, 2);
lean_ctor_set(x_3, 8, x_131);
lean_ctor_set(x_3, 7, x_131);
x_135 = !lean_is_exclusive(x_131);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_131, 0);
lean_dec(x_136);
lean_ctor_set_tag(x_131, 0);
lean_ctor_set(x_131, 0, x_3);
return x_131;
}
else
{
lean_object* x_137; 
lean_dec(x_131);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_3);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_138 = lean_ctor_get(x_3, 0);
x_139 = lean_ctor_get(x_3, 1);
x_140 = lean_ctor_get(x_3, 2);
x_141 = lean_ctor_get(x_3, 3);
x_142 = lean_ctor_get(x_3, 4);
x_143 = lean_ctor_get(x_3, 5);
x_144 = lean_ctor_get_uint8(x_3, sizeof(void*)*17);
x_145 = lean_ctor_get(x_3, 6);
x_146 = lean_ctor_get_uint8(x_3, sizeof(void*)*17 + 1);
x_147 = lean_ctor_get(x_3, 9);
x_148 = lean_ctor_get(x_3, 10);
x_149 = lean_ctor_get(x_3, 11);
x_150 = lean_ctor_get(x_3, 12);
x_151 = lean_ctor_get(x_3, 13);
x_152 = lean_ctor_get(x_3, 14);
x_153 = lean_ctor_get(x_3, 15);
x_154 = lean_ctor_get(x_3, 16);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_145);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_3);
lean_inc_ref_n(x_131, 2);
x_155 = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(x_155, 0, x_138);
lean_ctor_set(x_155, 1, x_139);
lean_ctor_set(x_155, 2, x_140);
lean_ctor_set(x_155, 3, x_141);
lean_ctor_set(x_155, 4, x_142);
lean_ctor_set(x_155, 5, x_143);
lean_ctor_set(x_155, 6, x_145);
lean_ctor_set(x_155, 7, x_131);
lean_ctor_set(x_155, 8, x_131);
lean_ctor_set(x_155, 9, x_147);
lean_ctor_set(x_155, 10, x_148);
lean_ctor_set(x_155, 11, x_149);
lean_ctor_set(x_155, 12, x_150);
lean_ctor_set(x_155, 13, x_151);
lean_ctor_set(x_155, 14, x_152);
lean_ctor_set(x_155, 15, x_153);
lean_ctor_set(x_155, 16, x_154);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_156 = x_131;
} else {
 lean_dec_ref(x_131);
 x_156 = lean_box(0);
}
lean_ctor_set_uint8(x_155, sizeof(void*)*17, x_144);
lean_ctor_set_uint8(x_155, sizeof(void*)*17 + 1, x_146);
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 1, 0);
} else {
 x_157 = x_156;
 lean_ctor_set_tag(x_157, 0);
}
lean_ctor_set(x_157, 0, x_155);
return x_157;
}
}
else
{
lean_object* x_158; 
lean_dec(x_131);
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_3);
return x_158;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[anonymous]", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(x_1, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0;
x_11 = lean_string_dec_eq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_inc(x_3);
x_12 = l_String_toName(x_3);
x_13 = l_Lean_Name_isAnonymous(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_free_object(x_7);
lean_dec(x_3);
x_14 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec_ref(x_14);
x_19 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_12, x_18, x_9);
x_1 = x_19;
x_2 = x_6;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_21 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1;
x_22 = lean_string_append(x_21, x_3);
lean_dec(x_3);
x_23 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2;
x_24 = lean_string_append(x_22, x_23);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
}
else
{
lean_object* x_25; 
lean_free_object(x_7);
lean_dec(x_3);
x_25 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec_ref(x_25);
x_30 = lean_box(0);
x_31 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_30, x_29, x_9);
x_1 = x_31;
x_2 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_7, 0);
lean_inc(x_33);
lean_dec(x_7);
x_34 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0;
x_35 = lean_string_dec_eq(x_3, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
lean_inc(x_3);
x_36 = l_String_toName(x_3);
x_37 = l_Lean_Name_isAnonymous(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_3);
x_38 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_6);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec_ref(x_38);
x_43 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_36, x_42, x_33);
x_1 = x_43;
x_2 = x_6;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_4);
x_45 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1;
x_46 = lean_string_append(x_45, x_3);
lean_dec(x_3);
x_47 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_3);
x_50 = l_Lean_Json_getStr_x3f(x_4);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_33);
lean_dec(x_6);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
lean_dec_ref(x_50);
x_55 = lean_box(0);
x_56 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_55, x_54, x_33);
x_1 = x_56;
x_2 = x_6;
goto _start;
}
}
}
}
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_1);
return x_58;
}
}
}
static lean_object* _init_l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected a `NameMap`, got '", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_box(1);
x_4 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0;
x_6 = lean_unsigned_to_nat(80u);
x_7 = l_Lean_Json_pretty(x_1, x_6);
x_8 = lean_string_append(x_5, x_7);
lean_dec_ref(x_7);
x_9 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
static lean_object* _init_l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_PKG_URL_MAP", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'LAKE_PKG_URL_MAP' has invalid JSON: ", 37, 37);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0;
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = l_Lean_Json_parse(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_4 = x_11;
goto block_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_4 = x_14;
goto block_8;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_ctor_set_tag(x_13, 0);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
block_8:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
x_15 = l_String_Slice_Pos_prev_x3f(x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint32_t x_16; 
lean_dec_ref(x_14);
x_16 = 65;
x_2 = x_16;
goto block_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_String_Slice_Pos_get_x3f(x_14, x_17);
lean_dec(x_17);
lean_dec_ref(x_14);
if (lean_obj_tag(x_18) == 0)
{
uint32_t x_19; 
x_19 = 65;
x_2 = x_19;
goto block_11;
}
else
{
lean_object* x_20; uint32_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_unbox_uint32(x_20);
lean_dec(x_20);
x_2 = x_21;
goto block_11;
}
}
block_11:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 47;
x_4 = lean_uint32_dec_eq(x_2, x_3);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_String_Slice_Pos_prevn(x_8, x_7, x_5);
lean_dec_ref(x_8);
x_10 = lean_string_utf8_extract(x_1, x_6, x_9);
lean_dec(x_9);
lean_dec_ref(x_1);
return x_10;
}
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
x_1 = lean_mk_string_unchecked("LAKE_ARTIFACT_CACHE", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_CACHE_KEY", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_CACHE_ARTIFACT_ENDPOINT", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_CACHE_REVISION_ENDPOINT", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_GITHASH", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_PATH", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SRC_PATH", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PATH", 4, 4);
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
x_1 = lean_mk_string_unchecked("RESERVOIR_API_URL", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/v1", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_compute___closed__12() {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = l_Lake_Env_compute___closed__9;
x_190 = lean_io_getenv(x_189);
if (lean_obj_tag(x_190) == 1)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_190, 0);
lean_inc(x_205);
lean_dec_ref(x_190);
x_206 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_205);
x_191 = x_206;
goto block_204;
}
else
{
lean_object* x_207; 
lean_dec(x_190);
x_207 = l_Lake_Env_compute___closed__12;
x_191 = x_207;
goto block_204;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
lean_inc_ref(x_12);
lean_inc(x_13);
lean_inc(x_3);
x_22 = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_6);
lean_ctor_set(x_22, 4, x_18);
lean_ctor_set(x_22, 5, x_7);
lean_ctor_set(x_22, 6, x_9);
lean_ctor_set(x_22, 7, x_13);
lean_ctor_set(x_22, 8, x_13);
lean_ctor_set(x_22, 9, x_8);
lean_ctor_set(x_22, 10, x_17);
lean_ctor_set(x_22, 11, x_21);
lean_ctor_set(x_22, 12, x_14);
lean_ctor_set(x_22, 13, x_10);
lean_ctor_set(x_22, 14, x_20);
lean_ctor_set(x_22, 15, x_15);
lean_ctor_set(x_22, 16, x_12);
lean_ctor_set_uint8(x_22, sizeof(void*)*17, x_11);
lean_ctor_set_uint8(x_22, sizeof(void*)*17 + 1, x_16);
x_23 = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(x_3, x_12, x_22);
lean_dec_ref(x_12);
return x_23;
}
block_47:
{
if (lean_obj_tag(x_37) == 0)
{
x_6 = x_25;
x_7 = x_26;
x_8 = x_27;
x_9 = x_28;
x_10 = x_29;
x_11 = x_30;
x_12 = x_31;
x_13 = x_32;
x_14 = x_33;
x_15 = x_34;
x_16 = x_35;
x_17 = x_40;
x_18 = x_36;
x_19 = lean_box(0);
x_20 = x_38;
x_21 = x_37;
goto block_24;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_42);
lean_ctor_set(x_37, 0, x_43);
x_6 = x_25;
x_7 = x_26;
x_8 = x_27;
x_9 = x_28;
x_10 = x_29;
x_11 = x_30;
x_12 = x_31;
x_13 = x_32;
x_14 = x_33;
x_15 = x_34;
x_16 = x_35;
x_17 = x_40;
x_18 = x_36;
x_19 = lean_box(0);
x_20 = x_38;
x_21 = x_37;
goto block_24;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
x_45 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_6 = x_25;
x_7 = x_26;
x_8 = x_27;
x_9 = x_28;
x_10 = x_29;
x_11 = x_30;
x_12 = x_31;
x_13 = x_32;
x_14 = x_33;
x_15 = x_34;
x_16 = x_35;
x_17 = x_40;
x_18 = x_36;
x_19 = lean_box(0);
x_20 = x_38;
x_21 = x_46;
goto block_24;
}
}
}
block_70:
{
if (lean_obj_tag(x_53) == 0)
{
x_25 = x_48;
x_26 = x_49;
x_27 = x_63;
x_28 = x_50;
x_29 = x_51;
x_30 = x_52;
x_31 = x_54;
x_32 = x_55;
x_33 = x_56;
x_34 = x_57;
x_35 = x_58;
x_36 = x_59;
x_37 = x_61;
x_38 = x_62;
x_39 = lean_box(0);
x_40 = x_53;
goto block_47;
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_53);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_53, 0);
x_66 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_65);
lean_ctor_set(x_53, 0, x_66);
x_25 = x_48;
x_26 = x_49;
x_27 = x_63;
x_28 = x_50;
x_29 = x_51;
x_30 = x_52;
x_31 = x_54;
x_32 = x_55;
x_33 = x_56;
x_34 = x_57;
x_35 = x_58;
x_36 = x_59;
x_37 = x_61;
x_38 = x_62;
x_39 = lean_box(0);
x_40 = x_53;
goto block_47;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_53, 0);
lean_inc(x_67);
lean_dec(x_53);
x_68 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_25 = x_48;
x_26 = x_49;
x_27 = x_63;
x_28 = x_50;
x_29 = x_51;
x_30 = x_52;
x_31 = x_54;
x_32 = x_55;
x_33 = x_56;
x_34 = x_57;
x_35 = x_58;
x_36 = x_59;
x_37 = x_61;
x_38 = x_62;
x_39 = lean_box(0);
x_40 = x_69;
goto block_47;
}
}
}
block_107:
{
uint8_t x_85; lean_object* x_86; 
x_85 = 0;
x_86 = lean_box(0);
if (lean_obj_tag(x_79) == 0)
{
x_48 = x_71;
x_49 = x_72;
x_50 = x_84;
x_51 = x_73;
x_52 = x_74;
x_53 = x_75;
x_54 = x_76;
x_55 = x_86;
x_56 = x_77;
x_57 = x_78;
x_58 = x_85;
x_59 = x_80;
x_60 = lean_box(0);
x_61 = x_82;
x_62 = x_83;
x_63 = x_79;
goto block_70;
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_79);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_88 = lean_ctor_get(x_79, 0);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_string_utf8_byte_size(x_88);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
lean_ctor_set(x_91, 2, x_90);
x_92 = l_String_Slice_trimAscii(x_91);
lean_dec_ref(x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 2);
lean_inc(x_95);
lean_dec_ref(x_92);
x_96 = lean_string_utf8_extract(x_93, x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_ctor_set(x_79, 0, x_96);
x_48 = x_71;
x_49 = x_72;
x_50 = x_84;
x_51 = x_73;
x_52 = x_74;
x_53 = x_75;
x_54 = x_76;
x_55 = x_86;
x_56 = x_77;
x_57 = x_78;
x_58 = x_85;
x_59 = x_80;
x_60 = lean_box(0);
x_61 = x_82;
x_62 = x_83;
x_63 = x_79;
goto block_70;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_97 = lean_ctor_get(x_79, 0);
lean_inc(x_97);
lean_dec(x_79);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_string_utf8_byte_size(x_97);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
lean_ctor_set(x_100, 2, x_99);
x_101 = l_String_Slice_trimAscii(x_100);
lean_dec_ref(x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 2);
lean_inc(x_104);
lean_dec_ref(x_101);
x_105 = lean_string_utf8_extract(x_102, x_103, x_104);
lean_dec(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_48 = x_71;
x_49 = x_72;
x_50 = x_84;
x_51 = x_73;
x_52 = x_74;
x_53 = x_75;
x_54 = x_76;
x_55 = x_86;
x_56 = x_77;
x_57 = x_78;
x_58 = x_85;
x_59 = x_80;
x_60 = lean_box(0);
x_61 = x_82;
x_62 = x_83;
x_63 = x_106;
goto block_70;
}
}
}
block_125:
{
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_122; 
x_122 = lean_box(0);
x_71 = x_108;
x_72 = x_109;
x_73 = x_110;
x_74 = x_121;
x_75 = x_111;
x_76 = x_112;
x_77 = x_114;
x_78 = x_115;
x_79 = x_116;
x_80 = x_117;
x_81 = lean_box(0);
x_82 = x_119;
x_83 = x_120;
x_84 = x_122;
goto block_107;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_113, 0);
lean_inc(x_123);
lean_dec_ref(x_113);
x_124 = l_Lake_envToBool_x3f(x_123);
x_71 = x_108;
x_72 = x_109;
x_73 = x_110;
x_74 = x_121;
x_75 = x_111;
x_76 = x_112;
x_77 = x_114;
x_78 = x_115;
x_79 = x_116;
x_80 = x_117;
x_81 = lean_box(0);
x_82 = x_119;
x_83 = x_120;
x_84 = x_124;
goto block_107;
}
}
block_140:
{
uint8_t x_139; 
x_139 = 0;
x_108 = x_126;
x_109 = x_127;
x_110 = x_128;
x_111 = x_129;
x_112 = x_130;
x_113 = x_131;
x_114 = x_132;
x_115 = x_133;
x_116 = x_134;
x_117 = x_135;
x_118 = lean_box(0);
x_119 = x_137;
x_120 = x_138;
x_121 = x_139;
goto block_125;
}
block_161:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_145) == 0)
{
x_126 = x_141;
x_127 = x_142;
x_128 = x_143;
x_129 = x_144;
x_130 = x_146;
x_131 = x_147;
x_132 = x_148;
x_133 = x_149;
x_134 = x_150;
x_135 = x_154;
x_136 = lean_box(0);
x_137 = x_152;
x_138 = x_153;
goto block_140;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_145, 0);
lean_inc(x_155);
lean_dec_ref(x_145);
x_156 = l_Lake_envToBool_x3f(x_155);
if (lean_obj_tag(x_156) == 0)
{
x_126 = x_141;
x_127 = x_142;
x_128 = x_143;
x_129 = x_144;
x_130 = x_146;
x_131 = x_147;
x_132 = x_148;
x_133 = x_149;
x_134 = x_150;
x_135 = x_154;
x_136 = lean_box(0);
x_137 = x_152;
x_138 = x_153;
goto block_140;
}
else
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
lean_dec_ref(x_156);
x_158 = lean_unbox(x_157);
lean_dec(x_157);
x_108 = x_141;
x_109 = x_142;
x_110 = x_143;
x_111 = x_144;
x_112 = x_146;
x_113 = x_147;
x_114 = x_148;
x_115 = x_149;
x_116 = x_150;
x_117 = x_154;
x_118 = lean_box(0);
x_119 = x_152;
x_120 = x_153;
x_121 = x_158;
goto block_125;
}
}
}
else
{
lean_object* x_159; uint8_t x_160; 
lean_dec(x_145);
x_159 = lean_ctor_get(x_4, 0);
x_160 = lean_unbox(x_159);
x_108 = x_141;
x_109 = x_142;
x_110 = x_143;
x_111 = x_144;
x_112 = x_146;
x_113 = x_147;
x_114 = x_148;
x_115 = x_149;
x_116 = x_150;
x_117 = x_154;
x_118 = lean_box(0);
x_119 = x_152;
x_120 = x_153;
x_121 = x_160;
goto block_125;
}
}
block_188:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_166 = l_Lake_Env_compute___closed__0;
x_167 = lean_io_getenv(x_166);
x_168 = l_Lake_Env_compute___closed__1;
x_169 = lean_io_getenv(x_168);
x_170 = l_Lake_Env_compute___closed__2;
x_171 = lean_io_getenv(x_170);
x_172 = l_Lake_Env_compute___closed__3;
x_173 = lean_io_getenv(x_172);
x_174 = l_Lake_Env_compute___closed__4;
x_175 = lean_io_getenv(x_174);
x_176 = l_Lake_Env_compute___closed__5;
x_177 = lean_io_getenv(x_176);
x_178 = l_Lake_Env_compute___closed__6;
x_179 = l_Lake_getSearchPath(x_178);
x_180 = l_Lake_Env_compute___closed__7;
x_181 = l_Lake_getSearchPath(x_180);
x_182 = l_Lake_sharedLibPathEnvVar;
x_183 = l_Lake_getSearchPath(x_182);
x_184 = l_Lake_Env_compute___closed__8;
x_185 = l_Lake_getSearchPath(x_184);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_186; 
x_186 = l_Lake_instInhabitedEnv_default___closed__0;
x_141 = x_164;
x_142 = x_162;
x_143 = x_181;
x_144 = x_173;
x_145 = x_167;
x_146 = x_163;
x_147 = x_169;
x_148 = x_179;
x_149 = x_185;
x_150 = x_171;
x_151 = lean_box(0);
x_152 = x_175;
x_153 = x_183;
x_154 = x_186;
goto block_161;
}
else
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_177, 0);
lean_inc(x_187);
lean_dec_ref(x_177);
x_141 = x_164;
x_142 = x_162;
x_143 = x_181;
x_144 = x_173;
x_145 = x_167;
x_146 = x_163;
x_147 = x_169;
x_148 = x_179;
x_149 = x_185;
x_150 = x_171;
x_151 = lean_box(0);
x_152 = x_175;
x_153 = x_183;
x_154 = x_187;
goto block_161;
}
}
block_204:
{
lean_object* x_192; lean_object* x_193; 
x_192 = l_Lake_Env_computeToolchain();
x_193 = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec_ref(x_193);
x_195 = l_Lake_Env_compute___closed__10;
x_196 = lean_io_getenv(x_195);
if (lean_obj_tag(x_196) == 1)
{
lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_191);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec_ref(x_196);
x_198 = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(x_197);
x_162 = x_194;
x_163 = x_192;
x_164 = x_198;
x_165 = lean_box(0);
goto block_188;
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_196);
x_199 = l_Lake_Env_compute___closed__11;
x_200 = lean_string_append(x_191, x_199);
x_162 = x_194;
x_163 = x_192;
x_164 = x_200;
x_165 = lean_box(0);
goto block_188;
}
}
else
{
uint8_t x_201; 
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_201 = !lean_is_exclusive(x_193);
if (x_201 == 0)
{
return x_193;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_193, 0);
lean_inc(x_202);
lean_dec(x_193);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
return x_203;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Env_compute(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
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
if (x_6 == 0)
{
lean_inc_ref(x_3);
return x_3;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_leanGithash(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 15);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_3, 6);
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
lean_inc_ref(x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_4);
lean_inc_ref(x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_inc(x_4);
lean_inc_ref(x_6);
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
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 12);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
lean_inc_ref(x_4);
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
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 13);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_inc_ref(x_4);
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
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 14);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lake_LeanInstall_sharedLibPath(x_2);
lean_dec_ref(x_2);
x_5 = l_List_appendTR___redArg(x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_computeToolchain___closed__0;
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_noToolchainVars___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_compute___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SYSROOT", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_noToolchainVars___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_AR", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Env_noToolchainVars___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__0;
x_2 = l_Lake_Env_noToolchainVars___closed__14;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Env_noToolchainVars___closed__2;
x_2 = l_Lake_Env_noToolchainVars___closed__15;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instInhabitedEnv_default___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_noToolchainVars(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*17 + 1);
x_3 = lean_ctor_get(x_1, 8);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_box(0);
x_5 = l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0;
if (x_2 == 0)
{
if (lean_obj_tag(x_3) == 0)
{
x_6 = x_4;
goto block_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_6 = x_3;
goto block_22;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_6 = x_25;
goto block_22;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_3);
x_26 = l_Lake_Env_noToolchainVars___closed__17;
x_6 = x_26;
goto block_22;
}
block_22:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lake_Env_noToolchainVars___closed__4;
x_9 = l_Lake_Env_noToolchainVars___closed__6;
x_10 = l_Lake_Env_noToolchainVars___closed__8;
x_11 = l_Lake_Env_noToolchainVars___closed__9;
x_12 = l_Lake_Env_noToolchainVars___closed__11;
x_13 = l_Lake_Env_noToolchainVars___closed__13;
x_14 = l_Lake_Env_noToolchainVars___closed__16;
x_15 = lean_array_push(x_14, x_7);
x_16 = lean_array_push(x_15, x_8);
x_17 = lean_array_push(x_16, x_9);
x_18 = lean_array_push(x_17, x_10);
x_19 = lean_array_push(x_18, x_11);
x_20 = lean_array_push(x_19, x_12);
x_21 = lean_array_push(x_20, x_13);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(1);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.Data.DTreeMap.Internal.Balancing", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.balanceR!", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("balanceR! input was not balanced", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2;
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_unsigned_to_nat(272u);
x_4 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1;
x_5 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2;
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(273u);
x_4 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1;
x_5 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.balanceL!", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("balanceL! input was not balanced", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6;
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_unsigned_to_nat(178u);
x_4 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5;
x_5 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6;
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(179u);
x_4 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5;
x_5 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = lean_string_dec_lt(x_1, x_5);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_string_dec_eq(x_1, x_5);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(x_1, x_2, x_8);
if (lean_obj_tag(x_7) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 4);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_mul(x_19, x_13);
x_21 = lean_nat_dec_lt(x_20, x_14);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_22, x_13);
x_24 = lean_nat_add(x_23, x_14);
lean_dec(x_14);
lean_dec(x_23);
if (lean_is_scalar(x_9)) {
 x_25 = lean_alloc_ctor(0, 5, 0);
} else {
 x_25 = x_9;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_6);
lean_ctor_set(x_25, 3, x_7);
lean_ctor_set(x_25, 4, x_12);
return x_25;
}
else
{
lean_object* x_26; 
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_26 = x_12;
} else {
 lean_dec_ref(x_12);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
x_29 = lean_ctor_get(x_17, 2);
x_30 = lean_ctor_get(x_17, 3);
x_31 = lean_ctor_get(x_17, 4);
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_mul(x_33, x_32);
x_35 = lean_nat_dec_lt(x_27, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_47; 
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 x_36 = x_17;
} else {
 lean_dec_ref(x_17);
 x_36 = lean_box(0);
}
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_37, x_13);
x_39 = lean_nat_add(x_38, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_30, 0);
lean_inc(x_54);
x_47 = x_54;
goto block_53;
}
else
{
lean_object* x_55; 
x_55 = lean_unsigned_to_nat(0u);
x_47 = x_55;
goto block_53;
}
block_46:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_nat_add(x_40, x_42);
lean_dec(x_42);
lean_dec(x_40);
if (lean_is_scalar(x_36)) {
 x_44 = lean_alloc_ctor(0, 5, 0);
} else {
 x_44 = x_36;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_15);
lean_ctor_set(x_44, 2, x_16);
lean_ctor_set(x_44, 3, x_31);
lean_ctor_set(x_44, 4, x_18);
if (lean_is_scalar(x_26)) {
 x_45 = lean_alloc_ctor(0, 5, 0);
} else {
 x_45 = x_26;
}
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_28);
lean_ctor_set(x_45, 2, x_29);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set(x_45, 4, x_44);
return x_45;
}
block_53:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_nat_add(x_38, x_47);
lean_dec(x_47);
lean_dec(x_38);
if (lean_is_scalar(x_9)) {
 x_49 = lean_alloc_ctor(0, 5, 0);
} else {
 x_49 = x_9;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_5);
lean_ctor_set(x_49, 2, x_6);
lean_ctor_set(x_49, 3, x_7);
lean_ctor_set(x_49, 4, x_30);
x_50 = lean_nat_add(x_37, x_32);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_31, 0);
lean_inc(x_51);
x_40 = x_50;
x_41 = x_49;
x_42 = x_51;
goto block_46;
}
else
{
lean_object* x_52; 
x_52 = lean_unsigned_to_nat(0u);
x_40 = x_50;
x_41 = x_49;
x_42 = x_52;
goto block_46;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_9);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_56, x_13);
x_58 = lean_nat_add(x_57, x_14);
lean_dec(x_14);
x_59 = lean_nat_add(x_57, x_27);
lean_dec(x_57);
lean_inc_ref(x_7);
if (lean_is_scalar(x_26)) {
 x_60 = lean_alloc_ctor(0, 5, 0);
} else {
 x_60 = x_26;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_5);
lean_ctor_set(x_60, 2, x_6);
lean_ctor_set(x_60, 3, x_7);
lean_ctor_set(x_60, 4, x_17);
x_61 = !lean_is_exclusive(x_7);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_7, 4);
lean_dec(x_62);
x_63 = lean_ctor_get(x_7, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_7, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_7, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_7, 0);
lean_dec(x_66);
lean_ctor_set(x_7, 4, x_18);
lean_ctor_set(x_7, 3, x_60);
lean_ctor_set(x_7, 2, x_16);
lean_ctor_set(x_7, 1, x_15);
lean_ctor_set(x_7, 0, x_58);
return x_7;
}
else
{
lean_object* x_67; 
lean_dec(x_7);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_15);
lean_ctor_set(x_67, 2, x_16);
lean_ctor_set(x_67, 3, x_60);
lean_ctor_set(x_67, 4, x_18);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_26);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_68 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3;
x_69 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_70 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4;
x_71 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_7, 0);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_73, x_72);
if (lean_is_scalar(x_9)) {
 x_75 = lean_alloc_ctor(0, 5, 0);
} else {
 x_75 = x_9;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_5);
lean_ctor_set(x_75, 2, x_6);
lean_ctor_set(x_75, 3, x_7);
lean_ctor_set(x_75, 4, x_12);
return x_75;
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_12, 3);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_12, 4);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_12);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_12, 0);
x_80 = lean_ctor_get(x_12, 1);
x_81 = lean_ctor_get(x_12, 2);
x_82 = lean_ctor_get(x_12, 4);
lean_dec(x_82);
x_83 = lean_ctor_get(x_12, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_76, 0);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_85, x_79);
lean_dec(x_79);
x_87 = lean_nat_add(x_85, x_84);
lean_ctor_set(x_12, 4, x_76);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 0, x_87);
if (lean_is_scalar(x_9)) {
 x_88 = lean_alloc_ctor(0, 5, 0);
} else {
 x_88 = x_9;
}
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_80);
lean_ctor_set(x_88, 2, x_81);
lean_ctor_set(x_88, 3, x_12);
lean_ctor_set(x_88, 4, x_77);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_89 = lean_ctor_get(x_12, 0);
x_90 = lean_ctor_get(x_12, 1);
x_91 = lean_ctor_get(x_12, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_12);
x_92 = lean_ctor_get(x_76, 0);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_93, x_89);
lean_dec(x_89);
x_95 = lean_nat_add(x_93, x_92);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_5);
lean_ctor_set(x_96, 2, x_6);
lean_ctor_set(x_96, 3, x_7);
lean_ctor_set(x_96, 4, x_76);
if (lean_is_scalar(x_9)) {
 x_97 = lean_alloc_ctor(0, 5, 0);
} else {
 x_97 = x_9;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_90);
lean_ctor_set(x_97, 2, x_91);
lean_ctor_set(x_97, 3, x_96);
lean_ctor_set(x_97, 4, x_77);
return x_97;
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_12);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_12, 4);
lean_dec(x_99);
x_100 = lean_ctor_get(x_12, 3);
lean_dec(x_100);
x_101 = lean_ctor_get(x_12, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_76);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_103 = lean_ctor_get(x_76, 1);
x_104 = lean_ctor_get(x_76, 2);
x_105 = lean_ctor_get(x_76, 4);
lean_dec(x_105);
x_106 = lean_ctor_get(x_76, 3);
lean_dec(x_106);
x_107 = lean_ctor_get(x_76, 0);
lean_dec(x_107);
x_108 = lean_unsigned_to_nat(3u);
x_109 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_76, 4, x_77);
lean_ctor_set(x_76, 3, x_77);
lean_ctor_set(x_76, 2, x_6);
lean_ctor_set(x_76, 1, x_5);
lean_ctor_set(x_76, 0, x_109);
lean_ctor_set(x_12, 3, x_77);
lean_ctor_set(x_12, 0, x_109);
if (lean_is_scalar(x_9)) {
 x_110 = lean_alloc_ctor(0, 5, 0);
} else {
 x_110 = x_9;
}
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_103);
lean_ctor_set(x_110, 2, x_104);
lean_ctor_set(x_110, 3, x_76);
lean_ctor_set(x_110, 4, x_12);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_76, 1);
x_112 = lean_ctor_get(x_76, 2);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_76);
x_113 = lean_unsigned_to_nat(3u);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_5);
lean_ctor_set(x_115, 2, x_6);
lean_ctor_set(x_115, 3, x_77);
lean_ctor_set(x_115, 4, x_77);
lean_ctor_set(x_12, 3, x_77);
lean_ctor_set(x_12, 0, x_114);
if (lean_is_scalar(x_9)) {
 x_116 = lean_alloc_ctor(0, 5, 0);
} else {
 x_116 = x_9;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_111);
lean_ctor_set(x_116, 2, x_112);
lean_ctor_set(x_116, 3, x_115);
lean_ctor_set(x_116, 4, x_12);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_117 = lean_ctor_get(x_12, 1);
x_118 = lean_ctor_get(x_12, 2);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_12);
x_119 = lean_ctor_get(x_76, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_76, 2);
lean_inc(x_120);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 lean_ctor_release(x_76, 3);
 lean_ctor_release(x_76, 4);
 x_121 = x_76;
} else {
 lean_dec_ref(x_76);
 x_121 = lean_box(0);
}
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_121)) {
 x_124 = lean_alloc_ctor(0, 5, 0);
} else {
 x_124 = x_121;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_5);
lean_ctor_set(x_124, 2, x_6);
lean_ctor_set(x_124, 3, x_77);
lean_ctor_set(x_124, 4, x_77);
x_125 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_117);
lean_ctor_set(x_125, 2, x_118);
lean_ctor_set(x_125, 3, x_77);
lean_ctor_set(x_125, 4, x_77);
if (lean_is_scalar(x_9)) {
 x_126 = lean_alloc_ctor(0, 5, 0);
} else {
 x_126 = x_9;
}
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_119);
lean_ctor_set(x_126, 2, x_120);
lean_ctor_set(x_126, 3, x_124);
lean_ctor_set(x_126, 4, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_12, 4);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_12);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_129 = lean_ctor_get(x_12, 1);
x_130 = lean_ctor_get(x_12, 2);
x_131 = lean_ctor_get(x_12, 4);
lean_dec(x_131);
x_132 = lean_ctor_get(x_12, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_12, 0);
lean_dec(x_133);
x_134 = lean_unsigned_to_nat(3u);
x_135 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_12, 4, x_76);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 0, x_135);
if (lean_is_scalar(x_9)) {
 x_136 = lean_alloc_ctor(0, 5, 0);
} else {
 x_136 = x_9;
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_129);
lean_ctor_set(x_136, 2, x_130);
lean_ctor_set(x_136, 3, x_12);
lean_ctor_set(x_136, 4, x_127);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_ctor_get(x_12, 1);
x_138 = lean_ctor_get(x_12, 2);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_12);
x_139 = lean_unsigned_to_nat(3u);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_5);
lean_ctor_set(x_141, 2, x_6);
lean_ctor_set(x_141, 3, x_76);
lean_ctor_set(x_141, 4, x_76);
if (lean_is_scalar(x_9)) {
 x_142 = lean_alloc_ctor(0, 5, 0);
} else {
 x_142 = x_9;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_137);
lean_ctor_set(x_142, 2, x_138);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set(x_142, 4, x_127);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_144 = lean_alloc_ctor(0, 5, 0);
} else {
 x_144 = x_9;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_5);
lean_ctor_set(x_144, 2, x_6);
lean_ctor_set(x_144, 3, x_127);
lean_ctor_set(x_144, 4, x_12);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_9)) {
 x_146 = lean_alloc_ctor(0, 5, 0);
} else {
 x_146 = x_9;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_5);
lean_ctor_set(x_146, 2, x_6);
lean_ctor_set(x_146, 3, x_12);
lean_ctor_set(x_146, 4, x_12);
return x_146;
}
}
}
else
{
lean_object* x_147; 
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_9)) {
 x_147 = lean_alloc_ctor(0, 5, 0);
} else {
 x_147 = x_9;
}
lean_ctor_set(x_147, 0, x_4);
lean_ctor_set(x_147, 1, x_1);
lean_ctor_set(x_147, 2, x_2);
lean_ctor_set(x_147, 3, x_7);
lean_ctor_set(x_147, 4, x_8);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_dec(x_4);
x_148 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(x_1, x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_149 = lean_ctor_get(x_8, 0);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_148, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_148, 3);
lean_inc(x_153);
x_154 = lean_ctor_get(x_148, 4);
lean_inc(x_154);
x_155 = lean_unsigned_to_nat(3u);
x_156 = lean_nat_mul(x_155, x_149);
x_157 = lean_nat_dec_lt(x_156, x_150);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_nat_add(x_158, x_150);
lean_dec(x_150);
x_160 = lean_nat_add(x_159, x_149);
lean_dec(x_159);
if (lean_is_scalar(x_9)) {
 x_161 = lean_alloc_ctor(0, 5, 0);
} else {
 x_161 = x_9;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_5);
lean_ctor_set(x_161, 2, x_6);
lean_ctor_set(x_161, 3, x_148);
lean_ctor_set(x_161, 4, x_8);
return x_161;
}
else
{
lean_object* x_162; 
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 lean_ctor_release(x_148, 4);
 x_162 = x_148;
} else {
 lean_dec_ref(x_148);
 x_162 = lean_box(0);
}
if (lean_obj_tag(x_153) == 0)
{
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_163 = lean_ctor_get(x_153, 0);
x_164 = lean_ctor_get(x_154, 0);
x_165 = lean_ctor_get(x_154, 1);
x_166 = lean_ctor_get(x_154, 2);
x_167 = lean_ctor_get(x_154, 3);
x_168 = lean_ctor_get(x_154, 4);
x_169 = lean_unsigned_to_nat(2u);
x_170 = lean_nat_mul(x_169, x_163);
x_171 = lean_nat_dec_lt(x_164, x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_183; lean_object* x_184; 
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 lean_ctor_release(x_154, 2);
 lean_ctor_release(x_154, 3);
 lean_ctor_release(x_154, 4);
 x_172 = x_154;
} else {
 lean_dec_ref(x_154);
 x_172 = lean_box(0);
}
x_173 = lean_unsigned_to_nat(1u);
x_174 = lean_nat_add(x_173, x_150);
lean_dec(x_150);
x_175 = lean_nat_add(x_174, x_149);
lean_dec(x_174);
x_183 = lean_nat_add(x_173, x_163);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_167, 0);
lean_inc(x_191);
x_184 = x_191;
goto block_190;
}
else
{
lean_object* x_192; 
x_192 = lean_unsigned_to_nat(0u);
x_184 = x_192;
goto block_190;
}
block_182:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_nat_add(x_177, x_178);
lean_dec(x_178);
lean_dec(x_177);
if (lean_is_scalar(x_172)) {
 x_180 = lean_alloc_ctor(0, 5, 0);
} else {
 x_180 = x_172;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_5);
lean_ctor_set(x_180, 2, x_6);
lean_ctor_set(x_180, 3, x_168);
lean_ctor_set(x_180, 4, x_8);
if (lean_is_scalar(x_162)) {
 x_181 = lean_alloc_ctor(0, 5, 0);
} else {
 x_181 = x_162;
}
lean_ctor_set(x_181, 0, x_175);
lean_ctor_set(x_181, 1, x_165);
lean_ctor_set(x_181, 2, x_166);
lean_ctor_set(x_181, 3, x_176);
lean_ctor_set(x_181, 4, x_180);
return x_181;
}
block_190:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_nat_add(x_183, x_184);
lean_dec(x_184);
lean_dec(x_183);
if (lean_is_scalar(x_9)) {
 x_186 = lean_alloc_ctor(0, 5, 0);
} else {
 x_186 = x_9;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_151);
lean_ctor_set(x_186, 2, x_152);
lean_ctor_set(x_186, 3, x_153);
lean_ctor_set(x_186, 4, x_167);
x_187 = lean_nat_add(x_173, x_149);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_168, 0);
lean_inc(x_188);
x_176 = x_186;
x_177 = x_187;
x_178 = x_188;
goto block_182;
}
else
{
lean_object* x_189; 
x_189 = lean_unsigned_to_nat(0u);
x_176 = x_186;
x_177 = x_187;
x_178 = x_189;
goto block_182;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_9);
x_193 = lean_unsigned_to_nat(1u);
x_194 = lean_nat_add(x_193, x_150);
lean_dec(x_150);
x_195 = lean_nat_add(x_194, x_149);
lean_dec(x_194);
x_196 = lean_nat_add(x_193, x_149);
x_197 = lean_nat_add(x_196, x_164);
lean_dec(x_196);
lean_inc_ref(x_8);
if (lean_is_scalar(x_162)) {
 x_198 = lean_alloc_ctor(0, 5, 0);
} else {
 x_198 = x_162;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_5);
lean_ctor_set(x_198, 2, x_6);
lean_ctor_set(x_198, 3, x_154);
lean_ctor_set(x_198, 4, x_8);
x_199 = !lean_is_exclusive(x_8);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_8, 4);
lean_dec(x_200);
x_201 = lean_ctor_get(x_8, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_8, 2);
lean_dec(x_202);
x_203 = lean_ctor_get(x_8, 1);
lean_dec(x_203);
x_204 = lean_ctor_get(x_8, 0);
lean_dec(x_204);
lean_ctor_set(x_8, 4, x_198);
lean_ctor_set(x_8, 3, x_153);
lean_ctor_set(x_8, 2, x_152);
lean_ctor_set(x_8, 1, x_151);
lean_ctor_set(x_8, 0, x_195);
return x_8;
}
else
{
lean_object* x_205; 
lean_dec(x_8);
x_205 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_205, 0, x_195);
lean_ctor_set(x_205, 1, x_151);
lean_ctor_set(x_205, 2, x_152);
lean_ctor_set(x_205, 3, x_153);
lean_ctor_set(x_205, 4, x_198);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_162);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_206 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7;
x_207 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_206);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_162);
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_208 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8;
x_209 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_208);
return x_209;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_8, 0);
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_nat_add(x_211, x_210);
if (lean_is_scalar(x_9)) {
 x_213 = lean_alloc_ctor(0, 5, 0);
} else {
 x_213 = x_9;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_5);
lean_ctor_set(x_213, 2, x_6);
lean_ctor_set(x_213, 3, x_148);
lean_ctor_set(x_213, 4, x_8);
return x_213;
}
}
else
{
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_148, 3);
lean_inc(x_214);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_148, 4);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_148);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_217 = lean_ctor_get(x_148, 0);
x_218 = lean_ctor_get(x_148, 1);
x_219 = lean_ctor_get(x_148, 2);
x_220 = lean_ctor_get(x_148, 4);
lean_dec(x_220);
x_221 = lean_ctor_get(x_148, 3);
lean_dec(x_221);
x_222 = lean_ctor_get(x_215, 0);
x_223 = lean_unsigned_to_nat(1u);
x_224 = lean_nat_add(x_223, x_217);
lean_dec(x_217);
x_225 = lean_nat_add(x_223, x_222);
lean_ctor_set(x_148, 4, x_8);
lean_ctor_set(x_148, 3, x_215);
lean_ctor_set(x_148, 2, x_6);
lean_ctor_set(x_148, 1, x_5);
lean_ctor_set(x_148, 0, x_225);
if (lean_is_scalar(x_9)) {
 x_226 = lean_alloc_ctor(0, 5, 0);
} else {
 x_226 = x_9;
}
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_218);
lean_ctor_set(x_226, 2, x_219);
lean_ctor_set(x_226, 3, x_214);
lean_ctor_set(x_226, 4, x_148);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_227 = lean_ctor_get(x_148, 0);
x_228 = lean_ctor_get(x_148, 1);
x_229 = lean_ctor_get(x_148, 2);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_148);
x_230 = lean_ctor_get(x_215, 0);
x_231 = lean_unsigned_to_nat(1u);
x_232 = lean_nat_add(x_231, x_227);
lean_dec(x_227);
x_233 = lean_nat_add(x_231, x_230);
x_234 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_5);
lean_ctor_set(x_234, 2, x_6);
lean_ctor_set(x_234, 3, x_215);
lean_ctor_set(x_234, 4, x_8);
if (lean_is_scalar(x_9)) {
 x_235 = lean_alloc_ctor(0, 5, 0);
} else {
 x_235 = x_9;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_228);
lean_ctor_set(x_235, 2, x_229);
lean_ctor_set(x_235, 3, x_214);
lean_ctor_set(x_235, 4, x_234);
return x_235;
}
}
else
{
uint8_t x_236; 
x_236 = !lean_is_exclusive(x_148);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_237 = lean_ctor_get(x_148, 1);
x_238 = lean_ctor_get(x_148, 2);
x_239 = lean_ctor_get(x_148, 4);
lean_dec(x_239);
x_240 = lean_ctor_get(x_148, 3);
lean_dec(x_240);
x_241 = lean_ctor_get(x_148, 0);
lean_dec(x_241);
x_242 = lean_unsigned_to_nat(3u);
x_243 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_148, 3, x_215);
lean_ctor_set(x_148, 2, x_6);
lean_ctor_set(x_148, 1, x_5);
lean_ctor_set(x_148, 0, x_243);
if (lean_is_scalar(x_9)) {
 x_244 = lean_alloc_ctor(0, 5, 0);
} else {
 x_244 = x_9;
}
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_237);
lean_ctor_set(x_244, 2, x_238);
lean_ctor_set(x_244, 3, x_214);
lean_ctor_set(x_244, 4, x_148);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_245 = lean_ctor_get(x_148, 1);
x_246 = lean_ctor_get(x_148, 2);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_148);
x_247 = lean_unsigned_to_nat(3u);
x_248 = lean_unsigned_to_nat(1u);
x_249 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_5);
lean_ctor_set(x_249, 2, x_6);
lean_ctor_set(x_249, 3, x_215);
lean_ctor_set(x_249, 4, x_215);
if (lean_is_scalar(x_9)) {
 x_250 = lean_alloc_ctor(0, 5, 0);
} else {
 x_250 = x_9;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_245);
lean_ctor_set(x_250, 2, x_246);
lean_ctor_set(x_250, 3, x_214);
lean_ctor_set(x_250, 4, x_249);
return x_250;
}
}
}
else
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_148, 4);
lean_inc(x_251);
if (lean_obj_tag(x_251) == 0)
{
uint8_t x_252; 
x_252 = !lean_is_exclusive(x_148);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_253 = lean_ctor_get(x_148, 1);
x_254 = lean_ctor_get(x_148, 2);
x_255 = lean_ctor_get(x_148, 4);
lean_dec(x_255);
x_256 = lean_ctor_get(x_148, 3);
lean_dec(x_256);
x_257 = lean_ctor_get(x_148, 0);
lean_dec(x_257);
x_258 = !lean_is_exclusive(x_251);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_259 = lean_ctor_get(x_251, 1);
x_260 = lean_ctor_get(x_251, 2);
x_261 = lean_ctor_get(x_251, 4);
lean_dec(x_261);
x_262 = lean_ctor_get(x_251, 3);
lean_dec(x_262);
x_263 = lean_ctor_get(x_251, 0);
lean_dec(x_263);
x_264 = lean_unsigned_to_nat(3u);
x_265 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_251, 4, x_214);
lean_ctor_set(x_251, 3, x_214);
lean_ctor_set(x_251, 2, x_254);
lean_ctor_set(x_251, 1, x_253);
lean_ctor_set(x_251, 0, x_265);
lean_ctor_set(x_148, 4, x_214);
lean_ctor_set(x_148, 2, x_6);
lean_ctor_set(x_148, 1, x_5);
lean_ctor_set(x_148, 0, x_265);
if (lean_is_scalar(x_9)) {
 x_266 = lean_alloc_ctor(0, 5, 0);
} else {
 x_266 = x_9;
}
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_259);
lean_ctor_set(x_266, 2, x_260);
lean_ctor_set(x_266, 3, x_251);
lean_ctor_set(x_266, 4, x_148);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_267 = lean_ctor_get(x_251, 1);
x_268 = lean_ctor_get(x_251, 2);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_251);
x_269 = lean_unsigned_to_nat(3u);
x_270 = lean_unsigned_to_nat(1u);
x_271 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_253);
lean_ctor_set(x_271, 2, x_254);
lean_ctor_set(x_271, 3, x_214);
lean_ctor_set(x_271, 4, x_214);
lean_ctor_set(x_148, 4, x_214);
lean_ctor_set(x_148, 2, x_6);
lean_ctor_set(x_148, 1, x_5);
lean_ctor_set(x_148, 0, x_270);
if (lean_is_scalar(x_9)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_9;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_267);
lean_ctor_set(x_272, 2, x_268);
lean_ctor_set(x_272, 3, x_271);
lean_ctor_set(x_272, 4, x_148);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_273 = lean_ctor_get(x_148, 1);
x_274 = lean_ctor_get(x_148, 2);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_148);
x_275 = lean_ctor_get(x_251, 1);
lean_inc(x_275);
x_276 = lean_ctor_get(x_251, 2);
lean_inc(x_276);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 lean_ctor_release(x_251, 2);
 lean_ctor_release(x_251, 3);
 lean_ctor_release(x_251, 4);
 x_277 = x_251;
} else {
 lean_dec_ref(x_251);
 x_277 = lean_box(0);
}
x_278 = lean_unsigned_to_nat(3u);
x_279 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_277)) {
 x_280 = lean_alloc_ctor(0, 5, 0);
} else {
 x_280 = x_277;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_273);
lean_ctor_set(x_280, 2, x_274);
lean_ctor_set(x_280, 3, x_214);
lean_ctor_set(x_280, 4, x_214);
x_281 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_5);
lean_ctor_set(x_281, 2, x_6);
lean_ctor_set(x_281, 3, x_214);
lean_ctor_set(x_281, 4, x_214);
if (lean_is_scalar(x_9)) {
 x_282 = lean_alloc_ctor(0, 5, 0);
} else {
 x_282 = x_9;
}
lean_ctor_set(x_282, 0, x_278);
lean_ctor_set(x_282, 1, x_275);
lean_ctor_set(x_282, 2, x_276);
lean_ctor_set(x_282, 3, x_280);
lean_ctor_set(x_282, 4, x_281);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_284 = lean_alloc_ctor(0, 5, 0);
} else {
 x_284 = x_9;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_5);
lean_ctor_set(x_284, 2, x_6);
lean_ctor_set(x_284, 3, x_148);
lean_ctor_set(x_284, 4, x_251);
return x_284;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_9)) {
 x_286 = lean_alloc_ctor(0, 5, 0);
} else {
 x_286 = x_9;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_5);
lean_ctor_set(x_286, 2, x_6);
lean_ctor_set(x_286, 3, x_148);
lean_ctor_set(x_286, 4, x_148);
return x_286;
}
}
}
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_unsigned_to_nat(1u);
x_288 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_1);
lean_ctor_set(x_288, 2, x_2);
lean_ctor_set(x_288, 3, x_3);
lean_ctor_set(x_288, 4, x_3);
return x_288;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(x_1, x_5);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_3, x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(x_9, x_10, x_7);
x_1 = x_11;
x_2 = x_6;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(1);
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(x_2, x_1);
x_4 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
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
x_1 = lean_unsigned_to_nat(14u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ELAN", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Env_baseVars___closed__5() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_91; lean_object* x_92; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*17);
x_7 = lean_ctor_get(x_1, 9);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 10);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 11);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 16);
lean_inc_ref(x_10);
lean_dec_ref(x_1);
x_91 = l_Lake_Env_baseVars___closed__4;
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_103; 
x_103 = lean_box(0);
x_92 = x_103;
goto block_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_4, 0);
x_105 = lean_ctor_get(x_104, 1);
lean_inc_ref(x_105);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_92 = x_106;
goto block_102;
}
block_57:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 7);
x_21 = lean_ctor_get(x_3, 11);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lake_Env_compute___closed__2;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
x_26 = l_Lake_Env_compute___closed__3;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
x_28 = l_Lake_Env_compute___closed__4;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
x_30 = l_Lake_Env_noToolchainVars___closed__7;
lean_inc_ref(x_20);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_20);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lake_Env_noToolchainVars___closed__10;
lean_inc_ref(x_19);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_19);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lake_Env_noToolchainVars___closed__12;
lean_inc_ref(x_21);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_21);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lake_Env_baseVars___closed__0;
x_40 = l_Lake_LeanInstall_leanCc_x3f(x_3);
lean_dec_ref(x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lake_Env_baseVars___closed__1;
x_43 = lean_array_push(x_42, x_16);
x_44 = lean_array_push(x_43, x_15);
x_45 = lean_array_push(x_44, x_13);
x_46 = lean_array_push(x_45, x_14);
x_47 = lean_array_push(x_46, x_11);
x_48 = lean_array_push(x_47, x_17);
x_49 = lean_array_push(x_48, x_23);
x_50 = lean_array_push(x_49, x_25);
x_51 = lean_array_push(x_50, x_27);
x_52 = lean_array_push(x_51, x_29);
x_53 = lean_array_push(x_52, x_32);
x_54 = lean_array_push(x_53, x_35);
x_55 = lean_array_push(x_54, x_38);
x_56 = lean_array_push(x_55, x_41);
return x_56;
}
block_79:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_62 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_63);
lean_dec_ref(x_2);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_61);
x_65 = l_Lake_Env_noToolchainVars___closed__1;
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lake_Env_noToolchainVars___closed__5;
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_62);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0;
x_72 = l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(x_5);
x_73 = l_Lean_Json_compress(x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lake_Env_compute___closed__0;
if (x_6 == 0)
{
lean_object* x_77; 
x_77 = l_Lake_Env_baseVars___closed__2;
x_11 = x_70;
x_12 = x_76;
x_13 = x_64;
x_14 = x_67;
x_15 = x_60;
x_16 = x_59;
x_17 = x_75;
x_18 = x_77;
goto block_57;
}
else
{
lean_object* x_78; 
x_78 = l_Lake_Env_baseVars___closed__3;
x_11 = x_70;
x_12 = x_76;
x_13 = x_64;
x_14 = x_67;
x_15 = x_60;
x_16 = x_59;
x_17 = x_75;
x_18 = x_78;
goto block_57;
}
}
block_90:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lake_Env_computeToolchain___closed__0;
x_85 = lean_string_utf8_byte_size(x_10);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_nat_dec_eq(x_85, x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_10);
x_58 = x_84;
x_59 = x_81;
x_60 = x_83;
x_61 = x_88;
goto block_79;
}
else
{
lean_object* x_89; 
lean_dec_ref(x_10);
x_89 = lean_box(0);
x_58 = x_84;
x_59 = x_81;
x_60 = x_83;
x_61 = x_89;
goto block_79;
}
}
block_102:
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lake_Env_baseVars___closed__5;
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_95; 
x_95 = lean_box(0);
x_80 = x_94;
x_81 = x_93;
x_82 = x_95;
goto block_90;
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_4);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_4, 0);
x_98 = lean_ctor_get(x_97, 0);
lean_inc_ref(x_98);
lean_dec(x_97);
lean_ctor_set(x_4, 0, x_98);
x_80 = x_94;
x_81 = x_93;
x_82 = x_4;
goto block_90;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_4, 0);
lean_inc(x_99);
lean_dec(x_4);
x_100 = lean_ctor_get(x_99, 0);
lean_inc_ref(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_80 = x_94;
x_81 = x_93;
x_82 = x_101;
goto block_90;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Env_vars___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Env_vars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Env_baseVars___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Env_vars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Env_baseVars___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_44; lean_object* x_45; 
x_2 = lean_ctor_get(x_1, 6);
x_3 = lean_ctor_get(x_1, 7);
lean_inc(x_3);
lean_inc_ref(x_1);
x_4 = l_Lake_Env_baseVars(x_1);
x_44 = l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0;
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_3);
if (x_54 == 0)
{
x_45 = x_3;
goto block_53;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_3, 0);
lean_inc(x_55);
lean_dec(x_3);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_45 = x_56;
goto block_53;
}
}
else
{
lean_object* x_57; 
lean_dec(x_3);
x_57 = l_Lake_Env_noToolchainVars___closed__17;
x_45 = x_57;
goto block_53;
}
block_43:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lake_Env_compute___closed__6;
x_10 = l_Lake_Env_leanPath(x_1);
x_11 = l_System_SearchPath_toString(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lake_Env_compute___closed__7;
x_15 = l_Lake_Env_leanSrcPath(x_1);
x_16 = l_System_SearchPath_toString(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lake_Env_compute___closed__5;
x_20 = l_Lake_Env_leanGithash(x_1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lake_Env_compute___closed__8;
x_24 = l_Lake_Env_path(x_1);
x_25 = l_System_SearchPath_toString(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lake_Env_vars___closed__0;
x_29 = lean_array_push(x_28, x_6);
x_30 = lean_array_push(x_29, x_8);
x_31 = lean_array_push(x_30, x_13);
x_32 = lean_array_push(x_31, x_18);
x_33 = lean_array_push(x_32, x_22);
x_34 = lean_array_push(x_33, x_27);
x_35 = l_Array_append___redArg(x_4, x_34);
lean_dec_ref(x_34);
x_36 = l_System_Platform_isWindows;
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = l_Lake_sharedLibPathEnvVar;
x_38 = l_Lake_Env_sharedLibPath(x_1);
x_39 = l_System_SearchPath_toString(x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_push(x_35, x_41);
return x_42;
}
else
{
lean_dec_ref(x_1);
return x_35;
}
}
block_53:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lake_Env_compute___closed__1;
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = l_Lake_Env_vars___closed__1;
x_5 = x_47;
x_6 = x_46;
x_7 = x_50;
goto block_43;
}
else
{
lean_object* x_51; 
x_51 = l_Lake_Env_vars___closed__2;
x_5 = x_47;
x_6 = x_46;
x_7 = x_51;
goto block_43;
}
}
else
{
lean_object* x_52; 
x_52 = l_Lake_Env_noToolchainVars___closed__17;
x_5 = x_47;
x_6 = x_46;
x_7 = x_52;
goto block_43;
}
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
lean_inc_ref(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc_ref(x_4);
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
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Env(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedEnv_default___closed__0 = _init_l_Lake_instInhabitedEnv_default___closed__0();
lean_mark_persistent(l_Lake_instInhabitedEnv_default___closed__0);
l_Lake_instInhabitedEnv_default___closed__1 = _init_l_Lake_instInhabitedEnv_default___closed__1();
lean_mark_persistent(l_Lake_instInhabitedEnv_default___closed__1);
l_Lake_instInhabitedEnv_default = _init_l_Lake_instInhabitedEnv_default();
lean_mark_persistent(l_Lake_instInhabitedEnv_default);
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
l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0 = _init_l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0();
lean_mark_persistent(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0);
l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1 = _init_l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1();
lean_mark_persistent(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1);
l_Lake_Env_computeToolchain___closed__0 = _init_l_Lake_Env_computeToolchain___closed__0();
lean_mark_persistent(l_Lake_Env_computeToolchain___closed__0);
l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0 = _init_l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0();
lean_mark_persistent(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0);
l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0 = _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0);
l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1);
l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2);
l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0 = _init_l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0();
lean_mark_persistent(l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0);
l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0 = _init_l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0();
lean_mark_persistent(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0);
l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1 = _init_l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1();
lean_mark_persistent(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1);
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
l_Lake_Env_compute___closed__10 = _init_l_Lake_Env_compute___closed__10();
lean_mark_persistent(l_Lake_Env_compute___closed__10);
l_Lake_Env_compute___closed__11 = _init_l_Lake_Env_compute___closed__11();
lean_mark_persistent(l_Lake_Env_compute___closed__11);
l_Lake_Env_compute___closed__12 = _init_l_Lake_Env_compute___closed__12();
lean_mark_persistent(l_Lake_Env_compute___closed__12);
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
l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0 = _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0);
l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1);
l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2);
l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3 = _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3);
l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4 = _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4);
l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5 = _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5);
l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6 = _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6);
l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7 = _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7);
l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8 = _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8);
l_Lake_Env_baseVars___closed__0 = _init_l_Lake_Env_baseVars___closed__0();
lean_mark_persistent(l_Lake_Env_baseVars___closed__0);
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
l_Lake_Env_vars___closed__0 = _init_l_Lake_Env_vars___closed__0();
lean_mark_persistent(l_Lake_Env_vars___closed__0);
l_Lake_Env_vars___closed__1 = _init_l_Lake_Env_vars___closed__1();
lean_mark_persistent(l_Lake_Env_vars___closed__1);
l_Lake_Env_vars___closed__2 = _init_l_Lake_Env_vars___closed__2();
lean_mark_persistent(l_Lake_Env_vars___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
