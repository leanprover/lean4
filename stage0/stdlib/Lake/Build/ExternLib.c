// Lean compiler output
// Module: Lake.Build.ExternLib
// Imports: public import Lake.Config.FacetConfig public import Lake.Build.Job.Monad import Lake.Build.Job.Register import Lake.Build.Common import Lake.Build.Infos
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
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1;
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_defaultFacetConfig;
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2;
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
extern uint8_t l_System_Platform_isOSX;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0(uint8_t, lean_object*);
extern lean_object* l_Lake_ExternLib_sharedFacet;
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0;
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(uint8_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_ExternLib_initFacetConfigs___closed__1;
extern lean_object* l_Lake_ExternLib_dynlibFacet;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0;
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___boxed(lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_ExternLib_dynlibFacetConfig___closed__0;
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1;
lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(lean_object*, size_t, size_t, uint64_t);
static lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticFacetConfig;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
extern lean_object* l_Lake_platformTrace;
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3;
lean_object* lean_st_ref_take(lean_object*);
static lean_object* l_Lake_ExternLib_staticFacetConfig___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__8;
static lean_object* l_Lake_ExternLib_defaultFacetConfig___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_sharedFacetConfig;
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0;
static lean_object* l_Lake_ExternLib_initFacetConfigs___closed__3;
extern lean_object* l_Lake_instDataKindFilePath;
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lake_ExternLib_staticFacetConfig___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1;
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ExternLib_initFacetConfigs___closed__2;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0;
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibFacetConfig;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ExternLib_dynlibFacetConfig___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4;
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__6;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
extern lean_object* l_Lake_instDataKindDynlib;
static lean_object* l_Lake_ExternLib_sharedFacetConfig___closed__0;
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
static lean_object* l_Lake_ExternLib_staticFacetConfig___closed__2;
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_staticFacet;
static lean_object* l_Lake_ExternLib_defaultFacetConfig___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
static lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0;
extern lean_object* l_Lake_ExternLib_defaultFacet;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0;
static lean_object* l_Lake_ExternLib_dynlibFacetConfig___closed__2;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_ExternLib_initFacetConfigs___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_initFacetConfigs;
extern uint8_t l_System_Platform_isWindows;
extern lean_object* l_Lake_ExternLib_keyword;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4;
static lean_object* l_Lake_ExternLib_sharedFacetConfig___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_7(x_3, x_1, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_apply_1(x_2, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_apply_1(x_2, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("static", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":static", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = l_Lake_instDataKindFilePath;
x_13 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0;
x_14 = l_Lean_Name_str___override(x_10, x_13);
x_15 = 1;
lean_inc(x_14);
x_16 = l_Lean_Name_toString(x_14, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0___boxed), 9, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_11);
lean_inc_ref(x_6);
x_19 = l_Lake_ensureJob___redArg(x_12, x_18, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_21, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_6, 3);
lean_inc(x_24);
lean_dec_ref(x_6);
x_25 = lean_st_ref_take(x_24);
x_26 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1;
x_27 = lean_string_append(x_16, x_26);
x_28 = 0;
lean_ctor_set(x_21, 2, x_27);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_28);
lean_inc_ref(x_21);
x_29 = l_Lake_Job_toOpaque___redArg(x_21);
x_30 = lean_array_push(x_25, x_29);
x_31 = lean_st_ref_set(x_24, x_30);
lean_dec(x_24);
x_32 = l_Lake_Job_renew___redArg(x_21);
lean_ctor_set(x_19, 0, x_32);
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_35 = lean_ctor_get(x_6, 3);
lean_inc(x_35);
lean_dec_ref(x_6);
x_36 = lean_st_ref_take(x_35);
x_37 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1;
x_38 = lean_string_append(x_16, x_37);
x_39 = 0;
x_40 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 2, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_39);
lean_inc_ref(x_40);
x_41 = l_Lake_Job_toOpaque___redArg(x_40);
x_42 = lean_array_push(x_36, x_41);
x_43 = lean_st_ref_set(x_35, x_42);
lean_dec(x_35);
x_44 = l_Lake_Job_renew___redArg(x_40);
lean_ctor_set(x_19, 0, x_44);
return x_19;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_45 = lean_ctor_get(x_19, 0);
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_19);
x_47 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 x_49 = x_45;
} else {
 lean_dec_ref(x_45);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_6, 3);
lean_inc(x_50);
lean_dec_ref(x_6);
x_51 = lean_st_ref_take(x_50);
x_52 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1;
x_53 = lean_string_append(x_16, x_52);
x_54 = 0;
if (lean_is_scalar(x_49)) {
 x_55 = lean_alloc_ctor(0, 3, 1);
} else {
 x_55 = x_49;
}
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_54);
lean_inc_ref(x_55);
x_56 = l_Lake_Job_toOpaque___redArg(x_55);
x_57 = lean_array_push(x_51, x_56);
x_58 = lean_st_ref_set(x_50, x_57);
lean_dec(x_50);
x_59 = l_Lake_Job_renew___redArg(x_55);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_46);
return x_60;
}
}
else
{
lean_dec_ref(x_16);
lean_dec_ref(x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_mkRelPathString(x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_Json_compress(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_ExternLib_staticFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ExternLib_staticFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ExternLib_staticFacetConfig___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_ExternLib_staticFacetConfig___closed__0;
x_2 = 1;
x_3 = l_Lake_instDataKindFilePath;
x_4 = l_Lake_ExternLib_staticFacetConfig___closed__1;
x_5 = l_Lake_ExternLib_keyword;
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_2);
return x_6;
}
}
static lean_object* _init_l_Lake_ExternLib_staticFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_ExternLib_staticFacetConfig___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-L", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0;
x_2 = l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-Wl,--whole-archive", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-Wl,--no-whole-archive", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3;
x_2 = l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-Wl,-force_load,", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_46; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_16 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_10, 2);
lean_inc(x_17);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 x_18 = x_10;
} else {
 lean_dec_ref(x_10);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_19);
lean_dec_ref(x_13);
x_46 = l_System_Platform_isOSX;
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4;
x_48 = l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__6;
x_49 = lean_array_push(x_48, x_4);
x_50 = lean_array_push(x_49, x_47);
x_20 = x_50;
goto block_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__7;
x_52 = lean_string_append(x_51, x_4);
lean_dec_ref(x_4);
x_53 = l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__8;
x_54 = lean_array_push(x_53, x_52);
x_20 = x_54;
goto block_45;
}
block_45:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_19, 3);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_19, 12);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_19, 18);
lean_inc_ref(x_23);
lean_dec_ref(x_19);
x_24 = l_Array_append___redArg(x_20, x_1);
x_25 = l_Array_append___redArg(x_24, x_2);
x_26 = l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2;
x_27 = lean_array_push(x_26, x_21);
x_28 = l_Array_append___redArg(x_25, x_27);
lean_dec_ref(x_27);
x_29 = l_Array_append___redArg(x_28, x_23);
lean_dec_ref(x_23);
x_30 = l_Lake_compileSharedLib(x_3, x_29, x_22, x_14);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 1);
if (lean_is_scalar(x_18)) {
 x_33 = lean_alloc_ctor(0, 3, 1);
} else {
 x_33 = x_18;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_16);
lean_ctor_set(x_33, 2, x_17);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_15);
lean_ctor_set(x_30, 1, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
if (lean_is_scalar(x_18)) {
 x_36 = lean_alloc_ctor(0, 3, 1);
} else {
 x_36 = x_18;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_16);
lean_ctor_set(x_36, 2, x_17);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_15);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_30, 1);
if (lean_is_scalar(x_18)) {
 x_40 = lean_alloc_ctor(0, 3, 1);
} else {
 x_40 = x_18;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_16);
lean_ctor_set(x_40, 2, x_17);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_15);
lean_ctor_set(x_30, 1, x_40);
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_30);
if (lean_is_scalar(x_18)) {
 x_43 = lean_alloc_ctor(0, 3, 1);
} else {
 x_43 = x_18;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_16);
lean_ctor_set(x_43, 2, x_17);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_15);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_buildLeanSharedLibOfStatic___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_Hash_nil;
x_8 = lean_string_hash(x_6);
lean_dec(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_mix_hash(x_4, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(x_1, x_5, x_6, x_7);
lean_dec_ref(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
static lean_object* _init_l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0;
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_string_append(x_6, x_3);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1;
x_6 = lean_string_append(x_5, x_4);
x_7 = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1;
x_11 = lean_string_append(x_10, x_9);
x_12 = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(x_11, x_3);
x_13 = 93;
x_14 = lean_string_push(x_12, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pure: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_13 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 x_15 = x_9;
} else {
 lean_dec_ref(x_9);
 x_15 = lean_box(0);
}
x_16 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_16);
x_17 = l_Lake_BuildTrace_mix(x_13, x_16);
x_46 = l_Lake_Hash_nil;
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_array_get_size(x_1);
x_49 = lean_nat_dec_lt(x_47, x_48);
if (x_49 == 0)
{
x_18 = x_46;
goto block_45;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_48, x_48);
if (x_50 == 0)
{
if (x_49 == 0)
{
x_18 = x_46;
goto block_45;
}
else
{
size_t x_51; size_t x_52; uint64_t x_53; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_48);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(x_1, x_51, x_52, x_46);
x_18 = x_53;
goto block_45;
}
}
else
{
size_t x_54; size_t x_55; uint64_t x_56; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_48);
x_56 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(x_1, x_54, x_55, x_46);
x_18 = x_56;
goto block_45;
}
}
block_45:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_19 = l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0;
x_20 = l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1;
lean_inc_ref(x_1);
x_21 = lean_array_to_list(x_1);
x_22 = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_20, x_22);
lean_dec_ref(x_22);
x_24 = lean_string_append(x_19, x_23);
lean_dec_ref(x_23);
x_25 = l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2;
x_26 = l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4;
x_27 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set_uint64(x_27, sizeof(void*)*3, x_18);
x_28 = l_Lake_BuildTrace_mix(x_17, x_27);
x_29 = l_Lake_platformTrace;
x_30 = l_Lake_BuildTrace_mix(x_28, x_29);
if (lean_is_scalar(x_15)) {
 x_31 = lean_alloc_ctor(0, 3, 1);
} else {
 x_31 = x_15;
}
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_14);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_12);
x_32 = l_Lake_sharedLibExt;
lean_inc_ref(x_3);
x_33 = l_System_FilePath_withExtension(x_3, x_32);
lean_inc_ref(x_33);
x_34 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed), 11, 4);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_1);
lean_closure_set(x_34, 2, x_33);
lean_closure_set(x_34, 3, x_3);
x_35 = 0;
lean_inc_ref(x_33);
x_36 = l_Lake_buildFileUnlessUpToDate_x27(x_33, x_34, x_35, x_4, x_5, x_6, x_7, x_8, x_31);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_33);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec_ref(x_33);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_buildLeanSharedLibOfStatic___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed), 10, 2);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_2);
x_12 = l_Lake_instDataKindFilePath;
x_13 = lean_unsigned_to_nat(0u);
x_14 = 0;
x_15 = l_Lake_Job_mapM___redArg(x_12, x_1, x_11, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_buildLeanSharedLibOfStatic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1;
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc_ref(x_3);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = lean_apply_7(x_3, x_1, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_2);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_11, 8);
lean_inc_ref(x_14);
lean_dec_ref(x_11);
x_15 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0;
x_16 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2;
x_17 = l_Lake_buildLeanSharedLibOfStatic(x_13, x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_16);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_ctor_get(x_11, 8);
lean_inc_ref(x_20);
lean_dec_ref(x_11);
x_21 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0;
x_22 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2;
x_23 = l_Lake_buildLeanSharedLibOfStatic(x_18, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":shared", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
x_12 = lean_ctor_get(x_9, 6);
lean_inc_ref(x_12);
x_13 = l_Lake_instDataKindFilePath;
x_14 = l_Lake_ExternLib_staticFacet;
lean_inc(x_10);
lean_inc(x_11);
x_15 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_10);
x_16 = l_Lake_ExternLib_keyword;
x_17 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_1);
lean_ctor_set(x_17, 3, x_14);
x_18 = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed), 9, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_12);
lean_inc_ref(x_6);
x_19 = l_Lake_ensureJob___redArg(x_13, x_18, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_21, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_6, 3);
lean_inc(x_24);
lean_dec_ref(x_6);
x_25 = lean_st_ref_take(x_24);
x_26 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0;
x_27 = l_Lean_Name_str___override(x_10, x_26);
x_28 = 1;
x_29 = l_Lean_Name_toString(x_27, x_28);
x_30 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0;
x_31 = lean_string_append(x_29, x_30);
x_32 = 0;
lean_ctor_set(x_21, 2, x_31);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_32);
lean_inc_ref(x_21);
x_33 = l_Lake_Job_toOpaque___redArg(x_21);
x_34 = lean_array_push(x_25, x_33);
x_35 = lean_st_ref_set(x_24, x_34);
lean_dec(x_24);
x_36 = l_Lake_Job_renew___redArg(x_21);
lean_ctor_set(x_19, 0, x_36);
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_ctor_get(x_6, 3);
lean_inc(x_39);
lean_dec_ref(x_6);
x_40 = lean_st_ref_take(x_39);
x_41 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0;
x_42 = l_Lean_Name_str___override(x_10, x_41);
x_43 = 1;
x_44 = l_Lean_Name_toString(x_42, x_43);
x_45 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0;
x_46 = lean_string_append(x_44, x_45);
x_47 = 0;
x_48 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_38);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_47);
lean_inc_ref(x_48);
x_49 = l_Lake_Job_toOpaque___redArg(x_48);
x_50 = lean_array_push(x_40, x_49);
x_51 = lean_st_ref_set(x_39, x_50);
lean_dec(x_39);
x_52 = l_Lake_Job_renew___redArg(x_48);
lean_ctor_set(x_19, 0, x_52);
return x_19;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_53 = lean_ctor_get(x_19, 0);
x_54 = lean_ctor_get(x_19, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_19);
x_55 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 x_57 = x_53;
} else {
 lean_dec_ref(x_53);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_6, 3);
lean_inc(x_58);
lean_dec_ref(x_6);
x_59 = lean_st_ref_take(x_58);
x_60 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0;
x_61 = l_Lean_Name_str___override(x_10, x_60);
x_62 = 1;
x_63 = l_Lean_Name_toString(x_61, x_62);
x_64 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0;
x_65 = lean_string_append(x_63, x_64);
x_66 = 0;
if (lean_is_scalar(x_57)) {
 x_67 = lean_alloc_ctor(0, 3, 1);
} else {
 x_67 = x_57;
}
lean_ctor_set(x_67, 0, x_55);
lean_ctor_set(x_67, 1, x_56);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*3, x_66);
lean_inc_ref(x_67);
x_68 = l_Lake_Job_toOpaque___redArg(x_67);
x_69 = lean_array_push(x_59, x_68);
x_70 = lean_st_ref_set(x_58, x_69);
lean_dec(x_58);
x_71 = l_Lake_Job_renew___redArg(x_67);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_54);
return x_72;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_ExternLib_staticFacetConfig___closed__0;
x_2 = 1;
x_3 = l_Lake_instDataKindFilePath;
x_4 = l_Lake_ExternLib_sharedFacetConfig___closed__0;
x_5 = l_Lake_ExternLib_keyword;
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_2);
return x_6;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_ExternLib_sharedFacetConfig___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shared library `", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` does not start with `lib`; this is not supported on Unix", 58, 58);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lib", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has no file name", 18, 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_1);
x_9 = l_System_FilePath_fileStem(x_1);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_System_Platform_isWindows;
if (x_11 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3;
x_49 = lean_string_utf8_byte_size(x_10);
x_50 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4;
x_51 = lean_nat_dec_le(x_50, x_49);
if (x_51 == 0)
{
x_12 = x_11;
goto block_47;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_string_memcmp(x_10, x_48, x_52, x_52, x_50);
x_12 = x_53;
goto block_47;
}
}
else
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = 0;
x_55 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2;
x_56 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_10);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_7);
return x_57;
}
block_47:
{
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0;
x_16 = lean_string_append(x_15, x_1);
lean_dec_ref(x_1);
x_17 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = 3;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_array_get_size(x_14);
x_22 = lean_array_push(x_14, x_20);
lean_ctor_set(x_7, 0, x_22);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_26 = lean_ctor_get(x_7, 1);
x_27 = lean_ctor_get(x_7, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_24);
lean_dec(x_7);
x_28 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0;
x_29 = lean_string_append(x_28, x_1);
lean_dec_ref(x_1);
x_30 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_array_get_size(x_24);
x_35 = lean_array_push(x_24, x_33);
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
lean_ctor_set(x_36, 2, x_27);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_25);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_unsigned_to_nat(3u);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_string_utf8_byte_size(x_10);
lean_inc(x_10);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
x_42 = l_String_Slice_Pos_nextn(x_41, x_39, x_38);
lean_dec_ref(x_41);
x_43 = lean_string_utf8_extract(x_10, x_42, x_40);
lean_dec(x_42);
lean_dec(x_10);
x_44 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2;
x_45 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_11);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_7);
return x_46;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_9);
x_58 = !lean_is_exclusive(x_7);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_7, 0);
x_60 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0;
x_61 = lean_string_append(x_60, x_1);
lean_dec_ref(x_1);
x_62 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5;
x_63 = lean_string_append(x_61, x_62);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_get_size(x_59);
x_67 = lean_array_push(x_59, x_65);
lean_ctor_set(x_7, 0, x_67);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_7);
return x_68;
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_69 = lean_ctor_get(x_7, 0);
x_70 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_71 = lean_ctor_get(x_7, 1);
x_72 = lean_ctor_get(x_7, 2);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_69);
lean_dec(x_7);
x_73 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0;
x_74 = lean_string_append(x_73, x_1);
lean_dec_ref(x_1);
x_75 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5;
x_76 = lean_string_append(x_74, x_75);
x_77 = 3;
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = lean_array_get_size(x_69);
x_80 = lean_array_push(x_69, x_78);
x_81 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_71);
lean_ctor_set(x_81, 2, x_72);
lean_ctor_set_uint8(x_81, sizeof(void*)*3, x_70);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0;
x_10 = l_Lake_instDataKindDynlib;
x_11 = lean_unsigned_to_nat(0u);
x_12 = 0;
x_13 = l_Lake_Job_mapM___redArg(x_10, x_1, x_9, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_2);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_7(x_2, x_1, x_3, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2;
x_13 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(x_11, x_2, x_3, x_4, x_5, x_6, x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2;
x_17 = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(x_14, x_2, x_3, x_4, x_5, x_6, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":dynlib", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
x_12 = l_Lake_instDataKindDynlib;
x_13 = l_Lake_ExternLib_sharedFacet;
lean_inc(x_10);
lean_inc(x_11);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_10);
x_15 = l_Lake_ExternLib_keyword;
x_16 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_1);
lean_ctor_set(x_16, 3, x_13);
x_17 = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed), 8, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc_ref(x_6);
x_18 = l_Lake_ensureJob___redArg(x_12, x_17, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_20, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_6, 3);
lean_inc(x_23);
lean_dec_ref(x_6);
x_24 = lean_st_ref_take(x_23);
x_25 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0;
x_26 = l_Lean_Name_str___override(x_10, x_25);
x_27 = 1;
x_28 = l_Lean_Name_toString(x_26, x_27);
x_29 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0;
x_30 = lean_string_append(x_28, x_29);
x_31 = 0;
lean_ctor_set(x_20, 2, x_30);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_31);
lean_inc_ref(x_20);
x_32 = l_Lake_Job_toOpaque___redArg(x_20);
x_33 = lean_array_push(x_24, x_32);
x_34 = lean_st_ref_set(x_23, x_33);
lean_dec(x_23);
x_35 = l_Lake_Job_renew___redArg(x_20);
lean_ctor_set(x_18, 0, x_35);
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_ctor_get(x_6, 3);
lean_inc(x_38);
lean_dec_ref(x_6);
x_39 = lean_st_ref_take(x_38);
x_40 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0;
x_41 = l_Lean_Name_str___override(x_10, x_40);
x_42 = 1;
x_43 = l_Lean_Name_toString(x_41, x_42);
x_44 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0;
x_45 = lean_string_append(x_43, x_44);
x_46 = 0;
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_37);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_46);
lean_inc_ref(x_47);
x_48 = l_Lake_Job_toOpaque___redArg(x_47);
x_49 = lean_array_push(x_39, x_48);
x_50 = lean_st_ref_set(x_38, x_49);
lean_dec(x_38);
x_51 = l_Lake_Job_renew___redArg(x_47);
lean_ctor_set(x_18, 0, x_51);
return x_18;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_52 = lean_ctor_get(x_18, 0);
x_53 = lean_ctor_get(x_18, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_18);
x_54 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_6, 3);
lean_inc(x_57);
lean_dec_ref(x_6);
x_58 = lean_st_ref_take(x_57);
x_59 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0;
x_60 = l_Lean_Name_str___override(x_10, x_59);
x_61 = 1;
x_62 = l_Lean_Name_toString(x_60, x_61);
x_63 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0;
x_64 = lean_string_append(x_62, x_63);
x_65 = 0;
if (lean_is_scalar(x_56)) {
 x_66 = lean_alloc_ctor(0, 3, 1);
} else {
 x_66 = x_56;
}
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_55);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_65);
lean_inc_ref(x_66);
x_67 = l_Lake_Job_toOpaque___redArg(x_66);
x_68 = lean_array_push(x_58, x_67);
x_69 = lean_st_ref_set(x_57, x_68);
lean_dec(x_57);
x_70 = l_Lake_Job_renew___redArg(x_66);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_53);
return x_71;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_Json_compress(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_ExternLib_dynlibFacetConfig___closed__0;
x_2 = 1;
x_3 = l_Lake_instDataKindDynlib;
x_4 = l_Lake_ExternLib_dynlibFacetConfig___closed__1;
x_5 = l_Lake_ExternLib_keyword;
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_2);
return x_6;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_ExternLib_dynlibFacetConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_9, 2);
x_12 = l_Lake_ExternLib_staticFacet;
lean_inc(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_10);
x_14 = l_Lake_ExternLib_keyword;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_12);
x_16 = lean_apply_7(x_2, x_15, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = l_Lake_ExternLib_staticFacetConfig___closed__0;
x_3 = 1;
x_4 = l_Lake_instDataKindFilePath;
x_5 = l_Lake_ExternLib_defaultFacetConfig___closed__0;
x_6 = l_Lake_ExternLib_keyword;
x_7 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_2);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*4 + 1, x_1);
return x_7;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_ExternLib_defaultFacetConfig___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Lean_Name_quickCmp(x_1, x_5);
switch (x_10) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(x_1, x_2, x_7);
x_12 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 4);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_mul(x_19, x_13);
x_21 = lean_nat_dec_lt(x_20, x_14);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_22 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_23 = lean_nat_add(x_22, x_13);
lean_dec(x_22);
if (lean_is_scalar(x_9)) {
 x_24 = lean_alloc_ctor(0, 5, 0);
} else {
 x_24 = x_9;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_6);
lean_ctor_set(x_24, 3, x_11);
lean_ctor_set(x_24, 4, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_25 = x_11;
} else {
 lean_dec_ref(x_11);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
x_29 = lean_ctor_get(x_18, 2);
x_30 = lean_ctor_get(x_18, 3);
x_31 = lean_ctor_get(x_18, 4);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_mul(x_32, x_26);
x_34 = lean_nat_dec_lt(x_27, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_45; lean_object* x_46; 
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 x_35 = x_18;
} else {
 lean_dec_ref(x_18);
 x_35 = lean_box(0);
}
x_36 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_37 = lean_nat_add(x_36, x_13);
lean_dec(x_36);
x_45 = lean_nat_add(x_12, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_30, 0);
lean_inc(x_53);
x_46 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = lean_unsigned_to_nat(0u);
x_46 = x_54;
goto block_52;
}
block_44:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_nat_add(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
if (lean_is_scalar(x_35)) {
 x_42 = lean_alloc_ctor(0, 5, 0);
} else {
 x_42 = x_35;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_5);
lean_ctor_set(x_42, 2, x_6);
lean_ctor_set(x_42, 3, x_31);
lean_ctor_set(x_42, 4, x_8);
if (lean_is_scalar(x_25)) {
 x_43 = lean_alloc_ctor(0, 5, 0);
} else {
 x_43 = x_25;
}
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_28);
lean_ctor_set(x_43, 2, x_29);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 4, x_42);
return x_43;
}
block_52:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_nat_add(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (lean_is_scalar(x_9)) {
 x_48 = lean_alloc_ctor(0, 5, 0);
} else {
 x_48 = x_9;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_15);
lean_ctor_set(x_48, 2, x_16);
lean_ctor_set(x_48, 3, x_17);
lean_ctor_set(x_48, 4, x_30);
x_49 = lean_nat_add(x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
x_38 = x_48;
x_39 = x_49;
x_40 = x_50;
goto block_44;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_38 = x_48;
x_39 = x_49;
x_40 = x_51;
goto block_44;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_9);
x_55 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_56 = lean_nat_add(x_55, x_13);
lean_dec(x_55);
x_57 = lean_nat_add(x_12, x_13);
x_58 = lean_nat_add(x_57, x_27);
lean_dec(x_57);
lean_inc_ref(x_8);
if (lean_is_scalar(x_25)) {
 x_59 = lean_alloc_ctor(0, 5, 0);
} else {
 x_59 = x_25;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_6);
lean_ctor_set(x_59, 3, x_18);
lean_ctor_set(x_59, 4, x_8);
x_60 = !lean_is_exclusive(x_8);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_8, 4);
lean_dec(x_61);
x_62 = lean_ctor_get(x_8, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_8, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_8, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_8, 0);
lean_dec(x_65);
lean_ctor_set(x_8, 4, x_59);
lean_ctor_set(x_8, 3, x_17);
lean_ctor_set(x_8, 2, x_16);
lean_ctor_set(x_8, 1, x_15);
lean_ctor_set(x_8, 0, x_56);
return x_8;
}
else
{
lean_object* x_66; 
lean_dec(x_8);
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_15);
lean_ctor_set(x_66, 2, x_16);
lean_ctor_set(x_66, 3, x_17);
lean_ctor_set(x_66, 4, x_59);
return x_66;
}
}
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_11, 3);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_11);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_11, 4);
x_70 = lean_ctor_get(x_11, 1);
x_71 = lean_ctor_get(x_11, 2);
x_72 = lean_ctor_get(x_11, 3);
lean_dec(x_72);
x_73 = lean_ctor_get(x_11, 0);
lean_dec(x_73);
x_74 = lean_unsigned_to_nat(3u);
lean_inc(x_69);
lean_ctor_set(x_11, 3, x_69);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_75 = lean_alloc_ctor(0, 5, 0);
} else {
 x_75 = x_9;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set(x_75, 3, x_67);
lean_ctor_set(x_75, 4, x_11);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_11, 4);
x_77 = lean_ctor_get(x_11, 1);
x_78 = lean_ctor_get(x_11, 2);
lean_inc(x_76);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_11);
x_79 = lean_unsigned_to_nat(3u);
lean_inc(x_76);
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_12);
lean_ctor_set(x_80, 1, x_5);
lean_ctor_set(x_80, 2, x_6);
lean_ctor_set(x_80, 3, x_76);
lean_ctor_set(x_80, 4, x_76);
if (lean_is_scalar(x_9)) {
 x_81 = lean_alloc_ctor(0, 5, 0);
} else {
 x_81 = x_9;
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_78);
lean_ctor_set(x_81, 3, x_67);
lean_ctor_set(x_81, 4, x_80);
return x_81;
}
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_11, 4);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_11);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_11, 1);
x_85 = lean_ctor_get(x_11, 2);
x_86 = lean_ctor_get(x_11, 4);
lean_dec(x_86);
x_87 = lean_ctor_get(x_11, 3);
lean_dec(x_87);
x_88 = lean_ctor_get(x_11, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_82);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_82, 1);
x_91 = lean_ctor_get(x_82, 2);
x_92 = lean_ctor_get(x_82, 4);
lean_dec(x_92);
x_93 = lean_ctor_get(x_82, 3);
lean_dec(x_93);
x_94 = lean_ctor_get(x_82, 0);
lean_dec(x_94);
x_95 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_82, 4, x_67);
lean_ctor_set(x_82, 3, x_67);
lean_ctor_set(x_82, 2, x_85);
lean_ctor_set(x_82, 1, x_84);
lean_ctor_set(x_82, 0, x_12);
lean_ctor_set(x_11, 4, x_67);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_96 = lean_alloc_ctor(0, 5, 0);
} else {
 x_96 = x_9;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_82);
lean_ctor_set(x_96, 4, x_11);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_82, 1);
x_98 = lean_ctor_get(x_82, 2);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_82);
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_100, 0, x_12);
lean_ctor_set(x_100, 1, x_84);
lean_ctor_set(x_100, 2, x_85);
lean_ctor_set(x_100, 3, x_67);
lean_ctor_set(x_100, 4, x_67);
lean_ctor_set(x_11, 4, x_67);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_101 = lean_alloc_ctor(0, 5, 0);
} else {
 x_101 = x_9;
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_97);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_100);
lean_ctor_set(x_101, 4, x_11);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_11, 1);
x_103 = lean_ctor_get(x_11, 2);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_11);
x_104 = lean_ctor_get(x_82, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_82, 2);
lean_inc(x_105);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 lean_ctor_release(x_82, 3);
 lean_ctor_release(x_82, 4);
 x_106 = x_82;
} else {
 lean_dec_ref(x_82);
 x_106 = lean_box(0);
}
x_107 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_12);
lean_ctor_set(x_108, 1, x_102);
lean_ctor_set(x_108, 2, x_103);
lean_ctor_set(x_108, 3, x_67);
lean_ctor_set(x_108, 4, x_67);
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_12);
lean_ctor_set(x_109, 1, x_5);
lean_ctor_set(x_109, 2, x_6);
lean_ctor_set(x_109, 3, x_67);
lean_ctor_set(x_109, 4, x_67);
if (lean_is_scalar(x_9)) {
 x_110 = lean_alloc_ctor(0, 5, 0);
} else {
 x_110 = x_9;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_104);
lean_ctor_set(x_110, 2, x_105);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set(x_110, 4, x_109);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_112 = lean_alloc_ctor(0, 5, 0);
} else {
 x_112 = x_9;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_5);
lean_ctor_set(x_112, 2, x_6);
lean_ctor_set(x_112, 3, x_11);
lean_ctor_set(x_112, 4, x_82);
return x_112;
}
}
}
}
case 1:
{
lean_object* x_113; 
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_9)) {
 x_113 = lean_alloc_ctor(0, 5, 0);
} else {
 x_113 = x_9;
}
lean_ctor_set(x_113, 0, x_4);
lean_ctor_set(x_113, 1, x_1);
lean_ctor_set(x_113, 2, x_2);
lean_ctor_set(x_113, 3, x_7);
lean_ctor_set(x_113, 4, x_8);
return x_113;
}
default: 
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_4);
x_114 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(x_1, x_2, x_8);
x_115 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_116 = lean_ctor_get(x_7, 0);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_114, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 4);
lean_inc(x_121);
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_nat_mul(x_122, x_116);
x_124 = lean_nat_dec_lt(x_123, x_117);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
x_125 = lean_nat_add(x_115, x_116);
x_126 = lean_nat_add(x_125, x_117);
lean_dec(x_117);
lean_dec(x_125);
if (lean_is_scalar(x_9)) {
 x_127 = lean_alloc_ctor(0, 5, 0);
} else {
 x_127 = x_9;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_5);
lean_ctor_set(x_127, 2, x_6);
lean_ctor_set(x_127, 3, x_7);
lean_ctor_set(x_127, 4, x_114);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 x_128 = x_114;
} else {
 lean_dec_ref(x_114);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_120, 0);
x_130 = lean_ctor_get(x_120, 1);
x_131 = lean_ctor_get(x_120, 2);
x_132 = lean_ctor_get(x_120, 3);
x_133 = lean_ctor_get(x_120, 4);
x_134 = lean_ctor_get(x_121, 0);
x_135 = lean_unsigned_to_nat(2u);
x_136 = lean_nat_mul(x_135, x_134);
x_137 = lean_nat_dec_lt(x_129, x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_148; 
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 x_138 = x_120;
} else {
 lean_dec_ref(x_120);
 x_138 = lean_box(0);
}
x_139 = lean_nat_add(x_115, x_116);
x_140 = lean_nat_add(x_139, x_117);
lean_dec(x_117);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_132, 0);
lean_inc(x_155);
x_148 = x_155;
goto block_154;
}
else
{
lean_object* x_156; 
x_156 = lean_unsigned_to_nat(0u);
x_148 = x_156;
goto block_154;
}
block_147:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_nat_add(x_142, x_143);
lean_dec(x_143);
lean_dec(x_142);
if (lean_is_scalar(x_138)) {
 x_145 = lean_alloc_ctor(0, 5, 0);
} else {
 x_145 = x_138;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_118);
lean_ctor_set(x_145, 2, x_119);
lean_ctor_set(x_145, 3, x_133);
lean_ctor_set(x_145, 4, x_121);
if (lean_is_scalar(x_128)) {
 x_146 = lean_alloc_ctor(0, 5, 0);
} else {
 x_146 = x_128;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_130);
lean_ctor_set(x_146, 2, x_131);
lean_ctor_set(x_146, 3, x_141);
lean_ctor_set(x_146, 4, x_145);
return x_146;
}
block_154:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_nat_add(x_139, x_148);
lean_dec(x_148);
lean_dec(x_139);
if (lean_is_scalar(x_9)) {
 x_150 = lean_alloc_ctor(0, 5, 0);
} else {
 x_150 = x_9;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_5);
lean_ctor_set(x_150, 2, x_6);
lean_ctor_set(x_150, 3, x_7);
lean_ctor_set(x_150, 4, x_132);
x_151 = lean_nat_add(x_115, x_134);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_133, 0);
lean_inc(x_152);
x_141 = x_150;
x_142 = x_151;
x_143 = x_152;
goto block_147;
}
else
{
lean_object* x_153; 
x_153 = lean_unsigned_to_nat(0u);
x_141 = x_150;
x_142 = x_151;
x_143 = x_153;
goto block_147;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_9);
x_157 = lean_nat_add(x_115, x_116);
x_158 = lean_nat_add(x_157, x_117);
lean_dec(x_117);
x_159 = lean_nat_add(x_157, x_129);
lean_dec(x_157);
lean_inc_ref(x_7);
if (lean_is_scalar(x_128)) {
 x_160 = lean_alloc_ctor(0, 5, 0);
} else {
 x_160 = x_128;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_5);
lean_ctor_set(x_160, 2, x_6);
lean_ctor_set(x_160, 3, x_7);
lean_ctor_set(x_160, 4, x_120);
x_161 = !lean_is_exclusive(x_7);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_7, 4);
lean_dec(x_162);
x_163 = lean_ctor_get(x_7, 3);
lean_dec(x_163);
x_164 = lean_ctor_get(x_7, 2);
lean_dec(x_164);
x_165 = lean_ctor_get(x_7, 1);
lean_dec(x_165);
x_166 = lean_ctor_get(x_7, 0);
lean_dec(x_166);
lean_ctor_set(x_7, 4, x_121);
lean_ctor_set(x_7, 3, x_160);
lean_ctor_set(x_7, 2, x_119);
lean_ctor_set(x_7, 1, x_118);
lean_ctor_set(x_7, 0, x_158);
return x_7;
}
else
{
lean_object* x_167; 
lean_dec(x_7);
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_158);
lean_ctor_set(x_167, 1, x_118);
lean_ctor_set(x_167, 2, x_119);
lean_ctor_set(x_167, 3, x_160);
lean_ctor_set(x_167, 4, x_121);
return x_167;
}
}
}
}
else
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_114, 3);
lean_inc(x_168);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_114);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_114, 4);
x_171 = lean_ctor_get(x_114, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_114, 0);
lean_dec(x_172);
x_173 = !lean_is_exclusive(x_168);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_ctor_get(x_168, 1);
x_175 = lean_ctor_get(x_168, 2);
x_176 = lean_ctor_get(x_168, 4);
lean_dec(x_176);
x_177 = lean_ctor_get(x_168, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_168, 0);
lean_dec(x_178);
x_179 = lean_unsigned_to_nat(3u);
lean_inc_n(x_170, 2);
lean_ctor_set(x_168, 4, x_170);
lean_ctor_set(x_168, 3, x_170);
lean_ctor_set(x_168, 2, x_6);
lean_ctor_set(x_168, 1, x_5);
lean_ctor_set(x_168, 0, x_115);
lean_inc(x_170);
lean_ctor_set(x_114, 3, x_170);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_180 = lean_alloc_ctor(0, 5, 0);
} else {
 x_180 = x_9;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_174);
lean_ctor_set(x_180, 2, x_175);
lean_ctor_set(x_180, 3, x_168);
lean_ctor_set(x_180, 4, x_114);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_168, 1);
x_182 = lean_ctor_get(x_168, 2);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_168);
x_183 = lean_unsigned_to_nat(3u);
lean_inc_n(x_170, 2);
x_184 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_184, 0, x_115);
lean_ctor_set(x_184, 1, x_5);
lean_ctor_set(x_184, 2, x_6);
lean_ctor_set(x_184, 3, x_170);
lean_ctor_set(x_184, 4, x_170);
lean_inc(x_170);
lean_ctor_set(x_114, 3, x_170);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_185 = lean_alloc_ctor(0, 5, 0);
} else {
 x_185 = x_9;
}
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_181);
lean_ctor_set(x_185, 2, x_182);
lean_ctor_set(x_185, 3, x_184);
lean_ctor_set(x_185, 4, x_114);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_186 = lean_ctor_get(x_114, 4);
x_187 = lean_ctor_get(x_114, 1);
x_188 = lean_ctor_get(x_114, 2);
lean_inc(x_186);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_114);
x_189 = lean_ctor_get(x_168, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_168, 2);
lean_inc(x_190);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 lean_ctor_release(x_168, 4);
 x_191 = x_168;
} else {
 lean_dec_ref(x_168);
 x_191 = lean_box(0);
}
x_192 = lean_unsigned_to_nat(3u);
lean_inc_n(x_186, 2);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 5, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_115);
lean_ctor_set(x_193, 1, x_5);
lean_ctor_set(x_193, 2, x_6);
lean_ctor_set(x_193, 3, x_186);
lean_ctor_set(x_193, 4, x_186);
lean_inc(x_186);
x_194 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_194, 0, x_115);
lean_ctor_set(x_194, 1, x_187);
lean_ctor_set(x_194, 2, x_188);
lean_ctor_set(x_194, 3, x_186);
lean_ctor_set(x_194, 4, x_186);
if (lean_is_scalar(x_9)) {
 x_195 = lean_alloc_ctor(0, 5, 0);
} else {
 x_195 = x_9;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_189);
lean_ctor_set(x_195, 2, x_190);
lean_ctor_set(x_195, 3, x_193);
lean_ctor_set(x_195, 4, x_194);
return x_195;
}
}
else
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_114, 4);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_114);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_198 = lean_ctor_get(x_114, 1);
x_199 = lean_ctor_get(x_114, 2);
x_200 = lean_ctor_get(x_114, 4);
lean_dec(x_200);
x_201 = lean_ctor_get(x_114, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_114, 0);
lean_dec(x_202);
x_203 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_114, 4, x_168);
lean_ctor_set(x_114, 2, x_6);
lean_ctor_set(x_114, 1, x_5);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_204 = lean_alloc_ctor(0, 5, 0);
} else {
 x_204 = x_9;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_198);
lean_ctor_set(x_204, 2, x_199);
lean_ctor_set(x_204, 3, x_114);
lean_ctor_set(x_204, 4, x_196);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_114, 1);
x_206 = lean_ctor_get(x_114, 2);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_114);
x_207 = lean_unsigned_to_nat(3u);
x_208 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_208, 0, x_115);
lean_ctor_set(x_208, 1, x_5);
lean_ctor_set(x_208, 2, x_6);
lean_ctor_set(x_208, 3, x_168);
lean_ctor_set(x_208, 4, x_168);
if (lean_is_scalar(x_9)) {
 x_209 = lean_alloc_ctor(0, 5, 0);
} else {
 x_209 = x_9;
}
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_205);
lean_ctor_set(x_209, 2, x_206);
lean_ctor_set(x_209, 3, x_208);
lean_ctor_set(x_209, 4, x_196);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_211 = lean_alloc_ctor(0, 5, 0);
} else {
 x_211 = x_9;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_5);
lean_ctor_set(x_211, 2, x_6);
lean_ctor_set(x_211, 3, x_196);
lean_ctor_set(x_211, 4, x_114);
return x_211;
}
}
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_unsigned_to_nat(1u);
x_213 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_1);
lean_ctor_set(x_213, 2, x_2);
lean_ctor_set(x_213, 3, x_3);
lean_ctor_set(x_213, 4, x_3);
return x_213;
}
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lake_ExternLib_defaultFacetConfig;
x_3 = l_Lake_ExternLib_defaultFacet;
x_4 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_ExternLib_initFacetConfigs___closed__0;
x_2 = l_Lake_ExternLib_staticFacetConfig;
x_3 = l_Lake_ExternLib_staticFacet;
x_4 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_ExternLib_initFacetConfigs___closed__1;
x_2 = l_Lake_ExternLib_sharedFacetConfig;
x_3 = l_Lake_ExternLib_sharedFacet;
x_4 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_ExternLib_initFacetConfigs___closed__2;
x_2 = l_Lake_ExternLib_dynlibFacetConfig;
x_3 = l_Lake_ExternLib_dynlibFacet;
x_4 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_ExternLib_initFacetConfigs___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* initialize_Lake_Build_Common(uint8_t builtin);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_ExternLib(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Register(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Common(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0 = _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0);
l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1 = _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1);
l_Lake_ExternLib_staticFacetConfig___closed__0 = _init_l_Lake_ExternLib_staticFacetConfig___closed__0();
lean_mark_persistent(l_Lake_ExternLib_staticFacetConfig___closed__0);
l_Lake_ExternLib_staticFacetConfig___closed__1 = _init_l_Lake_ExternLib_staticFacetConfig___closed__1();
lean_mark_persistent(l_Lake_ExternLib_staticFacetConfig___closed__1);
l_Lake_ExternLib_staticFacetConfig___closed__2 = _init_l_Lake_ExternLib_staticFacetConfig___closed__2();
lean_mark_persistent(l_Lake_ExternLib_staticFacetConfig___closed__2);
l_Lake_ExternLib_staticFacetConfig = _init_l_Lake_ExternLib_staticFacetConfig();
lean_mark_persistent(l_Lake_ExternLib_staticFacetConfig);
l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0);
l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1);
l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2);
l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3);
l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4);
l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5);
l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__6 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__6();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__6);
l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__7 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__7();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__7);
l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__8 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__8();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__8);
l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0 = _init_l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0();
lean_mark_persistent(l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0);
l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0 = _init_l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0();
lean_mark_persistent(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0);
l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1 = _init_l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1();
lean_mark_persistent(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1);
l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2 = _init_l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2();
lean_mark_persistent(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2);
l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0);
l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1);
l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2);
l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3);
l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4 = _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4);
l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0 = _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0);
l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1 = _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1);
l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2 = _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2);
l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0 = _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0);
l_Lake_ExternLib_sharedFacetConfig___closed__0 = _init_l_Lake_ExternLib_sharedFacetConfig___closed__0();
lean_mark_persistent(l_Lake_ExternLib_sharedFacetConfig___closed__0);
l_Lake_ExternLib_sharedFacetConfig___closed__1 = _init_l_Lake_ExternLib_sharedFacetConfig___closed__1();
lean_mark_persistent(l_Lake_ExternLib_sharedFacetConfig___closed__1);
l_Lake_ExternLib_sharedFacetConfig = _init_l_Lake_ExternLib_sharedFacetConfig();
lean_mark_persistent(l_Lake_ExternLib_sharedFacetConfig);
l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0 = _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0);
l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1 = _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1);
l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2 = _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2);
l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3 = _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3);
l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4 = _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4);
l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5 = _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5);
l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0 = _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0);
l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0 = _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0();
lean_mark_persistent(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0);
l_Lake_ExternLib_dynlibFacetConfig___closed__0 = _init_l_Lake_ExternLib_dynlibFacetConfig___closed__0();
lean_mark_persistent(l_Lake_ExternLib_dynlibFacetConfig___closed__0);
l_Lake_ExternLib_dynlibFacetConfig___closed__1 = _init_l_Lake_ExternLib_dynlibFacetConfig___closed__1();
lean_mark_persistent(l_Lake_ExternLib_dynlibFacetConfig___closed__1);
l_Lake_ExternLib_dynlibFacetConfig___closed__2 = _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2();
lean_mark_persistent(l_Lake_ExternLib_dynlibFacetConfig___closed__2);
l_Lake_ExternLib_dynlibFacetConfig = _init_l_Lake_ExternLib_dynlibFacetConfig();
lean_mark_persistent(l_Lake_ExternLib_dynlibFacetConfig);
l_Lake_ExternLib_defaultFacetConfig___closed__0 = _init_l_Lake_ExternLib_defaultFacetConfig___closed__0();
lean_mark_persistent(l_Lake_ExternLib_defaultFacetConfig___closed__0);
l_Lake_ExternLib_defaultFacetConfig___closed__1 = _init_l_Lake_ExternLib_defaultFacetConfig___closed__1();
lean_mark_persistent(l_Lake_ExternLib_defaultFacetConfig___closed__1);
l_Lake_ExternLib_defaultFacetConfig = _init_l_Lake_ExternLib_defaultFacetConfig();
lean_mark_persistent(l_Lake_ExternLib_defaultFacetConfig);
l_Lake_ExternLib_initFacetConfigs___closed__0 = _init_l_Lake_ExternLib_initFacetConfigs___closed__0();
lean_mark_persistent(l_Lake_ExternLib_initFacetConfigs___closed__0);
l_Lake_ExternLib_initFacetConfigs___closed__1 = _init_l_Lake_ExternLib_initFacetConfigs___closed__1();
lean_mark_persistent(l_Lake_ExternLib_initFacetConfigs___closed__1);
l_Lake_ExternLib_initFacetConfigs___closed__2 = _init_l_Lake_ExternLib_initFacetConfigs___closed__2();
lean_mark_persistent(l_Lake_ExternLib_initFacetConfigs___closed__2);
l_Lake_ExternLib_initFacetConfigs___closed__3 = _init_l_Lake_ExternLib_initFacetConfigs___closed__3();
lean_mark_persistent(l_Lake_ExternLib_initFacetConfigs___closed__3);
l_Lake_ExternLib_initFacetConfigs = _init_l_Lake_ExternLib_initFacetConfigs();
lean_mark_persistent(l_Lake_ExternLib_initFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
