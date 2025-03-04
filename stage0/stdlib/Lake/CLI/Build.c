// Lean compiler output
// Module: Lake.CLI.Build
// Imports: Lake.Config.Monad Lake.Build.Job Lake.CLI.Error
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
LEAN_EXPORT lean_object* l_Lake_resolveDefaultPackageTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveTargetBaseSpec(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolveTargetBaseSpec___closed__5;
lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lake_parseTargetSpecs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l_Lake_resolveTargetInPackage___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lake_parseTargetSpecs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_BuildInfo_key(lean_object*);
static lean_object* l_Lake_resolveExternLibTarget___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
static lean_object* l_Lake_resolveExeTarget___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_resolveLibTarget___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bind_bindLeft___at_Lake_BuildSpec_query___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___rarg(lean_object*);
static lean_object* l_Lake_resolveExeTarget___closed__4;
LEAN_EXPORT lean_object* l_Lake_resolveExeTarget(lean_object*, lean_object*);
static lean_object* l_Lake_resolveTargetBaseSpec___closed__9;
LEAN_EXPORT lean_object* l_Lake_querySpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveDefaultPackageTarget___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_resolveLibTarget_resolveFacet___closed__1;
LEAN_EXPORT lean_object* l_Lake_RBNode_dFind___at_Lake_resolveTargetInPackage___spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveModuleTarget(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_querySpecs___spec__1(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveExternLibTarget(lean_object*, lean_object*);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolveExternLibTarget___closed__4;
lean_object* l_Lake_Job_mixArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___rarg(lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_parseTargetSpec___closed__2;
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_buildSpecs___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolveExternLibTarget___closed__2;
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec___boxed__const__1;
lean_object* l_Lake_Workspace_findExternLib_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkBuildSpec(lean_object*);
lean_object* l_Lake_nullFormat___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkBuildSpec___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_resolveLibTarget___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolvePackageTarget___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolvePackageTarget___closed__1;
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_BuildSpec_query___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildKey_toSimpleString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_BuildSpec_query___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_parseTargetSpecs___closed__2;
lean_object* l_Lake_Package_findTargetConfig_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
static lean_object* l_Lake_parseTargetSpecs___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveCustomTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolvePackageTarget(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolveExternLibTarget___closed__5;
static lean_object* l_Lake_resolveExternLibTarget___closed__1;
static lean_object* l_Lake_resolveTargetBaseSpec___closed__8;
static lean_object* l_Lake_resolveExeTarget___closed__3;
LEAN_EXPORT lean_object* l_Lake_resolveCustomTarget(lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_resolveTargetBaseSpec___closed__11;
lean_object* l_Lake_EResult_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveModuleTarget___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolveModuleTarget___closed__4;
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_collectArray___rarg(lean_object*);
static lean_object* l_Lake_resolveModuleTarget___closed__1;
static lean_object* l_Lake_resolveTargetBaseSpec___closed__4;
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveTargetBaseSpec___boxed__const__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_parseTargetSpec___closed__1;
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_querySpecs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_resolveExeTarget___spec__1(uint8_t, lean_object*);
lean_object* l_Lake_Workspace_findLeanLib_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_querySpecs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findTargetConfig_x3f(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_resolveExeTarget___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_resolveTargetBaseSpec___closed__3;
static lean_object* l_Lake_resolveModuleTarget___closed__3;
static lean_object* l_Lake_resolveModuleTarget___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_resolveDefaultPackageTarget___closed__1;
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_resolveDefaultPackageTarget___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolveTargetInPackage___closed__1;
static lean_object* l_Lake_resolveTargetBaseSpec___closed__2;
lean_object* l_String_toName(lean_object*);
static lean_object* l_Lake_resolveTargetBaseSpec___closed__1;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
static lean_object* l_Lake_resolveExeTarget___closed__1;
uint8_t l_Substring_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_resolveTargetInWorkspace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_RBNode_find___at_Lake_Package_findLeanLib_x3f___spec__1(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveTargetInPackage___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolveTargetBaseSpec___closed__6;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_resolveTargetBaseSpec___closed__10;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_buildSpecs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___lambda__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_resolveTargetBaseSpec___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_resolveDefaultPackageTarget___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_resolveDefaultPackageTarget___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveTargetInWorkspace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget_resolveFacet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveTargetInPackage___lambda__1___boxed(lean_object*);
lean_object* l_Lake_maybeRegisterJob___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveTargetInPackage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget_resolveFacet___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBNode_dFind___at_Lake_resolveTargetInPackage___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkBuildSpec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_mkBuildSpec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_mkBuildSpec___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_mkConfigBuildSpec___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_mkConfigBuildSpec(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_8);
x_9 = lean_apply_6(x_2, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = l_Lake_BuildInfo_key(x_8);
x_17 = l_Lake_BuildKey_toSimpleString(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
x_20 = lean_string_utf8_byte_size(x_19);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_5);
return x_9;
}
else
{
uint8_t x_23; 
lean_free_object(x_9);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_24 = lean_ctor_get(x_15, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = 0;
lean_ctor_set(x_15, 1, x_17);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_26);
x_27 = lean_ctor_get(x_5, 3);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_st_ref_take(x_27, x_12);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_15);
x_31 = lean_array_push(x_29, x_15);
x_32 = lean_st_ref_set(x_27, x_31, x_30);
lean_dec(x_27);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = l_Lake_Job_renew___rarg(x_15);
lean_ctor_set(x_10, 0, x_35);
lean_ctor_set(x_32, 0, x_10);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = l_Lake_Job_renew___rarg(x_15);
lean_ctor_set(x_10, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_15);
x_39 = 0;
x_40 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_40, 0, x_18);
lean_ctor_set(x_40, 1, x_17);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_39);
x_41 = lean_ctor_get(x_5, 3);
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_st_ref_take(x_41, x_12);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_40);
x_45 = lean_array_push(x_43, x_40);
x_46 = lean_st_ref_set(x_41, x_45, x_44);
lean_dec(x_41);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = l_Lake_Job_renew___rarg(x_40);
lean_ctor_set(x_10, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_51 = lean_ctor_get(x_10, 0);
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_10);
x_53 = l_Lake_BuildInfo_key(x_8);
x_54 = l_Lake_BuildKey_toSimpleString(x_53);
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
x_57 = lean_string_utf8_byte_size(x_56);
lean_dec(x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_eq(x_57, x_58);
lean_dec(x_57);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_5);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_51);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_9, 0, x_60);
return x_9;
}
else
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_free_object(x_9);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_61 = x_51;
} else {
 lean_dec_ref(x_51);
 x_61 = lean_box(0);
}
x_62 = 0;
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 1);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_55);
lean_ctor_set(x_63, 1, x_54);
lean_ctor_set_uint8(x_63, sizeof(void*)*2, x_62);
x_64 = lean_ctor_get(x_5, 3);
lean_inc(x_64);
lean_dec(x_5);
x_65 = lean_st_ref_take(x_64, x_12);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_63);
x_68 = lean_array_push(x_66, x_63);
x_69 = lean_st_ref_set(x_64, x_68, x_67);
lean_dec(x_64);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = l_Lake_Job_renew___rarg(x_63);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_52);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_75 = lean_ctor_get(x_9, 1);
lean_inc(x_75);
lean_dec(x_9);
x_76 = lean_ctor_get(x_10, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_10, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_78 = x_10;
} else {
 lean_dec_ref(x_10);
 x_78 = lean_box(0);
}
x_79 = l_Lake_BuildInfo_key(x_8);
x_80 = l_Lake_BuildKey_toSimpleString(x_79);
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
x_83 = lean_string_utf8_byte_size(x_82);
lean_dec(x_82);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_eq(x_83, x_84);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_5);
if (lean_is_scalar(x_78)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_78;
}
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_77);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_75);
return x_87;
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_88 = x_76;
} else {
 lean_dec_ref(x_76);
 x_88 = lean_box(0);
}
x_89 = 0;
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 1);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_81);
lean_ctor_set(x_90, 1, x_80);
lean_ctor_set_uint8(x_90, sizeof(void*)*2, x_89);
x_91 = lean_ctor_get(x_5, 3);
lean_inc(x_91);
lean_dec(x_5);
x_92 = lean_st_ref_take(x_91, x_75);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_90);
x_95 = lean_array_push(x_93, x_90);
x_96 = lean_st_ref_set(x_91, x_95, x_94);
lean_dec(x_91);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
x_99 = l_Lake_Job_renew___rarg(x_90);
if (lean_is_scalar(x_78)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_78;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_77);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_98;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_97);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_8);
lean_dec(x_5);
x_102 = !lean_is_exclusive(x_9);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_9, 0);
lean_dec(x_103);
x_104 = !lean_is_exclusive(x_10);
if (x_104 == 0)
{
return x_9;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_10, 0);
x_106 = lean_ctor_get(x_10, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_10);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_9, 0, x_107);
return x_9;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_9, 1);
lean_inc(x_108);
lean_dec(x_9);
x_109 = lean_ctor_get(x_10, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_10, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_111 = x_10;
} else {
 lean_dec_ref(x_10);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_108);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_8);
lean_dec(x_5);
x_114 = !lean_is_exclusive(x_9);
if (x_114 == 0)
{
return x_9;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_9, 0);
x_116 = lean_ctor_get(x_9, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_9);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_23);
x_24 = lean_apply_6(x_2, x_23, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = l_Lake_BuildInfo_key(x_23);
x_30 = l_Lake_BuildKey_toSimpleString(x_29);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
x_33 = lean_string_utf8_byte_size(x_32);
lean_dec(x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_5);
x_8 = x_25;
x_9 = x_26;
goto block_22;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_28, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = 0;
lean_ctor_set(x_28, 1, x_30);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_39);
x_40 = lean_ctor_get(x_5, 3);
lean_inc(x_40);
lean_dec(x_5);
x_41 = lean_st_ref_take(x_40, x_26);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_28);
x_44 = lean_array_push(x_42, x_28);
x_45 = lean_st_ref_set(x_40, x_44, x_43);
lean_dec(x_40);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lake_Job_renew___rarg(x_28);
lean_ctor_set(x_25, 0, x_47);
x_8 = x_25;
x_9 = x_46;
goto block_22;
}
else
{
uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_28);
x_48 = 0;
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_31);
lean_ctor_set(x_49, 1, x_30);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_48);
x_50 = lean_ctor_get(x_5, 3);
lean_inc(x_50);
lean_dec(x_5);
x_51 = lean_st_ref_take(x_50, x_26);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_49);
x_54 = lean_array_push(x_52, x_49);
x_55 = lean_st_ref_set(x_50, x_54, x_53);
lean_dec(x_50);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lake_Job_renew___rarg(x_49);
lean_ctor_set(x_25, 0, x_57);
x_8 = x_25;
x_9 = x_56;
goto block_22;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_58 = lean_ctor_get(x_25, 0);
x_59 = lean_ctor_get(x_25, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_25);
x_60 = l_Lake_BuildInfo_key(x_23);
x_61 = l_Lake_BuildKey_toSimpleString(x_60);
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
x_64 = lean_string_utf8_byte_size(x_63);
lean_dec(x_63);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_5);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_59);
x_8 = x_67;
x_9 = x_26;
goto block_22;
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_68 = x_58;
} else {
 lean_dec_ref(x_58);
 x_68 = lean_box(0);
}
x_69 = 0;
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 1);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_62);
lean_ctor_set(x_70, 1, x_61);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_69);
x_71 = lean_ctor_get(x_5, 3);
lean_inc(x_71);
lean_dec(x_5);
x_72 = lean_st_ref_take(x_71, x_26);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_70);
x_75 = lean_array_push(x_73, x_70);
x_76 = lean_st_ref_set(x_71, x_75, x_74);
lean_dec(x_71);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lake_Job_renew___rarg(x_70);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_59);
x_8 = x_79;
x_9 = x_77;
goto block_22;
}
}
}
else
{
lean_object* x_80; uint8_t x_81; 
lean_dec(x_23);
lean_dec(x_5);
x_80 = lean_ctor_get(x_24, 1);
lean_inc(x_80);
lean_dec(x_24);
x_81 = !lean_is_exclusive(x_25);
if (x_81 == 0)
{
x_8 = x_25;
x_9 = x_80;
goto block_22;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_25, 0);
x_83 = lean_ctor_get(x_25, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_25);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_8 = x_84;
x_9 = x_80;
goto block_22;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_23);
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_24);
if (x_85 == 0)
{
return x_24;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_24, 0);
x_87 = lean_ctor_get(x_24, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_24);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
block_22:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_BuildSpec_query___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_apply_7(x_2, x_12, x_3, x_4, x_5, x_6, x_13, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_24 = x_10;
} else {
 lean_dec_ref(x_10);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_BuildSpec_query___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_BuildSpec_query___spec__1___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Bind_bindLeft___at_Lake_BuildSpec_query___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_apply_7(x_1, x_12, x_3, x_4, x_5, x_6, x_13, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_24 = x_10;
} else {
 lean_dec_ref(x_10);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box(x_2);
x_12 = lean_apply_1(x_10, x_11);
x_13 = lean_alloc_closure((void*)(l_Lake_EResult_map___rarg), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = l_Task_Priority_default;
x_17 = 0;
x_18 = lean_task_map(x_13, x_15, x_16, x_17);
lean_ctor_set(x_3, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_8);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_24 = l_Task_Priority_default;
x_25 = 0;
x_26 = lean_task_map(x_13, x_21, x_24, x_25);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_inc(x_9);
x_10 = l_Lake_BuildInfo_key(x_9);
x_11 = l_Lake_BuildKey_toSimpleString(x_10);
x_12 = lean_alloc_closure((void*)(l_Lake_maybeRegisterJob___rarg___boxed), 8, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, lean_box(0));
x_14 = lean_box(x_2);
x_15 = lean_alloc_closure((void*)(l_Lake_BuildSpec_query___lambda__1___boxed), 9, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_BuildSpec_query___spec__1___rarg), 8, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Bind_bindLeft___at_Lake_BuildSpec_query___spec__2(x_12, x_16, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lake_BuildSpec_query___lambda__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_BuildSpec_query(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_buildSpecs___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_31; lean_object* x_32; lean_object* x_42; lean_object* x_43; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_42 = lean_ctor_get(x_13, 0);
lean_inc(x_42);
lean_dec(x_13);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_42);
x_43 = lean_apply_6(x_4, x_42, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = l_Lake_BuildInfo_key(x_42);
x_49 = l_Lake_BuildKey_toSimpleString(x_48);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
x_52 = lean_string_utf8_byte_size(x_51);
lean_dec(x_51);
x_53 = lean_nat_dec_eq(x_52, x_14);
lean_dec(x_52);
if (x_53 == 0)
{
lean_dec(x_50);
lean_dec(x_49);
x_31 = x_44;
x_32 = x_45;
goto block_41;
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_55 = lean_ctor_get(x_47, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_47, 0);
lean_dec(x_56);
x_57 = 0;
lean_ctor_set(x_47, 1, x_49);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_57);
x_58 = lean_ctor_get(x_7, 3);
lean_inc(x_58);
x_59 = lean_st_ref_take(x_58, x_45);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_47);
x_62 = lean_array_push(x_60, x_47);
x_63 = lean_st_ref_set(x_58, x_62, x_61);
lean_dec(x_58);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lake_Job_renew___rarg(x_47);
lean_ctor_set(x_44, 0, x_65);
x_31 = x_44;
x_32 = x_64;
goto block_41;
}
else
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_47);
x_66 = 0;
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_50);
lean_ctor_set(x_67, 1, x_49);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_66);
x_68 = lean_ctor_get(x_7, 3);
lean_inc(x_68);
x_69 = lean_st_ref_take(x_68, x_45);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_67);
x_72 = lean_array_push(x_70, x_67);
x_73 = lean_st_ref_set(x_68, x_72, x_71);
lean_dec(x_68);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lake_Job_renew___rarg(x_67);
lean_ctor_set(x_44, 0, x_75);
x_31 = x_44;
x_32 = x_74;
goto block_41;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_76 = lean_ctor_get(x_44, 0);
x_77 = lean_ctor_get(x_44, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_44);
x_78 = l_Lake_BuildInfo_key(x_42);
x_79 = l_Lake_BuildKey_toSimpleString(x_78);
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
x_82 = lean_string_utf8_byte_size(x_81);
lean_dec(x_81);
x_83 = lean_nat_dec_eq(x_82, x_14);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_80);
lean_dec(x_79);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_77);
x_31 = x_84;
x_32 = x_45;
goto block_41;
}
else
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_85 = x_76;
} else {
 lean_dec_ref(x_76);
 x_85 = lean_box(0);
}
x_86 = 0;
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 1);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_86);
x_88 = lean_ctor_get(x_7, 3);
lean_inc(x_88);
x_89 = lean_st_ref_take(x_88, x_45);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_87);
x_92 = lean_array_push(x_90, x_87);
x_93 = lean_st_ref_set(x_88, x_92, x_91);
lean_dec(x_88);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = l_Lake_Job_renew___rarg(x_87);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_77);
x_31 = x_96;
x_32 = x_94;
goto block_41;
}
}
}
else
{
lean_object* x_97; uint8_t x_98; 
lean_dec(x_42);
x_97 = lean_ctor_get(x_43, 1);
lean_inc(x_97);
lean_dec(x_43);
x_98 = !lean_is_exclusive(x_44);
if (x_98 == 0)
{
x_31 = x_44;
x_32 = x_97;
goto block_41;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_44, 0);
x_100 = lean_ctor_get(x_44, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_44);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_31 = x_101;
x_32 = x_97;
goto block_41;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_42);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_102 = !lean_is_exclusive(x_43);
if (x_102 == 0)
{
return x_43;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_43, 0);
x_104 = lean_ctor_get(x_43, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_43);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
block_30:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_15, x_2, x_18);
x_2 = x_21;
x_3 = x_22;
x_8 = x_19;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_17);
return x_29;
}
}
}
block_41:
{
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
x_16 = x_31;
x_17 = x_32;
goto block_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_16 = x_36;
x_17 = x_32;
goto block_30;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
x_16 = x_31;
x_17 = x_32;
goto block_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_31);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_16 = x_40;
x_17 = x_32;
goto block_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSpecs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_array_size(x_1);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at_Lake_buildSpecs___spec__1(x_8, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = l_Lake_Job_mixArray___rarg(x_15);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = l_Lake_Job_mixArray___rarg(x_17);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_24 = x_11;
} else {
 lean_dec_ref(x_11);
 x_24 = lean_box(0);
}
x_25 = l_Lake_Job_mixArray___rarg(x_22);
lean_dec(x_22);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_10, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_11);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_10, 0, x_33);
return x_10;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_dec(x_10);
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_37 = x_11;
} else {
 lean_dec_ref(x_11);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_buildSpecs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lake_buildSpecs___spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_querySpecs___spec__1(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_inc(x_17);
x_18 = l_Lake_BuildInfo_key(x_17);
x_19 = l_Lake_BuildKey_toSimpleString(x_18);
x_20 = lean_alloc_closure((void*)(l_Lake_maybeRegisterJob___rarg___boxed), 8, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, lean_box(0));
x_22 = lean_box(x_1);
x_23 = lean_alloc_closure((void*)(l_Lake_BuildSpec_query___lambda__1___boxed), 9, 2);
lean_closure_set(x_23, 0, x_14);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_BuildSpec_query___spec__1___rarg), 8, 2);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Bind_bindLeft___at_Lake_BuildSpec_query___spec__2(x_20, x_24, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_32 = lean_array_uset(x_16, x_3, x_28);
x_3 = x_31;
x_4 = x_32;
x_9 = x_29;
x_10 = x_27;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_25, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_25, 0, x_39);
return x_25;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_ctor_get(x_26, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_43 = x_26;
} else {
 lean_dec_ref(x_26);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_querySpecs(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lake_querySpecs___spec__1(x_2, x_9, x_10, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = l_Lake_Job_collectArray___rarg(x_16);
lean_dec(x_16);
lean_ctor_set(x_12, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = l_Lake_Job_collectArray___rarg(x_18);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_25 = x_12;
} else {
 lean_dec_ref(x_12);
 x_25 = lean_box(0);
}
x_26 = l_Lake_Job_collectArray___rarg(x_23);
lean_dec(x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_11, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_11, 0, x_34);
return x_11;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_ctor_get(x_12, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_38 = x_12;
} else {
 lean_dec_ref(x_12);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
return x_11;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_querySpecs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lake_querySpecs___spec__1(x_11, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_querySpecs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_querySpecs(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_6 = l_Lake_stringToLegalOrSimpleName(x_2);
x_7 = lean_ctor_get(x_1, 4);
x_8 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_7, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_parsePackageSpec(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_resolveModuleTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveModuleTarget___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanArts", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveModuleTarget___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_resolveModuleTarget___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_resolveModuleTarget___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_nullFormat___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveModuleTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Name_isAnonymous(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_findModuleFacetConfig_x3f(x_3, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = l_Lake_resolveModuleTarget___closed__1;
x_7 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_11);
return x_5;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_14);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
x_19 = lean_ctor_get_uint8(x_17, sizeof(void*)*2);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_21 = x_17;
} else {
 lean_dec_ref(x_17);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 2, 1);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_19);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
x_24 = l_Lake_resolveModuleTarget___closed__3;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = l_Lake_resolveModuleTarget___closed__4;
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveModuleTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_resolveModuleTarget(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_resolveLibTarget_resolveFacet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("library", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget_resolveFacet(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Workspace_findLibraryFacetConfig_x3f(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = l_Lake_resolveLibTarget_resolveFacet___closed__1;
x_6 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_10);
return x_4;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_13);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_20 = x_16;
} else {
 lean_dec_ref(x_16);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(0, 2, 1);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_18);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget_resolveFacet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_resolveLibTarget_resolveFacet(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_resolveLibTarget___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_5, x_4, x_9);
lean_inc(x_2);
x_11 = l_Lake_resolveLibTarget_resolveFacet(x_1, x_2, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_10);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
x_18 = lean_array_uset(x_10, x_4, x_15);
x_4 = x_17;
x_5 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Name_isAnonymous(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lake_resolveLibTarget_resolveFacet(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_mk(x_12);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_array_mk(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
lean_dec(x_3);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 7);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_array_size(x_20);
x_22 = 0;
x_23 = l_Array_mapMUnsafe_map___at_Lake_resolveLibTarget___spec__1(x_1, x_2, x_21, x_22, x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_resolveLibTarget___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lake_resolveLibTarget___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_resolveLibTarget(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_resolveExeTarget___spec__1(uint8_t x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lake_resolveExeTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exe", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveExeTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_resolveExeTarget___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_resolveExeTarget___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("executable", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveExeTarget___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_stdFormat___at_Lake_resolveExeTarget___spec__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveExeTarget(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_isAnonymous(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lake_resolveExeTarget___closed__2;
x_5 = lean_name_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = l_Lake_resolveExeTarget___closed__3;
x_7 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = 1;
x_11 = l_Lake_resolveExeTarget___closed__4;
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = 1;
x_16 = l_Lake_resolveExeTarget___closed__4;
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_resolveExeTarget___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at_Lake_resolveExeTarget___spec__1(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_resolveExternLibTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("static", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveExternLibTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_resolveExternLibTarget___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_resolveExternLibTarget___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shared", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveExternLibTarget___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_resolveExternLibTarget___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_resolveExternLibTarget___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("external library", 16, 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveExternLibTarget(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_isAnonymous(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lake_resolveExternLibTarget___closed__2;
x_5 = lean_name_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lake_resolveExternLibTarget___closed__4;
x_7 = lean_name_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_8 = l_Lake_resolveExternLibTarget___closed__5;
x_9 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = 1;
x_13 = l_Lake_resolveExeTarget___closed__4;
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = 1;
x_18 = l_Lake_resolveExeTarget___closed__4;
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = 1;
x_23 = l_Lake_resolveExeTarget___closed__4;
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveCustomTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Name_isAnonymous(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_alloc_ctor(19, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_ctor_get(x_4, 1);
x_10 = 1;
lean_inc(x_9);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveCustomTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_resolveCustomTarget(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_RBNode_dFind___at_Lake_resolveTargetInPackage___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = l_Lean_Name_quickCmp(x_3, x_6);
switch (x_9) {
case 0:
{
x_2 = x_5;
goto _start;
}
case 1:
{
lean_object* x_11; 
lean_inc(x_7);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_7);
return x_11;
}
default: 
{
x_2 = x_8;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_resolveTargetInPackage___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lake_resolveTargetInPackage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_resolveTargetInPackage___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveTargetInPackage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_findTargetConfig_x3f(x_3, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 9);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_7, x_3);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 10);
lean_inc(x_9);
x_10 = l_Lake_RBNode_dFind___at_Lake_resolveTargetInPackage___spec__1(x_2, x_9, x_3);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 8);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_RBNode_find___at_Lake_Package_findLeanLib_x3f___spec__1(x_12, x_3);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_inc(x_2);
lean_inc(x_3);
x_14 = l_Lake_Package_findTargetModule_x3f(x_3, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 0;
x_18 = l_Lake_resolveTargetInPackage___closed__1;
x_19 = l_Lean_Name_toString(x_3, x_17, x_18);
x_20 = lean_alloc_ctor(16, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lake_resolveModuleTarget(x_1, x_22, x_4);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_mk(x_30);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_mk(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_3);
x_37 = lean_ctor_get(x_13, 0);
lean_inc(x_37);
lean_dec(x_13);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lake_resolveLibTarget(x_1, x_38, x_4);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_10, 0);
lean_inc(x_40);
lean_dec(x_10);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_3);
lean_ctor_set(x_41, 2, x_40);
x_42 = l_Lake_resolveExternLibTarget(x_41, x_4);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_mk(x_49);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_mk(x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_3);
x_56 = lean_ctor_get(x_8, 0);
lean_inc(x_56);
lean_dec(x_8);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lake_resolveExeTarget(x_57, x_4);
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
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_mk(x_65);
lean_ctor_set(x_58, 0, x_66);
return x_58;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_58, 0);
lean_inc(x_67);
lean_dec(x_58);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_mk(x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_5, 0);
lean_inc(x_72);
lean_dec(x_5);
x_73 = l_Lake_resolveCustomTarget(x_2, x_3, x_4, x_72);
lean_dec(x_72);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
return x_73;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 0);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_array_mk(x_80);
lean_ctor_set(x_73, 0, x_81);
return x_73;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_73, 0);
lean_inc(x_82);
lean_dec(x_73);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_array_mk(x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBNode_dFind___at_Lake_resolveTargetInPackage___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_RBNode_dFind___at_Lake_resolveTargetInPackage___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveTargetInPackage___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_resolveTargetInPackage___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveTargetInPackage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_resolveTargetInPackage(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_resolveDefaultPackageTarget___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_uget(x_3, x_4);
x_9 = lean_box(0);
lean_inc(x_2);
x_10 = l_Lake_resolveTargetInPackage(x_1, x_2, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Array_append___rarg(x_6, x_14);
lean_dec(x_14);
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
x_4 = x_17;
x_6 = x_15;
goto _start;
}
}
else
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
}
}
static lean_object* _init_l_Lake_resolveDefaultPackageTarget___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_resolveDefaultPackageTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_resolveDefaultPackageTarget___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveDefaultPackageTarget(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 12);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = l_Lake_resolveDefaultPackageTarget___closed__2;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = l_Lake_resolveDefaultPackageTarget___closed__2;
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_12 = l_Lake_resolveDefaultPackageTarget___closed__1;
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_resolveDefaultPackageTarget___spec__1(x_1, x_2, x_3, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_resolveDefaultPackageTarget___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_resolveDefaultPackageTarget___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveDefaultPackageTarget___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_resolveDefaultPackageTarget(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_resolvePackageTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePackageTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Name_isAnonymous(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_findPackageFacetConfig_x3f(x_3, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = l_Lake_resolvePackageTarget___closed__1;
x_7 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_mk(x_15);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_17);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_mk(x_21);
lean_ctor_set(x_5, 0, x_22);
return x_5;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
x_25 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 1);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_25);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_mk(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_3);
x_33 = l_Lake_resolveDefaultPackageTarget(x_1, x_2);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePackageTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_resolvePackageTarget(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveTargetInWorkspace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Workspace_findTargetConfig_x3f(x_2, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_findLeanExe_x3f(x_2, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l_Lake_Workspace_findExternLib_x3f(x_2, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Lake_Workspace_findLeanLib_x3f(x_2, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 4);
x_9 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_8, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_inc(x_2);
x_10 = l_Lake_Workspace_findTargetModule_x3f(x_2, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_11 = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(x_11, 0, x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lake_resolveModuleTarget(x_1, x_13, x_3);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
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
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_mk(x_21);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_array_mk(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
lean_dec(x_9);
x_29 = l_Lake_resolvePackageTarget(x_1, x_28, x_3);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_30 = lean_ctor_get(x_7, 0);
lean_inc(x_30);
lean_dec(x_7);
x_31 = l_Lake_resolveLibTarget(x_1, x_30, x_3);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
lean_dec(x_6);
x_33 = l_Lake_resolveExternLibTarget(x_32, x_3);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_array_mk(x_40);
lean_ctor_set(x_33, 0, x_41);
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_mk(x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
x_47 = lean_ctor_get(x_5, 0);
lean_inc(x_47);
lean_dec(x_5);
x_48 = l_Lake_resolveExeTarget(x_47, x_3);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_array_mk(x_55);
lean_ctor_set(x_48, 0, x_56);
return x_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_48, 0);
lean_inc(x_57);
lean_dec(x_48);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_array_mk(x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_4, 0);
lean_inc(x_62);
lean_dec(x_4);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_66 = l_Lake_resolveCustomTarget(x_64, x_2, x_3, x_65);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
lean_free_object(x_62);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
return x_66;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 0);
x_72 = lean_box(0);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 1, x_72);
lean_ctor_set(x_62, 0, x_71);
x_73 = lean_array_mk(x_62);
lean_ctor_set(x_66, 0, x_73);
return x_66;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
lean_dec(x_66);
x_75 = lean_box(0);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 1, x_75);
lean_ctor_set(x_62, 0, x_74);
x_76 = lean_array_mk(x_62);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_62, 0);
x_79 = lean_ctor_get(x_62, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_62);
x_80 = l_Lake_resolveCustomTarget(x_78, x_2, x_3, x_79);
lean_dec(x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_85 = x_80;
} else {
 lean_dec_ref(x_80);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_array_mk(x_87);
if (lean_is_scalar(x_85)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_85;
}
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveTargetInWorkspace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_resolveTargetInWorkspace(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_resolveTargetBaseSpec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveTargetBaseSpec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_resolveTargetBaseSpec___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_resolveTargetBaseSpec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_resolveTargetBaseSpec___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_resolveTargetBaseSpec___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_resolveTargetBaseSpec___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_resolveTargetBaseSpec___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_resolveTargetBaseSpec___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("+", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveTargetBaseSpec___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_resolveTargetBaseSpec___closed__5;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_resolveTargetBaseSpec___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_resolveTargetBaseSpec___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_resolveTargetBaseSpec___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_resolveTargetBaseSpec___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_resolveTargetBaseSpec___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_resolveTargetBaseSpec___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveTargetBaseSpec___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static uint8_t _init_l_Lake_resolveTargetBaseSpec___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_resolveTargetBaseSpec___closed__9;
x_2 = l_Lake_resolveTargetBaseSpec___closed__10;
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_resolveTargetBaseSpec___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveTargetBaseSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_160; 
x_160 = l_Lake_resolveTargetBaseSpec___closed__11;
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_box(0);
x_162 = l_Lake_resolveTargetBaseSpec___closed__9;
x_163 = lean_unsigned_to_nat(0u);
x_164 = l_String_splitOnAux(x_2, x_162, x_163, x_163, x_163, x_161);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_3);
lean_dec(x_1);
x_165 = l_Lake_resolveTargetBaseSpec___boxed__const__1;
x_166 = lean_alloc_ctor(18, 2, 0);
lean_ctor_set(x_166, 0, x_2);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_164, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
lean_dec(x_164);
x_4 = x_168;
x_5 = x_169;
goto block_159;
}
}
else
{
lean_object* x_170; 
x_170 = lean_box(0);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_170;
goto block_159;
}
block_159:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_2);
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_6);
lean_inc(x_4);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_6);
x_10 = l_Lake_resolveTargetBaseSpec___closed__2;
x_11 = l_Substring_nextn(x_9, x_10, x_7);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_11);
lean_inc(x_4);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_12);
x_14 = l_Lake_resolveTargetBaseSpec___closed__4;
x_15 = l_Substring_beq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = l_Lake_resolveTargetBaseSpec___closed__6;
x_17 = l_Substring_nextn(x_9, x_16, x_7);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_17);
lean_inc(x_4);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_Lake_resolveTargetBaseSpec___closed__8;
x_21 = l_Substring_beq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_6);
x_22 = l_Lake_stringToLegalOrSimpleName(x_4);
x_23 = l_Lake_resolveTargetInWorkspace(x_1, x_22, x_3);
lean_dec(x_1);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Substring_nextn(x_9, x_24, x_7);
lean_dec(x_9);
x_26 = lean_nat_add(x_7, x_25);
lean_dec(x_25);
x_27 = lean_string_utf8_extract(x_4, x_26, x_6);
lean_dec(x_6);
lean_dec(x_26);
lean_dec(x_4);
x_28 = l_String_toName(x_27);
lean_inc(x_28);
x_29 = l_Lake_Workspace_findTargetModule_x3f(x_28, x_1);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Lake_resolveModuleTarget(x_1, x_32, x_3);
lean_dec(x_1);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_array_mk(x_40);
lean_ctor_set(x_33, 0, x_41);
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_mk(x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = l_Substring_nextn(x_9, x_47, x_7);
lean_dec(x_9);
x_49 = lean_nat_add(x_7, x_48);
lean_dec(x_48);
x_50 = lean_string_utf8_extract(x_4, x_49, x_6);
lean_dec(x_6);
lean_dec(x_49);
lean_dec(x_4);
x_51 = l_Lake_parsePackageSpec(x_1, x_50);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
lean_dec(x_51);
x_56 = l_Lake_resolvePackageTarget(x_1, x_55, x_3);
lean_dec(x_1);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_6);
lean_dec(x_4);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = l_Lake_resolvePackageTarget(x_1, x_57, x_3);
lean_dec(x_1);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_5, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_5, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_61 = x_5;
} else {
 lean_dec_ref(x_5);
 x_61 = lean_box(0);
}
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_dec(x_2);
x_138 = lean_string_utf8_byte_size(x_4);
x_139 = lean_unsigned_to_nat(0u);
lean_inc(x_138);
lean_inc(x_4);
x_140 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_140, 0, x_4);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_140, 2, x_138);
x_141 = l_Lake_resolveTargetBaseSpec___closed__2;
x_142 = l_Substring_nextn(x_140, x_141, x_139);
x_143 = lean_nat_add(x_139, x_142);
lean_dec(x_142);
lean_inc(x_4);
x_144 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_144, 0, x_4);
lean_ctor_set(x_144, 1, x_139);
lean_ctor_set(x_144, 2, x_143);
x_145 = l_Lake_resolveTargetBaseSpec___closed__4;
x_146 = l_Substring_beq(x_144, x_145);
if (x_146 == 0)
{
lean_dec(x_140);
lean_dec(x_138);
x_62 = x_4;
goto block_137;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_unsigned_to_nat(1u);
x_148 = l_Substring_nextn(x_140, x_147, x_139);
lean_dec(x_140);
x_149 = lean_nat_add(x_139, x_148);
lean_dec(x_148);
x_150 = lean_string_utf8_extract(x_4, x_149, x_138);
lean_dec(x_138);
lean_dec(x_149);
lean_dec(x_4);
x_62 = x_150;
goto block_137;
}
}
else
{
uint8_t x_151; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_60);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_60, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_60, 0);
lean_dec(x_153);
x_154 = l_Lake_resolveTargetBaseSpec___boxed__const__1;
lean_ctor_set_tag(x_60, 18);
lean_ctor_set(x_60, 1, x_154);
lean_ctor_set(x_60, 0, x_2);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_60);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_60);
x_156 = l_Lake_resolveTargetBaseSpec___boxed__const__1;
x_157 = lean_alloc_ctor(18, 2, 0);
lean_ctor_set(x_157, 0, x_2);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
block_137:
{
lean_object* x_63; 
x_63 = l_Lake_parsePackageSpec(x_1, x_62);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_3);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
return x_63;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_63, 0);
x_69 = lean_string_utf8_byte_size(x_59);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_inc(x_69);
lean_inc(x_59);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_59);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_72, 2, x_69);
x_73 = l_Lake_resolveTargetBaseSpec___closed__6;
x_74 = l_Substring_nextn(x_72, x_73, x_70);
x_75 = lean_nat_add(x_70, x_74);
lean_dec(x_74);
lean_inc(x_59);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_59);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_76, 2, x_75);
x_77 = l_Lake_resolveTargetBaseSpec___closed__8;
x_78 = l_Substring_beq(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_72);
lean_dec(x_69);
lean_free_object(x_63);
lean_dec(x_61);
x_79 = l_Lake_stringToLegalOrSimpleName(x_59);
x_80 = l_Lake_resolveTargetInPackage(x_1, x_68, x_79, x_3);
lean_dec(x_1);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_unsigned_to_nat(1u);
x_82 = l_Substring_nextn(x_72, x_81, x_70);
lean_dec(x_72);
x_83 = lean_nat_add(x_70, x_82);
lean_dec(x_82);
x_84 = lean_string_utf8_extract(x_59, x_83, x_69);
lean_dec(x_69);
lean_dec(x_83);
lean_dec(x_59);
x_85 = l_String_toName(x_84);
lean_inc(x_85);
x_86 = l_Lake_Package_findTargetModule_x3f(x_85, x_68);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
lean_dec(x_61);
lean_dec(x_3);
lean_dec(x_1);
x_87 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_tag(x_63, 0);
lean_ctor_set(x_63, 0, x_87);
return x_63;
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_85);
lean_free_object(x_63);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lake_resolveModuleTarget(x_1, x_88, x_3);
lean_dec(x_1);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
lean_dec(x_61);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
else
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_89);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 0);
x_95 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_61;
}
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_array_mk(x_96);
lean_ctor_set(x_89, 0, x_97);
return x_89;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_89, 0);
lean_inc(x_98);
lean_dec(x_89);
x_99 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_61;
}
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_array_mk(x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
}
}
else
{
lean_object* x_103; 
lean_dec(x_69);
lean_free_object(x_63);
lean_dec(x_61);
lean_dec(x_59);
x_103 = l_Lake_resolvePackageTarget(x_1, x_68, x_3);
lean_dec(x_1);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_63, 0);
lean_inc(x_104);
lean_dec(x_63);
x_105 = lean_string_utf8_byte_size(x_59);
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_nat_dec_eq(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_inc(x_105);
lean_inc(x_59);
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_59);
lean_ctor_set(x_108, 1, x_106);
lean_ctor_set(x_108, 2, x_105);
x_109 = l_Lake_resolveTargetBaseSpec___closed__6;
x_110 = l_Substring_nextn(x_108, x_109, x_106);
x_111 = lean_nat_add(x_106, x_110);
lean_dec(x_110);
lean_inc(x_59);
x_112 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_112, 0, x_59);
lean_ctor_set(x_112, 1, x_106);
lean_ctor_set(x_112, 2, x_111);
x_113 = l_Lake_resolveTargetBaseSpec___closed__8;
x_114 = l_Substring_beq(x_112, x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_108);
lean_dec(x_105);
lean_dec(x_61);
x_115 = l_Lake_stringToLegalOrSimpleName(x_59);
x_116 = l_Lake_resolveTargetInPackage(x_1, x_104, x_115, x_3);
lean_dec(x_1);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_unsigned_to_nat(1u);
x_118 = l_Substring_nextn(x_108, x_117, x_106);
lean_dec(x_108);
x_119 = lean_nat_add(x_106, x_118);
lean_dec(x_118);
x_120 = lean_string_utf8_extract(x_59, x_119, x_105);
lean_dec(x_105);
lean_dec(x_119);
lean_dec(x_59);
x_121 = l_String_toName(x_120);
lean_inc(x_121);
x_122 = l_Lake_Package_findTargetModule_x3f(x_121, x_104);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_61);
lean_dec(x_3);
lean_dec(x_1);
x_123 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_123, 0, x_121);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_121);
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
lean_dec(x_122);
x_126 = l_Lake_resolveModuleTarget(x_1, x_125, x_3);
lean_dec(x_1);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_61);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 1, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_127);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_126, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 x_131 = x_126;
} else {
 lean_dec_ref(x_126);
 x_131 = lean_box(0);
}
x_132 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_61;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_array_mk(x_133);
if (lean_is_scalar(x_131)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_131;
}
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
}
else
{
lean_object* x_136; 
lean_dec(x_105);
lean_dec(x_61);
lean_dec(x_59);
x_136 = l_Lake_resolvePackageTarget(x_1, x_104, x_3);
lean_dec(x_1);
return x_136;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lake_parseExeTargetSpec___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_124; 
x_124 = l_Lake_resolveTargetBaseSpec___closed__11;
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_box(0);
x_126 = l_Lake_resolveTargetBaseSpec___closed__9;
x_127 = lean_unsigned_to_nat(0u);
x_128 = l_String_splitOnAux(x_2, x_126, x_127, x_127, x_127, x_125);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = l_Lake_parseExeTargetSpec___boxed__const__1;
x_130 = lean_alloc_ctor(18, 2, 0);
lean_ctor_set(x_130, 0, x_2);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_128, 1);
lean_inc(x_133);
lean_dec(x_128);
x_3 = x_132;
x_4 = x_133;
goto block_123;
}
}
else
{
lean_object* x_134; 
x_134 = lean_box(0);
lean_inc(x_2);
x_3 = x_2;
x_4 = x_134;
goto block_123;
}
block_123:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lake_stringToLegalOrSimpleName(x_3);
x_6 = l_Lake_Workspace_findLeanExe_x3f(x_5, x_1);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_dec(x_15);
x_16 = lean_string_utf8_byte_size(x_3);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
lean_inc(x_3);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_16);
x_19 = l_Lake_resolveTargetBaseSpec___closed__2;
x_20 = l_Substring_nextn(x_18, x_19, x_17);
x_21 = lean_nat_add(x_17, x_20);
lean_dec(x_20);
lean_inc(x_3);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_21);
x_23 = l_Lake_resolveTargetBaseSpec___closed__4;
x_24 = l_Substring_beq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_16);
x_25 = l_Lake_parsePackageSpec(x_1, x_3);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_2);
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
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = l_Lake_stringToLegalOrSimpleName(x_14);
x_32 = lean_ctor_get(x_30, 9);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_33, x_31);
lean_dec(x_31);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_30);
lean_free_object(x_4);
x_35 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_35);
return x_25;
}
else
{
lean_object* x_36; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_36);
lean_ctor_set(x_4, 0, x_30);
lean_ctor_set(x_25, 0, x_4);
return x_25;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_25, 0);
lean_inc(x_37);
lean_dec(x_25);
x_38 = l_Lake_stringToLegalOrSimpleName(x_14);
x_39 = lean_ctor_get(x_37, 9);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_40, x_38);
lean_dec(x_38);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_37);
lean_free_object(x_4);
x_42 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_42, 0, x_2);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_44);
lean_ctor_set(x_4, 0, x_37);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_4);
return x_45;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = l_Substring_nextn(x_18, x_46, x_17);
lean_dec(x_18);
x_48 = lean_nat_add(x_17, x_47);
lean_dec(x_47);
x_49 = lean_string_utf8_extract(x_3, x_48, x_16);
lean_dec(x_16);
lean_dec(x_48);
lean_dec(x_3);
x_50 = l_Lake_parsePackageSpec(x_1, x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_50, 0);
x_56 = l_Lake_stringToLegalOrSimpleName(x_14);
x_57 = lean_ctor_get(x_55, 9);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_58, x_56);
lean_dec(x_56);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
lean_dec(x_55);
lean_free_object(x_4);
x_60 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_60, 0, x_2);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 0, x_60);
return x_50;
}
else
{
lean_object* x_61; 
lean_dec(x_2);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_61);
lean_ctor_set(x_4, 0, x_55);
lean_ctor_set(x_50, 0, x_4);
return x_50;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_50, 0);
lean_inc(x_62);
lean_dec(x_50);
x_63 = l_Lake_stringToLegalOrSimpleName(x_14);
x_64 = lean_ctor_get(x_62, 9);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_65, x_63);
lean_dec(x_63);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_62);
lean_free_object(x_4);
x_67 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_67, 0, x_2);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_2);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_69);
lean_ctor_set(x_4, 0, x_62);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_4);
return x_70;
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_71 = lean_ctor_get(x_4, 0);
lean_inc(x_71);
lean_dec(x_4);
x_72 = lean_string_utf8_byte_size(x_3);
x_73 = lean_unsigned_to_nat(0u);
lean_inc(x_72);
lean_inc(x_3);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_3);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_72);
x_75 = l_Lake_resolveTargetBaseSpec___closed__2;
x_76 = l_Substring_nextn(x_74, x_75, x_73);
x_77 = lean_nat_add(x_73, x_76);
lean_dec(x_76);
lean_inc(x_3);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_3);
lean_ctor_set(x_78, 1, x_73);
lean_ctor_set(x_78, 2, x_77);
x_79 = l_Lake_resolveTargetBaseSpec___closed__4;
x_80 = l_Substring_beq(x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_74);
lean_dec(x_72);
x_81 = l_Lake_parsePackageSpec(x_1, x_3);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_71);
lean_dec(x_2);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 1, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_86 = x_81;
} else {
 lean_dec_ref(x_81);
 x_86 = lean_box(0);
}
x_87 = l_Lake_stringToLegalOrSimpleName(x_71);
x_88 = lean_ctor_get(x_85, 9);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_89, x_87);
lean_dec(x_87);
lean_dec(x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_85);
x_91 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_91, 0, x_2);
if (lean_is_scalar(x_86)) {
 x_92 = lean_alloc_ctor(0, 1, 0);
} else {
 x_92 = x_86;
 lean_ctor_set_tag(x_92, 0);
}
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_2);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_85);
lean_ctor_set(x_94, 1, x_93);
if (lean_is_scalar(x_86)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_86;
}
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_unsigned_to_nat(1u);
x_97 = l_Substring_nextn(x_74, x_96, x_73);
lean_dec(x_74);
x_98 = lean_nat_add(x_73, x_97);
lean_dec(x_97);
x_99 = lean_string_utf8_extract(x_3, x_98, x_72);
lean_dec(x_72);
lean_dec(x_98);
lean_dec(x_3);
x_100 = l_Lake_parsePackageSpec(x_1, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_71);
lean_dec(x_2);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 1, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_101);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_100, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_105 = x_100;
} else {
 lean_dec_ref(x_100);
 x_105 = lean_box(0);
}
x_106 = l_Lake_stringToLegalOrSimpleName(x_71);
x_107 = lean_ctor_get(x_104, 9);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
x_109 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_108, x_106);
lean_dec(x_106);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_104);
x_110 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_110, 0, x_2);
if (lean_is_scalar(x_105)) {
 x_111 = lean_alloc_ctor(0, 1, 0);
} else {
 x_111 = x_105;
 lean_ctor_set_tag(x_111, 0);
}
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_2);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
lean_dec(x_109);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_104);
lean_ctor_set(x_113, 1, x_112);
if (lean_is_scalar(x_105)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_105;
}
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_4);
lean_dec(x_3);
x_115 = !lean_is_exclusive(x_12);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_12, 1);
lean_dec(x_116);
x_117 = lean_ctor_get(x_12, 0);
lean_dec(x_117);
x_118 = l_Lake_parseExeTargetSpec___boxed__const__1;
lean_ctor_set_tag(x_12, 18);
lean_ctor_set(x_12, 1, x_118);
lean_ctor_set(x_12, 0, x_2);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_12);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_12);
x_120 = l_Lake_parseExeTargetSpec___boxed__const__1;
x_121 = lean_alloc_ctor(18, 2, 0);
lean_ctor_set(x_121, 0, x_2);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_parseExeTargetSpec(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_parseTargetSpec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static uint8_t _init_l_Lake_parseTargetSpec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_parseTargetSpec___closed__1;
x_2 = l_Lake_resolveTargetBaseSpec___closed__10;
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_parseTargetSpec___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 58;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lake_parseTargetSpec___closed__2;
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = l_Lake_parseTargetSpec___closed__1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_String_splitOnAux(x_2, x_5, x_6, x_6, x_6, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_8 = l_Lake_parseTargetSpec___boxed__const__1;
x_9 = lean_alloc_ctor(18, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = l_Lake_resolveTargetBaseSpec(x_1, x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = l_String_toName(x_17);
x_19 = l_Lake_resolveTargetBaseSpec(x_1, x_16, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
x_23 = l_Lake_parseTargetSpec___boxed__const__1;
lean_ctor_set_tag(x_15, 18);
lean_ctor_set(x_15, 1, x_23);
lean_ctor_set(x_15, 0, x_2);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
x_25 = l_Lake_parseTargetSpec___boxed__const__1;
x_26 = lean_alloc_ctor(18, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lake_resolveTargetBaseSpec(x_1, x_2, x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lake_parseTargetSpecs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
lean_inc(x_1);
x_11 = l_Lake_parseTargetSpec(x_1, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Array_append___rarg(x_6, x_15);
lean_dec(x_15);
x_5 = x_10;
x_6 = x_16;
x_7 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_parseTargetSpecs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_parseTargetSpecs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_parseTargetSpecs___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Lake_parseTargetSpecs___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_List_forIn_x27_loop___at_Lake_parseTargetSpecs___spec__1(x_1, x_2, x_3, x_2, x_2, x_4, lean_box(0));
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Lake_parseTargetSpecs___closed__2;
x_11 = l_Array_isEmpty___rarg(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_10, x_9, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = l_Lake_resolveDefaultPackageTarget(x_1, x_14);
lean_dec(x_1);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_10, x_19, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lake_parseTargetSpecs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at_Lake_parseTargetSpecs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_parseTargetSpecs___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Lake_Config_Monad(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Error(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Build(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Error(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_resolveModuleTarget___closed__1 = _init_l_Lake_resolveModuleTarget___closed__1();
lean_mark_persistent(l_Lake_resolveModuleTarget___closed__1);
l_Lake_resolveModuleTarget___closed__2 = _init_l_Lake_resolveModuleTarget___closed__2();
lean_mark_persistent(l_Lake_resolveModuleTarget___closed__2);
l_Lake_resolveModuleTarget___closed__3 = _init_l_Lake_resolveModuleTarget___closed__3();
lean_mark_persistent(l_Lake_resolveModuleTarget___closed__3);
l_Lake_resolveModuleTarget___closed__4 = _init_l_Lake_resolveModuleTarget___closed__4();
lean_mark_persistent(l_Lake_resolveModuleTarget___closed__4);
l_Lake_resolveLibTarget_resolveFacet___closed__1 = _init_l_Lake_resolveLibTarget_resolveFacet___closed__1();
lean_mark_persistent(l_Lake_resolveLibTarget_resolveFacet___closed__1);
l_Lake_resolveExeTarget___closed__1 = _init_l_Lake_resolveExeTarget___closed__1();
lean_mark_persistent(l_Lake_resolveExeTarget___closed__1);
l_Lake_resolveExeTarget___closed__2 = _init_l_Lake_resolveExeTarget___closed__2();
lean_mark_persistent(l_Lake_resolveExeTarget___closed__2);
l_Lake_resolveExeTarget___closed__3 = _init_l_Lake_resolveExeTarget___closed__3();
lean_mark_persistent(l_Lake_resolveExeTarget___closed__3);
l_Lake_resolveExeTarget___closed__4 = _init_l_Lake_resolveExeTarget___closed__4();
lean_mark_persistent(l_Lake_resolveExeTarget___closed__4);
l_Lake_resolveExternLibTarget___closed__1 = _init_l_Lake_resolveExternLibTarget___closed__1();
lean_mark_persistent(l_Lake_resolveExternLibTarget___closed__1);
l_Lake_resolveExternLibTarget___closed__2 = _init_l_Lake_resolveExternLibTarget___closed__2();
lean_mark_persistent(l_Lake_resolveExternLibTarget___closed__2);
l_Lake_resolveExternLibTarget___closed__3 = _init_l_Lake_resolveExternLibTarget___closed__3();
lean_mark_persistent(l_Lake_resolveExternLibTarget___closed__3);
l_Lake_resolveExternLibTarget___closed__4 = _init_l_Lake_resolveExternLibTarget___closed__4();
lean_mark_persistent(l_Lake_resolveExternLibTarget___closed__4);
l_Lake_resolveExternLibTarget___closed__5 = _init_l_Lake_resolveExternLibTarget___closed__5();
lean_mark_persistent(l_Lake_resolveExternLibTarget___closed__5);
l_Lake_resolveTargetInPackage___closed__1 = _init_l_Lake_resolveTargetInPackage___closed__1();
lean_mark_persistent(l_Lake_resolveTargetInPackage___closed__1);
l_Lake_resolveDefaultPackageTarget___closed__1 = _init_l_Lake_resolveDefaultPackageTarget___closed__1();
lean_mark_persistent(l_Lake_resolveDefaultPackageTarget___closed__1);
l_Lake_resolveDefaultPackageTarget___closed__2 = _init_l_Lake_resolveDefaultPackageTarget___closed__2();
lean_mark_persistent(l_Lake_resolveDefaultPackageTarget___closed__2);
l_Lake_resolvePackageTarget___closed__1 = _init_l_Lake_resolvePackageTarget___closed__1();
lean_mark_persistent(l_Lake_resolvePackageTarget___closed__1);
l_Lake_resolveTargetBaseSpec___closed__1 = _init_l_Lake_resolveTargetBaseSpec___closed__1();
lean_mark_persistent(l_Lake_resolveTargetBaseSpec___closed__1);
l_Lake_resolveTargetBaseSpec___closed__2 = _init_l_Lake_resolveTargetBaseSpec___closed__2();
lean_mark_persistent(l_Lake_resolveTargetBaseSpec___closed__2);
l_Lake_resolveTargetBaseSpec___closed__3 = _init_l_Lake_resolveTargetBaseSpec___closed__3();
lean_mark_persistent(l_Lake_resolveTargetBaseSpec___closed__3);
l_Lake_resolveTargetBaseSpec___closed__4 = _init_l_Lake_resolveTargetBaseSpec___closed__4();
lean_mark_persistent(l_Lake_resolveTargetBaseSpec___closed__4);
l_Lake_resolveTargetBaseSpec___closed__5 = _init_l_Lake_resolveTargetBaseSpec___closed__5();
lean_mark_persistent(l_Lake_resolveTargetBaseSpec___closed__5);
l_Lake_resolveTargetBaseSpec___closed__6 = _init_l_Lake_resolveTargetBaseSpec___closed__6();
lean_mark_persistent(l_Lake_resolveTargetBaseSpec___closed__6);
l_Lake_resolveTargetBaseSpec___closed__7 = _init_l_Lake_resolveTargetBaseSpec___closed__7();
lean_mark_persistent(l_Lake_resolveTargetBaseSpec___closed__7);
l_Lake_resolveTargetBaseSpec___closed__8 = _init_l_Lake_resolveTargetBaseSpec___closed__8();
lean_mark_persistent(l_Lake_resolveTargetBaseSpec___closed__8);
l_Lake_resolveTargetBaseSpec___closed__9 = _init_l_Lake_resolveTargetBaseSpec___closed__9();
lean_mark_persistent(l_Lake_resolveTargetBaseSpec___closed__9);
l_Lake_resolveTargetBaseSpec___closed__10 = _init_l_Lake_resolveTargetBaseSpec___closed__10();
lean_mark_persistent(l_Lake_resolveTargetBaseSpec___closed__10);
l_Lake_resolveTargetBaseSpec___closed__11 = _init_l_Lake_resolveTargetBaseSpec___closed__11();
l_Lake_resolveTargetBaseSpec___boxed__const__1 = _init_l_Lake_resolveTargetBaseSpec___boxed__const__1();
lean_mark_persistent(l_Lake_resolveTargetBaseSpec___boxed__const__1);
l_Lake_parseExeTargetSpec___boxed__const__1 = _init_l_Lake_parseExeTargetSpec___boxed__const__1();
lean_mark_persistent(l_Lake_parseExeTargetSpec___boxed__const__1);
l_Lake_parseTargetSpec___closed__1 = _init_l_Lake_parseTargetSpec___closed__1();
lean_mark_persistent(l_Lake_parseTargetSpec___closed__1);
l_Lake_parseTargetSpec___closed__2 = _init_l_Lake_parseTargetSpec___closed__2();
l_Lake_parseTargetSpec___boxed__const__1 = _init_l_Lake_parseTargetSpec___boxed__const__1();
lean_mark_persistent(l_Lake_parseTargetSpec___boxed__const__1);
l_Lake_parseTargetSpecs___closed__1 = _init_l_Lake_parseTargetSpecs___closed__1();
lean_mark_persistent(l_Lake_parseTargetSpecs___closed__1);
l_Lake_parseTargetSpecs___closed__2 = _init_l_Lake_parseTargetSpecs___closed__2();
lean_mark_persistent(l_Lake_parseTargetSpecs___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
