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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lake_parseTargetSpecs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_BuildInfo_key(lean_object*);
static lean_object* l_Lake_resolveExternLibTarget___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveConfigDeclTarget___lambda__1___boxed(lean_object*);
extern lean_object* l_Lake_ExternLib_sharedFacet;
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
static lean_object* l_Lake_resolveExeTarget___closed__2;
extern lean_object* l_Lake_Package_keyword;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_resolveLibTarget___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bind_bindLeft___at_Lake_BuildSpec_query___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___rarg(lean_object*);
static lean_object* l_Lake_resolveExeTarget___closed__4;
LEAN_EXPORT lean_object* l_Lake_resolveConfigDeclTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveExeTarget(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_resolveTargetBaseSpec___closed__9;
LEAN_EXPORT lean_object* l_Lake_querySpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveDefaultPackageTarget___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_resolveLibTarget_resolveFacet___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveModuleTarget(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_exeFacet;
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
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_buildSpecs___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolveExternLibTarget___closed__2;
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_mkBuildSpec(lean_object*);
lean_object* l_Lake_nullFormat___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lake_Module_leanArtsFacet;
lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolveConfigDeclTarget___closed__2;
LEAN_EXPORT lean_object* l_Lake_mkBuildSpec___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_resolveLibTarget___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveConfigDeclTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolvePackageTarget___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolvePackageTarget___closed__1;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_BuildSpec_query___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildKey_toSimpleString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_BuildSpec_query___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_parseTargetSpecs___closed__2;
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
static lean_object* l_Lake_resolveConfigDeclTarget___closed__1;
LEAN_EXPORT uint8_t l_Lake_resolveConfigDeclTarget___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveCustomTarget(lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_resolveTargetBaseSpec___closed__11;
lean_object* l_Lake_EResult_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveModuleTarget___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_querySpecs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_resolveExeTarget___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_resolveTargetBaseSpec___closed__3;
static lean_object* l_Lake_resolveModuleTarget___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_resolveDefaultPackageTarget___closed__1;
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_resolveDefaultPackageTarget___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_resolveTargetBaseSpec___closed__2;
lean_object* l_String_toName(lean_object*);
static lean_object* l_Lake_resolveTargetBaseSpec___closed__1;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_staticFacet;
static lean_object* l_Lake_resolveExeTarget___closed__1;
uint8_t l_Substring_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_resolveTargetInWorkspace___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveTargetInPackage___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolveLibTarget_resolveFacet___closed__2;
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
extern lean_object* l_Lake_LeanExe_keyword;
static lean_object* l_Lake_resolveDefaultPackageTarget___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveTargetInWorkspace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget_resolveFacet(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_maybeRegisterJob___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveTargetInPackage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
static lean_object* l_Lake_resolveLibTarget_resolveFacet___closed__3;
static lean_object* l_Lake_resolveConfigDeclTarget___closed__3;
lean_object* l_Array_emptyWithCapacity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget_resolveFacet___boxed(lean_object*, lean_object*, lean_object*);
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
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_mkConfigBuildSpec___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_mkConfigBuildSpec___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_mkConfigBuildSpec(x_1);
lean_dec(x_1);
return x_2;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = l_Lake_BuildInfo_key(x_8);
x_17 = l_Lake_BuildKey_toSimpleString(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_20);
x_21 = lean_string_utf8_byte_size(x_20);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_5);
return x_9;
}
else
{
uint8_t x_24; 
lean_free_object(x_9);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_25 = lean_ctor_get(x_15, 2);
lean_dec(x_25);
x_26 = lean_ctor_get(x_15, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_15, 0);
lean_dec(x_27);
x_28 = 0;
lean_ctor_set(x_15, 2, x_17);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_28);
x_29 = lean_ctor_get(x_5, 3);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_st_ref_take(x_29, x_12);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_15);
x_33 = l_Lake_Job_toOpaque___rarg(x_15);
x_34 = lean_array_push(x_31, x_33);
x_35 = lean_st_ref_set(x_29, x_34, x_32);
lean_dec(x_29);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = l_Lake_Job_renew___rarg(x_15);
lean_ctor_set(x_10, 0, x_38);
lean_ctor_set(x_35, 0, x_10);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = l_Lake_Job_renew___rarg(x_15);
lean_ctor_set(x_10, 0, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_15);
x_42 = 0;
x_43 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_43, 0, x_18);
lean_ctor_set(x_43, 1, x_19);
lean_ctor_set(x_43, 2, x_17);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_42);
x_44 = lean_ctor_get(x_5, 3);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_st_ref_take(x_44, x_12);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_43);
x_48 = l_Lake_Job_toOpaque___rarg(x_43);
x_49 = lean_array_push(x_46, x_48);
x_50 = lean_st_ref_set(x_44, x_49, x_47);
lean_dec(x_44);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = l_Lake_Job_renew___rarg(x_43);
lean_ctor_set(x_10, 0, x_53);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_10);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_55 = lean_ctor_get(x_10, 0);
x_56 = lean_ctor_get(x_10, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_10);
x_57 = l_Lake_BuildInfo_key(x_8);
x_58 = l_Lake_BuildKey_toSimpleString(x_57);
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 2);
lean_inc(x_61);
x_62 = lean_string_utf8_byte_size(x_61);
lean_dec(x_61);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_nat_dec_eq(x_62, x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_5);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_56);
lean_ctor_set(x_9, 0, x_65);
return x_9;
}
else
{
lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_free_object(x_9);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 x_66 = x_55;
} else {
 lean_dec_ref(x_55);
 x_66 = lean_box(0);
}
x_67 = 0;
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 3, 1);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_60);
lean_ctor_set(x_68, 2, x_58);
lean_ctor_set_uint8(x_68, sizeof(void*)*3, x_67);
x_69 = lean_ctor_get(x_5, 3);
lean_inc(x_69);
lean_dec(x_5);
x_70 = lean_st_ref_take(x_69, x_12);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_68);
x_73 = l_Lake_Job_toOpaque___rarg(x_68);
x_74 = lean_array_push(x_71, x_73);
x_75 = lean_st_ref_set(x_69, x_74, x_72);
lean_dec(x_69);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = l_Lake_Job_renew___rarg(x_68);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_56);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_81 = lean_ctor_get(x_9, 1);
lean_inc(x_81);
lean_dec(x_9);
x_82 = lean_ctor_get(x_10, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_10, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_84 = x_10;
} else {
 lean_dec_ref(x_10);
 x_84 = lean_box(0);
}
x_85 = l_Lake_BuildInfo_key(x_8);
x_86 = l_Lake_BuildKey_toSimpleString(x_85);
x_87 = lean_ctor_get(x_82, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 2);
lean_inc(x_89);
x_90 = lean_string_utf8_byte_size(x_89);
lean_dec(x_89);
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_nat_dec_eq(x_90, x_91);
lean_dec(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_5);
if (lean_is_scalar(x_84)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_84;
}
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_83);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_81);
return x_94;
}
else
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 x_95 = x_82;
} else {
 lean_dec_ref(x_82);
 x_95 = lean_box(0);
}
x_96 = 0;
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 3, 1);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_88);
lean_ctor_set(x_97, 2, x_86);
lean_ctor_set_uint8(x_97, sizeof(void*)*3, x_96);
x_98 = lean_ctor_get(x_5, 3);
lean_inc(x_98);
lean_dec(x_5);
x_99 = lean_st_ref_take(x_98, x_81);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_97);
x_102 = l_Lake_Job_toOpaque___rarg(x_97);
x_103 = lean_array_push(x_100, x_102);
x_104 = lean_st_ref_set(x_98, x_103, x_101);
lean_dec(x_98);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_107 = l_Lake_Job_renew___rarg(x_97);
if (lean_is_scalar(x_84)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_84;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_83);
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_106;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_105);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_8);
lean_dec(x_5);
x_110 = !lean_is_exclusive(x_9);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_9, 0);
lean_dec(x_111);
x_112 = !lean_is_exclusive(x_10);
if (x_112 == 0)
{
return x_9;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_10, 0);
x_114 = lean_ctor_get(x_10, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_10);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_9, 0, x_115);
return x_9;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_ctor_get(x_9, 1);
lean_inc(x_116);
lean_dec(x_9);
x_117 = lean_ctor_get(x_10, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_10, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_119 = x_10;
} else {
 lean_dec_ref(x_10);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_116);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_8);
lean_dec(x_5);
x_122 = !lean_is_exclusive(x_9);
if (x_122 == 0)
{
return x_9;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_9, 0);
x_124 = lean_ctor_get(x_9, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_9);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_26);
x_27 = lean_apply_6(x_2, x_26, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = l_Lake_BuildInfo_key(x_26);
x_33 = l_Lake_BuildKey_toSimpleString(x_32);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 2);
lean_inc(x_36);
x_37 = lean_string_utf8_byte_size(x_36);
lean_dec(x_36);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_37, x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_5);
x_8 = x_28;
x_9 = x_29;
goto block_25;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_41 = lean_ctor_get(x_31, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_31, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_31, 0);
lean_dec(x_43);
x_44 = 0;
lean_ctor_set(x_31, 2, x_33);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_44);
x_45 = lean_ctor_get(x_5, 3);
lean_inc(x_45);
lean_dec(x_5);
x_46 = lean_st_ref_take(x_45, x_29);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_31);
x_49 = l_Lake_Job_toOpaque___rarg(x_31);
x_50 = lean_array_push(x_47, x_49);
x_51 = lean_st_ref_set(x_45, x_50, x_48);
lean_dec(x_45);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lake_Job_renew___rarg(x_31);
lean_ctor_set(x_28, 0, x_53);
x_8 = x_28;
x_9 = x_52;
goto block_25;
}
else
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_31);
x_54 = 0;
x_55 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_55, 0, x_34);
lean_ctor_set(x_55, 1, x_35);
lean_ctor_set(x_55, 2, x_33);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_54);
x_56 = lean_ctor_get(x_5, 3);
lean_inc(x_56);
lean_dec(x_5);
x_57 = lean_st_ref_take(x_56, x_29);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_55);
x_60 = l_Lake_Job_toOpaque___rarg(x_55);
x_61 = lean_array_push(x_58, x_60);
x_62 = lean_st_ref_set(x_56, x_61, x_59);
lean_dec(x_56);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lake_Job_renew___rarg(x_55);
lean_ctor_set(x_28, 0, x_64);
x_8 = x_28;
x_9 = x_63;
goto block_25;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_65 = lean_ctor_get(x_28, 0);
x_66 = lean_ctor_get(x_28, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_28);
x_67 = l_Lake_BuildInfo_key(x_26);
x_68 = l_Lake_BuildKey_toSimpleString(x_67);
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 2);
lean_inc(x_71);
x_72 = lean_string_utf8_byte_size(x_71);
lean_dec(x_71);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_nat_dec_eq(x_72, x_73);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_5);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_66);
x_8 = x_75;
x_9 = x_29;
goto block_25;
}
else
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 x_76 = x_65;
} else {
 lean_dec_ref(x_65);
 x_76 = lean_box(0);
}
x_77 = 0;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 3, 1);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_68);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_77);
x_79 = lean_ctor_get(x_5, 3);
lean_inc(x_79);
lean_dec(x_5);
x_80 = lean_st_ref_take(x_79, x_29);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_78);
x_83 = l_Lake_Job_toOpaque___rarg(x_78);
x_84 = lean_array_push(x_81, x_83);
x_85 = lean_st_ref_set(x_79, x_84, x_82);
lean_dec(x_79);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lake_Job_renew___rarg(x_78);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_66);
x_8 = x_88;
x_9 = x_86;
goto block_25;
}
}
}
else
{
lean_object* x_89; uint8_t x_90; 
lean_dec(x_26);
lean_dec(x_5);
x_89 = lean_ctor_get(x_27, 1);
lean_inc(x_89);
lean_dec(x_27);
x_90 = !lean_is_exclusive(x_28);
if (x_90 == 0)
{
x_8 = x_28;
x_9 = x_89;
goto block_25;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_28, 0);
x_92 = lean_ctor_get(x_28, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_28);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_8 = x_93;
x_9 = x_89;
goto block_25;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_26);
lean_dec(x_5);
x_94 = !lean_is_exclusive(x_27);
if (x_94 == 0)
{
return x_27;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_27, 0);
x_96 = lean_ctor_get(x_27, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_27);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
block_25:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = l_Lake_Job_toOpaque___rarg(x_11);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = l_Lake_Job_toOpaque___rarg(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
return x_24;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_dec(x_16);
x_17 = l_Task_Priority_default;
x_18 = 0;
x_19 = lean_task_map(x_13, x_15, x_17, x_18);
x_20 = lean_box(0);
lean_ctor_set(x_3, 1, x_20);
lean_ctor_set(x_3, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_26 = l_Task_Priority_default;
x_27 = 0;
x_28 = lean_task_map(x_13, x_23, x_26, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_8);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_9);
return x_32;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_31; lean_object* x_32; lean_object* x_45; lean_object* x_46; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_45 = lean_ctor_get(x_13, 0);
lean_inc(x_45);
lean_dec(x_13);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_45);
x_46 = lean_apply_6(x_4, x_45, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_50 = lean_ctor_get(x_47, 0);
x_51 = l_Lake_BuildInfo_key(x_45);
x_52 = l_Lake_BuildKey_toSimpleString(x_51);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 2);
lean_inc(x_55);
x_56 = lean_string_utf8_byte_size(x_55);
lean_dec(x_55);
x_57 = lean_nat_dec_eq(x_56, x_14);
lean_dec(x_56);
if (x_57 == 0)
{
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_31 = x_47;
x_32 = x_48;
goto block_44;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_59 = lean_ctor_get(x_50, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_50, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_50, 0);
lean_dec(x_61);
x_62 = 0;
lean_ctor_set(x_50, 2, x_52);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_62);
x_63 = lean_ctor_get(x_7, 3);
lean_inc(x_63);
x_64 = lean_st_ref_take(x_63, x_48);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_50);
x_67 = l_Lake_Job_toOpaque___rarg(x_50);
x_68 = lean_array_push(x_65, x_67);
x_69 = lean_st_ref_set(x_63, x_68, x_66);
lean_dec(x_63);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lake_Job_renew___rarg(x_50);
lean_ctor_set(x_47, 0, x_71);
x_31 = x_47;
x_32 = x_70;
goto block_44;
}
else
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_50);
x_72 = 0;
x_73 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_73, 0, x_53);
lean_ctor_set(x_73, 1, x_54);
lean_ctor_set(x_73, 2, x_52);
lean_ctor_set_uint8(x_73, sizeof(void*)*3, x_72);
x_74 = lean_ctor_get(x_7, 3);
lean_inc(x_74);
x_75 = lean_st_ref_take(x_74, x_48);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_73);
x_78 = l_Lake_Job_toOpaque___rarg(x_73);
x_79 = lean_array_push(x_76, x_78);
x_80 = lean_st_ref_set(x_74, x_79, x_77);
lean_dec(x_74);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lake_Job_renew___rarg(x_73);
lean_ctor_set(x_47, 0, x_82);
x_31 = x_47;
x_32 = x_81;
goto block_44;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_83 = lean_ctor_get(x_47, 0);
x_84 = lean_ctor_get(x_47, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_47);
x_85 = l_Lake_BuildInfo_key(x_45);
x_86 = l_Lake_BuildKey_toSimpleString(x_85);
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 2);
lean_inc(x_89);
x_90 = lean_string_utf8_byte_size(x_89);
lean_dec(x_89);
x_91 = lean_nat_dec_eq(x_90, x_14);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_84);
x_31 = x_92;
x_32 = x_48;
goto block_44;
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 x_93 = x_83;
} else {
 lean_dec_ref(x_83);
 x_93 = lean_box(0);
}
x_94 = 0;
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 3, 1);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_87);
lean_ctor_set(x_95, 1, x_88);
lean_ctor_set(x_95, 2, x_86);
lean_ctor_set_uint8(x_95, sizeof(void*)*3, x_94);
x_96 = lean_ctor_get(x_7, 3);
lean_inc(x_96);
x_97 = lean_st_ref_take(x_96, x_48);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_95);
x_100 = l_Lake_Job_toOpaque___rarg(x_95);
x_101 = lean_array_push(x_98, x_100);
x_102 = lean_st_ref_set(x_96, x_101, x_99);
lean_dec(x_96);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_Lake_Job_renew___rarg(x_95);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_84);
x_31 = x_105;
x_32 = x_103;
goto block_44;
}
}
}
else
{
lean_object* x_106; uint8_t x_107; 
lean_dec(x_45);
x_106 = lean_ctor_get(x_46, 1);
lean_inc(x_106);
lean_dec(x_46);
x_107 = !lean_is_exclusive(x_47);
if (x_107 == 0)
{
x_31 = x_47;
x_32 = x_106;
goto block_44;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_47, 0);
x_109 = lean_ctor_get(x_47, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_47);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_31 = x_110;
x_32 = x_106;
goto block_44;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_45);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_111 = !lean_is_exclusive(x_46);
if (x_111 == 0)
{
return x_46;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_46, 0);
x_113 = lean_ctor_get(x_46, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_46);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
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
block_44:
{
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = l_Lake_Job_toOpaque___rarg(x_34);
lean_ctor_set(x_31, 0, x_35);
x_16 = x_31;
x_17 = x_32;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = l_Lake_Job_toOpaque___rarg(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_16 = x_39;
x_17 = x_32;
goto block_30;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
x_16 = x_31;
x_17 = x_32;
goto block_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_31);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_16 = x_43;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lake_Module_keyword;
x_6 = l_Lean_Name_append(x_5, x_3);
x_7 = l_Lake_Workspace_findModuleFacetConfig_x3f(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = l_Lake_resolveModuleTarget___closed__1;
x_9 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_13);
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_2);
lean_ctor_set(x_14, 3, x_6);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_16 = lean_ctor_get(x_12, 2);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 2, x_2);
lean_ctor_set(x_22, 3, x_6);
x_23 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_24 = lean_ctor_get(x_19, 2);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_3);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lake_Module_keyword;
x_30 = l_Lake_Module_leanArtsFacet;
x_31 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_2);
lean_ctor_set(x_31, 3, x_30);
x_32 = 1;
x_33 = l_Lake_resolveModuleTarget___closed__2;
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
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
x_8 = lean_alloc_ctor(0, 2, 0);
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
LEAN_EXPORT uint8_t l_Lake_resolveConfigDeclTarget___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lake_resolveConfigDeclTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_resolveConfigDeclTarget___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveConfigDeclTarget___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("default", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveConfigDeclTarget___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_resolveConfigDeclTarget___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveConfigDeclTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_59; 
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_59 = l_Lean_Name_isAnonymous(x_6);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_7);
lean_dec(x_3);
x_60 = l_Lean_Name_isAnonymous(x_5);
if (x_60 == 0)
{
x_8 = x_5;
goto block_58;
}
else
{
lean_object* x_61; 
lean_dec(x_5);
x_61 = l_Lake_resolveConfigDeclTarget___closed__3;
x_8 = x_61;
goto block_58;
}
}
else
{
lean_object* x_62; 
lean_dec(x_6);
lean_dec(x_4);
x_62 = l_Lake_resolveCustomTarget(x_2, x_3, x_5, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_62, 0);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_mk(x_69);
lean_ctor_set(x_62, 0, x_70);
return x_62;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_62, 0);
lean_inc(x_71);
lean_dec(x_62);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_array_mk(x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
block_58:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_6);
x_9 = l_Lean_Name_append(x_6, x_8);
x_10 = l_Lake_Workspace_findFacetConfig_x3f(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_11 = 1;
x_12 = l_Lake_resolveConfigDeclTarget___closed__1;
x_13 = l_Lean_Name_toString(x_6, x_11, x_12);
x_14 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_4, 3);
x_22 = lean_ctor_get(x_4, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
lean_inc(x_18);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 3, x_9);
lean_ctor_set(x_4, 2, x_25);
lean_ctor_set(x_4, 1, x_6);
lean_ctor_set(x_4, 0, x_26);
x_27 = lean_ctor_get_uint8(x_17, sizeof(void*)*3);
x_28 = lean_ctor_get(x_17, 2);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_27);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_mk(x_31);
lean_ctor_set(x_10, 0, x_32);
return x_10;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_4, 3);
lean_inc(x_33);
lean_dec(x_4);
lean_inc(x_18);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_18);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_18);
x_36 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_6);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_9);
x_37 = lean_ctor_get_uint8(x_17, sizeof(void*)*3);
x_38 = lean_ctor_get(x_17, 2);
lean_inc(x_38);
lean_dec(x_17);
x_39 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_37);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_mk(x_41);
lean_ctor_set(x_10, 0, x_42);
return x_10;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_43 = lean_ctor_get(x_10, 0);
lean_inc(x_43);
lean_dec(x_10);
x_44 = lean_ctor_get(x_4, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_4, 3);
lean_inc(x_46);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_47 = x_4;
} else {
 lean_dec_ref(x_4);
 x_47 = lean_box(0);
}
lean_inc(x_44);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_2);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_46);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_44);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(1, 4, 0);
} else {
 x_50 = x_47;
 lean_ctor_set_tag(x_50, 1);
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_6);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set(x_50, 3, x_9);
x_51 = lean_ctor_get_uint8(x_43, sizeof(void*)*3);
x_52 = lean_ctor_get(x_43, 2);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_51);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_array_mk(x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveConfigDeclTarget___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_resolveConfigDeclTarget___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveConfigDeclTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_resolveConfigDeclTarget(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
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
static lean_object* _init_l_Lake_resolveLibTarget_resolveFacet___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveLibTarget_resolveFacet___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_resolveLibTarget_resolveFacet___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
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
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lake_resolveLibTarget_resolveFacet___closed__3;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_2);
lean_ctor_set(x_15, 3, x_3);
x_16 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_17 = lean_ctor_get(x_10, 2);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_16);
lean_ctor_set(x_4, 0, x_18);
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lake_resolveLibTarget_resolveFacet___closed__3;
x_24 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_2);
lean_ctor_set(x_24, 3, x_3);
x_25 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_26 = lean_ctor_get(x_19, 2);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lake_resolveLibTarget_resolveFacet___closed__3;
x_6 = l_Lean_Name_append(x_5, x_3);
x_7 = l_Lake_resolveLibTarget_resolveFacet(x_1, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_mk(x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_mk(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
lean_dec(x_3);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 7);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_array_size(x_22);
x_24 = 0;
x_25 = l_Array_mapMUnsafe_map___at_Lake_resolveLibTarget___spec__1(x_1, x_2, x_23, x_24, x_22);
return x_25;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lake_LeanExe_keyword;
x_14 = l_Lake_LeanExe_exeFacet;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_14);
x_16 = 1;
x_17 = l_Lake_resolveExeTarget___closed__4;
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lake_LeanExe_keyword;
x_25 = l_Lake_LeanExe_exeFacet;
x_26 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_1);
lean_ctor_set(x_26, 3, x_25);
x_27 = 1;
x_28 = l_Lake_resolveExeTarget___closed__4;
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_27);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lake_ExternLib_keyword;
x_16 = l_Lake_ExternLib_sharedFacet;
x_17 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_1);
lean_ctor_set(x_17, 3, x_16);
x_18 = 1;
x_19 = l_Lake_resolveExeTarget___closed__4;
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lake_ExternLib_keyword;
x_27 = l_Lake_ExternLib_staticFacet;
x_28 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_1);
lean_ctor_set(x_28, 3, x_27);
x_29 = 1;
x_30 = l_Lake_resolveExeTarget___closed__4;
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_29);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lake_ExternLib_keyword;
x_38 = l_Lake_ExternLib_staticFacet;
x_39 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_1);
lean_ctor_set(x_39, 3, x_38);
x_40 = 1;
x_41 = l_Lake_resolveExeTarget___closed__4;
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_40);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveTargetInPackage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_findTargetDecl_x3f(x_3, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_inc(x_2);
lean_inc(x_3);
x_6 = l_Lake_Package_findTargetModule_x3f(x_3, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = 0;
x_9 = l_Lake_resolveConfigDeclTarget___closed__1;
x_10 = l_Lean_Name_toString(x_3, x_8, x_9);
x_11 = lean_alloc_ctor(16, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_Lake_resolveModuleTarget(x_1, x_13, x_4);
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
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec(x_5);
x_29 = l_Lake_resolveConfigDeclTarget(x_1, x_2, x_3, x_28, x_4);
return x_29;
}
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
x_2 = l_Array_emptyWithCapacity(lean_box(0), x_1);
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
x_3 = lean_ctor_get(x_2, 11);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lake_Package_keyword;
x_6 = l_Lean_Name_append(x_5, x_3);
x_7 = l_Lake_Workspace_findPackageFacetConfig_x3f(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = l_Lake_resolvePackageTarget___closed__1;
x_9 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_ctor_set(x_7, 0, x_13);
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_2);
lean_ctor_set(x_14, 3, x_6);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_16 = lean_ctor_get(x_12, 2);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_mk(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_2);
lean_ctor_set(x_25, 3, x_6);
x_26 = lean_ctor_get_uint8(x_22, sizeof(void*)*3);
x_27 = lean_ctor_get(x_22, 2);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_26);
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
x_4 = l_Lake_Workspace_findTargetDecl_x3f(x_2, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 4);
x_6 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_inc(x_2);
x_7 = l_Lake_Workspace_findTargetModule_x3f(x_2, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lake_resolveModuleTarget(x_1, x_10, x_3);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
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
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_mk(x_18);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_array_mk(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
x_26 = l_Lake_resolvePackageTarget(x_1, x_25, x_3);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_27);
lean_dec(x_4);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lake_resolveConfigDeclTarget(x_1, x_28, x_2, x_29, x_3);
return x_30;
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
lean_object* x_3; lean_object* x_4; uint8_t x_118; 
x_118 = l_Lake_resolveTargetBaseSpec___closed__11;
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_box(0);
x_120 = l_Lake_resolveTargetBaseSpec___closed__9;
x_121 = lean_unsigned_to_nat(0u);
x_122 = l_String_splitOnAux(x_2, x_120, x_121, x_121, x_121, x_119);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = l_Lake_parseExeTargetSpec___boxed__const__1;
x_124 = lean_alloc_ctor(18, 2, 0);
lean_ctor_set(x_124, 0, x_2);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_122, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_dec(x_122);
x_3 = x_126;
x_4 = x_127;
goto block_117;
}
}
else
{
lean_object* x_128; 
x_128 = lean_box(0);
lean_inc(x_2);
x_3 = x_2;
x_4 = x_128;
goto block_117;
}
block_117:
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_string_utf8_byte_size(x_3);
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
lean_inc(x_3);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_14);
x_17 = l_Lake_resolveTargetBaseSpec___closed__2;
x_18 = l_Substring_nextn(x_16, x_17, x_15);
x_19 = lean_nat_add(x_15, x_18);
lean_dec(x_18);
lean_inc(x_3);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_Lake_resolveTargetBaseSpec___closed__4;
x_22 = l_Substring_beq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_14);
x_23 = l_Lake_parsePackageSpec(x_1, x_3);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_2);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = l_Lake_stringToLegalOrSimpleName(x_13);
x_30 = l_Lake_Package_findTargetDecl_x3f(x_29, x_28);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_28);
x_31 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 3);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Lake_LeanExe_keyword;
x_38 = lean_name_eq(x_35, x_37);
lean_dec(x_35);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_28);
lean_ctor_set_tag(x_30, 20);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
lean_object* x_39; 
lean_free_object(x_30);
lean_dec(x_2);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_23, 0, x_39);
return x_23;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 3);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l_Lake_LeanExe_keyword;
x_45 = lean_name_eq(x_42, x_44);
lean_dec(x_42);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_28);
x_46 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_46);
return x_23;
}
else
{
lean_object* x_47; 
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_28);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_47, 2, x_43);
lean_ctor_set(x_23, 0, x_47);
return x_23;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_23, 0);
lean_inc(x_48);
lean_dec(x_23);
x_49 = l_Lake_stringToLegalOrSimpleName(x_13);
x_50 = l_Lake_Package_findTargetDecl_x3f(x_49, x_48);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_48);
x_51 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_51, 0, x_2);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_53, 3);
lean_inc(x_57);
lean_dec(x_53);
x_58 = l_Lake_LeanExe_keyword;
x_59 = lean_name_eq(x_56, x_58);
lean_dec(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_48);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(20, 1, 0);
} else {
 x_60 = x_54;
 lean_ctor_set_tag(x_60, 20);
}
lean_ctor_set(x_60, 0, x_2);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_54);
lean_dec(x_2);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_48);
lean_ctor_set(x_62, 1, x_55);
lean_ctor_set(x_62, 2, x_57);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_unsigned_to_nat(1u);
x_65 = l_Substring_nextn(x_16, x_64, x_15);
lean_dec(x_16);
x_66 = lean_nat_add(x_15, x_65);
lean_dec(x_65);
x_67 = lean_string_utf8_extract(x_3, x_66, x_14);
lean_dec(x_14);
lean_dec(x_66);
lean_dec(x_3);
x_68 = l_Lake_parsePackageSpec(x_1, x_67);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
lean_dec(x_13);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_68, 0);
x_74 = l_Lake_stringToLegalOrSimpleName(x_13);
x_75 = l_Lake_Package_findTargetDecl_x3f(x_74, x_73);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_dec(x_73);
x_76 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set_tag(x_68, 0);
lean_ctor_set(x_68, 0, x_76);
return x_68;
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 3);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l_Lake_LeanExe_keyword;
x_83 = lean_name_eq(x_80, x_82);
lean_dec(x_80);
if (x_83 == 0)
{
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_73);
lean_ctor_set_tag(x_75, 20);
lean_ctor_set(x_75, 0, x_2);
lean_ctor_set_tag(x_68, 0);
lean_ctor_set(x_68, 0, x_75);
return x_68;
}
else
{
lean_object* x_84; 
lean_free_object(x_75);
lean_dec(x_2);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_73);
lean_ctor_set(x_84, 1, x_79);
lean_ctor_set(x_84, 2, x_81);
lean_ctor_set(x_68, 0, x_84);
return x_68;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
lean_dec(x_75);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 3);
lean_inc(x_88);
lean_dec(x_85);
x_89 = l_Lake_LeanExe_keyword;
x_90 = lean_name_eq(x_87, x_89);
lean_dec(x_87);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_73);
x_91 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_91, 0, x_2);
lean_ctor_set_tag(x_68, 0);
lean_ctor_set(x_68, 0, x_91);
return x_68;
}
else
{
lean_object* x_92; 
lean_dec(x_2);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_73);
lean_ctor_set(x_92, 1, x_86);
lean_ctor_set(x_92, 2, x_88);
lean_ctor_set(x_68, 0, x_92);
return x_68;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_68, 0);
lean_inc(x_93);
lean_dec(x_68);
x_94 = l_Lake_stringToLegalOrSimpleName(x_13);
x_95 = l_Lake_Package_findTargetDecl_x3f(x_94, x_93);
lean_dec(x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_93);
x_96 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_96, 0, x_2);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 x_99 = x_95;
} else {
 lean_dec_ref(x_95);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 3);
lean_inc(x_102);
lean_dec(x_98);
x_103 = l_Lake_LeanExe_keyword;
x_104 = lean_name_eq(x_101, x_103);
lean_dec(x_101);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_93);
if (lean_is_scalar(x_99)) {
 x_105 = lean_alloc_ctor(20, 1, 0);
} else {
 x_105 = x_99;
 lean_ctor_set_tag(x_105, 20);
}
lean_ctor_set(x_105, 0, x_2);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_99);
lean_dec(x_2);
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_93);
lean_ctor_set(x_107, 1, x_100);
lean_ctor_set(x_107, 2, x_102);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_4);
lean_dec(x_3);
x_109 = !lean_is_exclusive(x_12);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_12, 1);
lean_dec(x_110);
x_111 = lean_ctor_get(x_12, 0);
lean_dec(x_111);
x_112 = l_Lake_parseExeTargetSpec___boxed__const__1;
lean_ctor_set_tag(x_12, 18);
lean_ctor_set(x_12, 1, x_112);
lean_ctor_set(x_12, 0, x_2);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_12);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_12);
x_114 = l_Lake_parseExeTargetSpec___boxed__const__1;
x_115 = lean_alloc_ctor(18, 2, 0);
lean_ctor_set(x_115, 0, x_2);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
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
l_Lake_resolveConfigDeclTarget___closed__1 = _init_l_Lake_resolveConfigDeclTarget___closed__1();
lean_mark_persistent(l_Lake_resolveConfigDeclTarget___closed__1);
l_Lake_resolveConfigDeclTarget___closed__2 = _init_l_Lake_resolveConfigDeclTarget___closed__2();
lean_mark_persistent(l_Lake_resolveConfigDeclTarget___closed__2);
l_Lake_resolveConfigDeclTarget___closed__3 = _init_l_Lake_resolveConfigDeclTarget___closed__3();
lean_mark_persistent(l_Lake_resolveConfigDeclTarget___closed__3);
l_Lake_resolveLibTarget_resolveFacet___closed__1 = _init_l_Lake_resolveLibTarget_resolveFacet___closed__1();
lean_mark_persistent(l_Lake_resolveLibTarget_resolveFacet___closed__1);
l_Lake_resolveLibTarget_resolveFacet___closed__2 = _init_l_Lake_resolveLibTarget_resolveFacet___closed__2();
lean_mark_persistent(l_Lake_resolveLibTarget_resolveFacet___closed__2);
l_Lake_resolveLibTarget_resolveFacet___closed__3 = _init_l_Lake_resolveLibTarget_resolveFacet___closed__3();
lean_mark_persistent(l_Lake_resolveLibTarget_resolveFacet___closed__3);
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
