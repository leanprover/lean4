// Lean compiler output
// Module: Lake.CLI.Build
// Imports: Lake.CLI.Error Lake.Config.Workspace Lake.Config.Monad Lake.Build.Infos Lake.Build.Job.Monad Lake.Build.Job.Register Lake.Util.IO
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_buildSpecs_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_mkBuildSpec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lake_parseTargetSpecs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0;
static lean_object* l_Lake_parseTargetSpec___closed__0;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildSpec_ctorIdx(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_parsePackageSpec_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_buildSpecs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_BuildInfo_key(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_parsePackageSpec_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_querySpecs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__2;
extern lean_object* l_Lake_ExternLib_sharedFacet;
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_resolveLibTarget_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lake_Package_keyword;
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(uint8_t);
lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__1;
LEAN_EXPORT lean_object* l_Lake_querySpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__0;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__4;
lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__3;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_querySpecs_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_exeFacet;
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetModule_x3f(lean_object*, lean_object*);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveExeTarget_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Module_leanArtsFacet;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
static lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1;
static lean_object* l_Lake_parseTargetSpecs___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1;
lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lake_parseTargetSpecs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_querySpecs_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__2;
LEAN_EXPORT lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveExeTarget_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lake_BuildKey_toSimpleString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(uint8_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lake_parseTargetSpecs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget___boxed(lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_parseTargetSpec___closed__1;
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_mkBuildSpec(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__3;
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_querySpecs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(uint8_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_parsePackageSpec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__5;
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lam__0(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_resolveLibTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_Lake_Job_mixArray___redArg(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec(lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_parsePackageSpec_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_staticFacet;
uint8_t l_Substring_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___boxed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__0;
LEAN_EXPORT lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___boxed(lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__4;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__1;
LEAN_EXPORT lean_object* l_Lake_BuildSpec_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_querySpecs_spec__0___lam__0(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_formatQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildSpecs___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildSpec_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildSpec_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_mkBuildSpec___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 1;
x_4 = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_mkBuildSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 1;
x_6 = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_4 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_4);
x_5 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
x_6 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_6);
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_mkConfigBuildSpec___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_mkConfigBuildSpec(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
lean_inc_ref(x_6);
lean_inc_ref(x_9);
x_10 = lean_apply_7(x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 2);
x_21 = lean_string_utf8_byte_size(x_20);
lean_dec_ref(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_free_object(x_12);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_free_object(x_11);
lean_dec(x_15);
lean_dec(x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec_ref(x_10);
x_24 = lean_ctor_get(x_6, 3);
lean_inc(x_24);
lean_dec_ref(x_6);
x_25 = lean_st_ref_take(x_24, x_13);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Lake_BuildInfo_key(x_9);
x_29 = l_Lake_BuildKey_toSimpleString(x_28);
x_30 = 0;
lean_ctor_set(x_12, 2, x_29);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_30);
lean_inc_ref(x_12);
x_31 = l_Lake_Job_toOpaque___redArg(x_12);
x_32 = lean_array_push(x_26, x_31);
x_33 = lean_st_ref_set(x_24, x_32, x_27);
lean_dec(x_24);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = l_Lake_Job_renew___redArg(x_12);
lean_ctor_set(x_11, 0, x_36);
lean_ctor_set(x_33, 0, x_11);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l_Lake_Job_renew___redArg(x_12);
lean_ctor_set(x_11, 0, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_ctor_get(x_12, 1);
x_42 = lean_ctor_get(x_12, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_12);
x_43 = lean_string_utf8_byte_size(x_42);
lean_dec_ref(x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_dec(x_41);
lean_dec_ref(x_40);
lean_free_object(x_11);
lean_dec(x_15);
lean_dec(x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
return x_10;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_10);
x_46 = lean_ctor_get(x_6, 3);
lean_inc(x_46);
lean_dec_ref(x_6);
x_47 = lean_st_ref_take(x_46, x_13);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = l_Lake_BuildInfo_key(x_9);
x_51 = l_Lake_BuildKey_toSimpleString(x_50);
x_52 = 0;
x_53 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_53, 0, x_40);
lean_ctor_set(x_53, 1, x_41);
lean_ctor_set(x_53, 2, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_52);
lean_inc_ref(x_53);
x_54 = l_Lake_Job_toOpaque___redArg(x_53);
x_55 = lean_array_push(x_48, x_54);
x_56 = lean_st_ref_set(x_46, x_55, x_49);
lean_dec(x_46);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = l_Lake_Job_renew___redArg(x_53);
lean_ctor_set(x_11, 0, x_59);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_11);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_61 = lean_ctor_get(x_11, 1);
lean_inc(x_61);
lean_dec(x_11);
x_62 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_64);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_65 = x_12;
} else {
 lean_dec_ref(x_12);
 x_65 = lean_box(0);
}
x_66 = lean_string_utf8_byte_size(x_64);
lean_dec_ref(x_64);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_nat_dec_eq(x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_dec(x_65);
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec(x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
return x_10;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec_ref(x_10);
x_69 = lean_ctor_get(x_6, 3);
lean_inc(x_69);
lean_dec_ref(x_6);
x_70 = lean_st_ref_take(x_69, x_13);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec_ref(x_70);
x_73 = l_Lake_BuildInfo_key(x_9);
x_74 = l_Lake_BuildKey_toSimpleString(x_73);
x_75 = 0;
if (lean_is_scalar(x_65)) {
 x_76 = lean_alloc_ctor(0, 3, 1);
} else {
 x_76 = x_65;
}
lean_ctor_set(x_76, 0, x_62);
lean_ctor_set(x_76, 1, x_63);
lean_ctor_set(x_76, 2, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_75);
lean_inc_ref(x_76);
x_77 = l_Lake_Job_toOpaque___redArg(x_76);
x_78 = lean_array_push(x_71, x_77);
x_79 = lean_st_ref_set(x_69, x_78, x_72);
lean_dec(x_69);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = l_Lake_Job_renew___redArg(x_76);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_61);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
}
}
else
{
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_16; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
lean_inc_ref(x_6);
lean_inc_ref(x_22);
x_23 = lean_apply_7(x_2, x_22, x_3, x_4, x_5, x_6, x_7, x_8);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec_ref(x_24);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
x_31 = lean_ctor_get(x_25, 2);
x_32 = lean_string_utf8_byte_size(x_31);
lean_dec_ref(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_free_object(x_25);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec_ref(x_22);
lean_dec_ref(x_6);
x_16 = x_23;
goto block_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_23);
x_35 = lean_ctor_get(x_6, 3);
lean_inc(x_35);
lean_dec_ref(x_6);
x_36 = lean_st_ref_take(x_35, x_26);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Lake_BuildInfo_key(x_22);
x_40 = l_Lake_BuildKey_toSimpleString(x_39);
x_41 = 0;
lean_ctor_set(x_25, 2, x_40);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_41);
lean_inc_ref(x_25);
x_42 = l_Lake_Job_toOpaque___redArg(x_25);
x_43 = lean_array_push(x_37, x_42);
x_44 = lean_st_ref_set(x_35, x_43, x_38);
lean_dec(x_35);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l_Lake_Job_renew___redArg(x_25);
x_9 = x_46;
x_10 = x_27;
x_11 = x_45;
goto block_15;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
x_49 = lean_ctor_get(x_25, 2);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
x_50 = lean_string_utf8_byte_size(x_49);
lean_dec_ref(x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_eq(x_50, x_51);
lean_dec(x_50);
if (x_52 == 0)
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_27);
lean_dec(x_26);
lean_dec_ref(x_22);
lean_dec_ref(x_6);
x_16 = x_23;
goto block_21;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_23);
x_53 = lean_ctor_get(x_6, 3);
lean_inc(x_53);
lean_dec_ref(x_6);
x_54 = lean_st_ref_take(x_53, x_26);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = l_Lake_BuildInfo_key(x_22);
x_58 = l_Lake_BuildKey_toSimpleString(x_57);
x_59 = 0;
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_47);
lean_ctor_set(x_60, 1, x_48);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_59);
lean_inc_ref(x_60);
x_61 = l_Lake_Job_toOpaque___redArg(x_60);
x_62 = lean_array_push(x_55, x_61);
x_63 = lean_st_ref_set(x_53, x_62, x_56);
lean_dec(x_53);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lake_Job_renew___redArg(x_60);
x_9 = x_65;
x_10 = x_27;
x_11 = x_64;
goto block_15;
}
}
}
else
{
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_6);
x_16 = x_23;
goto block_21;
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lake_Job_toOpaque___redArg(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
block_21:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec_ref(x_17);
x_9 = x_19;
x_10 = x_20;
x_11 = x_18;
goto block_15;
}
else
{
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(x_2);
x_7 = lean_apply_2(x_1, x_6, x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_box(x_2);
x_11 = lean_apply_2(x_1, x_10, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec_ref(x_1);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
lean_inc_ref(x_7);
lean_inc_ref(x_10);
x_12 = lean_apply_7(x_3, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 2);
x_23 = lean_ctor_get(x_14, 1);
lean_dec(x_23);
x_24 = lean_box(0);
x_25 = lean_box(x_2);
x_26 = lean_alloc_closure((void*)(l_Lake_BuildSpec_query___lam__0___boxed), 3, 2);
lean_closure_set(x_26, 0, x_11);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = 0;
x_29 = lean_task_map(x_26, x_21, x_27, x_28);
x_30 = lean_string_utf8_byte_size(x_22);
x_31 = lean_nat_dec_eq(x_30, x_27);
lean_dec(x_30);
if (x_31 == 0)
{
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_29);
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec_ref(x_22);
lean_free_object(x_12);
x_32 = lean_ctor_get(x_7, 3);
lean_inc(x_32);
lean_dec_ref(x_7);
x_33 = lean_st_ref_take(x_32, x_16);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = l_Lake_BuildInfo_key(x_10);
x_37 = l_Lake_BuildKey_toSimpleString(x_36);
lean_ctor_set(x_14, 2, x_37);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_29);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_28);
lean_inc_ref(x_14);
x_38 = l_Lake_Job_toOpaque___redArg(x_14);
x_39 = lean_array_push(x_34, x_38);
x_40 = lean_st_ref_set(x_32, x_39, x_35);
lean_dec(x_32);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = l_Lake_Job_renew___redArg(x_14);
lean_ctor_set(x_13, 0, x_43);
lean_ctor_set(x_40, 0, x_13);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_Lake_Job_renew___redArg(x_14);
lean_ctor_set(x_13, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_13);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get(x_14, 2);
x_49 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_14);
x_50 = lean_box(0);
x_51 = lean_box(x_2);
x_52 = lean_alloc_closure((void*)(l_Lake_BuildSpec_query___lam__0___boxed), 3, 2);
lean_closure_set(x_52, 0, x_11);
lean_closure_set(x_52, 1, x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = 0;
x_55 = lean_task_map(x_52, x_47, x_53, x_54);
x_56 = lean_string_utf8_byte_size(x_48);
x_57 = lean_nat_dec_eq(x_56, x_53);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec_ref(x_10);
lean_dec_ref(x_7);
x_58 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_50);
lean_ctor_set(x_58, 2, x_48);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_49);
lean_ctor_set(x_13, 0, x_58);
return x_12;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_48);
lean_free_object(x_12);
x_59 = lean_ctor_get(x_7, 3);
lean_inc(x_59);
lean_dec_ref(x_7);
x_60 = lean_st_ref_take(x_59, x_16);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = l_Lake_BuildInfo_key(x_10);
x_64 = l_Lake_BuildKey_toSimpleString(x_63);
x_65 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_50);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_54);
lean_inc_ref(x_65);
x_66 = l_Lake_Job_toOpaque___redArg(x_65);
x_67 = lean_array_push(x_61, x_66);
x_68 = lean_st_ref_set(x_59, x_67, x_62);
lean_dec(x_59);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = l_Lake_Job_renew___redArg(x_65);
lean_ctor_set(x_13, 0, x_71);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_13);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_73 = lean_ctor_get(x_13, 1);
lean_inc(x_73);
lean_dec(x_13);
x_74 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_75);
x_76 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_77 = x_14;
} else {
 lean_dec_ref(x_14);
 x_77 = lean_box(0);
}
x_78 = lean_box(0);
x_79 = lean_box(x_2);
x_80 = lean_alloc_closure((void*)(l_Lake_BuildSpec_query___lam__0___boxed), 3, 2);
lean_closure_set(x_80, 0, x_11);
lean_closure_set(x_80, 1, x_79);
x_81 = lean_unsigned_to_nat(0u);
x_82 = 0;
x_83 = lean_task_map(x_80, x_74, x_81, x_82);
x_84 = lean_string_utf8_byte_size(x_75);
x_85 = lean_nat_dec_eq(x_84, x_81);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_10);
lean_dec_ref(x_7);
if (lean_is_scalar(x_77)) {
 x_86 = lean_alloc_ctor(0, 3, 1);
} else {
 x_86 = x_77;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_78);
lean_ctor_set(x_86, 2, x_75);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_76);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_73);
lean_ctor_set(x_12, 0, x_87);
return x_12;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_75);
lean_free_object(x_12);
x_88 = lean_ctor_get(x_7, 3);
lean_inc(x_88);
lean_dec_ref(x_7);
x_89 = lean_st_ref_take(x_88, x_16);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec_ref(x_89);
x_92 = l_Lake_BuildInfo_key(x_10);
x_93 = l_Lake_BuildKey_toSimpleString(x_92);
if (lean_is_scalar(x_77)) {
 x_94 = lean_alloc_ctor(0, 3, 1);
} else {
 x_94 = x_77;
}
lean_ctor_set(x_94, 0, x_83);
lean_ctor_set(x_94, 1, x_78);
lean_ctor_set(x_94, 2, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*3, x_82);
lean_inc_ref(x_94);
x_95 = l_Lake_Job_toOpaque___redArg(x_94);
x_96 = lean_array_push(x_90, x_95);
x_97 = lean_st_ref_set(x_88, x_96, x_91);
lean_dec(x_88);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = l_Lake_Job_renew___redArg(x_94);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_73);
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_98);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_103 = lean_ctor_get(x_12, 1);
lean_inc(x_103);
lean_dec(x_12);
x_104 = lean_ctor_get(x_13, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_105 = x_13;
} else {
 lean_dec_ref(x_13);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_107);
x_108 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_109 = x_14;
} else {
 lean_dec_ref(x_14);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
x_111 = lean_box(x_2);
x_112 = lean_alloc_closure((void*)(l_Lake_BuildSpec_query___lam__0___boxed), 3, 2);
lean_closure_set(x_112, 0, x_11);
lean_closure_set(x_112, 1, x_111);
x_113 = lean_unsigned_to_nat(0u);
x_114 = 0;
x_115 = lean_task_map(x_112, x_106, x_113, x_114);
x_116 = lean_string_utf8_byte_size(x_107);
x_117 = lean_nat_dec_eq(x_116, x_113);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_10);
lean_dec_ref(x_7);
if (lean_is_scalar(x_109)) {
 x_118 = lean_alloc_ctor(0, 3, 1);
} else {
 x_118 = x_109;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_110);
lean_ctor_set(x_118, 2, x_107);
lean_ctor_set_uint8(x_118, sizeof(void*)*3, x_108);
if (lean_is_scalar(x_105)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_105;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_104);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_103);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec_ref(x_107);
x_121 = lean_ctor_get(x_7, 3);
lean_inc(x_121);
lean_dec_ref(x_7);
x_122 = lean_st_ref_take(x_121, x_103);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec_ref(x_122);
x_125 = l_Lake_BuildInfo_key(x_10);
x_126 = l_Lake_BuildKey_toSimpleString(x_125);
if (lean_is_scalar(x_109)) {
 x_127 = lean_alloc_ctor(0, 3, 1);
} else {
 x_127 = x_109;
}
lean_ctor_set(x_127, 0, x_115);
lean_ctor_set(x_127, 1, x_110);
lean_ctor_set(x_127, 2, x_126);
lean_ctor_set_uint8(x_127, sizeof(void*)*3, x_114);
lean_inc_ref(x_127);
x_128 = l_Lake_Job_toOpaque___redArg(x_127);
x_129 = lean_array_push(x_123, x_128);
x_130 = lean_st_ref_set(x_121, x_129, x_124);
lean_dec(x_121);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = l_Lake_Job_renew___redArg(x_127);
if (lean_is_scalar(x_105)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_105;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_104);
if (lean_is_scalar(x_132)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_132;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_131);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
x_136 = !lean_is_exclusive(x_12);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_12, 0);
lean_dec(x_137);
x_138 = !lean_is_exclusive(x_13);
if (x_138 == 0)
{
return x_12;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_13, 0);
x_140 = lean_ctor_get(x_13, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_13);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_12, 0, x_141);
return x_12;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_12, 1);
lean_inc(x_142);
lean_dec(x_12);
x_143 = lean_ctor_get(x_13, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_13, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_145 = x_13;
} else {
 lean_dec_ref(x_13);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_142);
return x_147;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lake_BuildSpec_query___lam__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_BuildSpec_query(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_buildSpecs_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
lean_inc_ref(x_4);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_15);
x_16 = lean_apply_7(x_4, x_15, x_5, x_6, x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_3, x_2, x_19);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_17, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_17, 1);
lean_inc(x_49);
lean_dec_ref(x_17);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 1);
x_53 = lean_ctor_get(x_48, 2);
x_54 = lean_string_utf8_byte_size(x_53);
lean_dec_ref(x_53);
x_55 = lean_nat_dec_eq(x_54, x_19);
lean_dec(x_54);
if (x_55 == 0)
{
lean_free_object(x_48);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_49);
lean_dec(x_18);
lean_dec_ref(x_15);
x_30 = x_16;
goto block_47;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_16);
x_56 = lean_ctor_get(x_8, 3);
x_57 = lean_st_ref_take(x_56, x_18);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = l_Lake_BuildInfo_key(x_15);
x_61 = l_Lake_BuildKey_toSimpleString(x_60);
x_62 = 0;
lean_ctor_set(x_48, 2, x_61);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_62);
lean_inc_ref(x_48);
x_63 = l_Lake_Job_toOpaque___redArg(x_48);
x_64 = lean_array_push(x_58, x_63);
x_65 = lean_st_ref_set(x_56, x_64, x_59);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = l_Lake_Job_renew___redArg(x_48);
x_21 = x_67;
x_22 = x_49;
x_23 = x_66;
goto block_29;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_48, 0);
x_69 = lean_ctor_get(x_48, 1);
x_70 = lean_ctor_get(x_48, 2);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_48);
x_71 = lean_string_utf8_byte_size(x_70);
lean_dec_ref(x_70);
x_72 = lean_nat_dec_eq(x_71, x_19);
lean_dec(x_71);
if (x_72 == 0)
{
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_49);
lean_dec(x_18);
lean_dec_ref(x_15);
x_30 = x_16;
goto block_47;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec_ref(x_16);
x_73 = lean_ctor_get(x_8, 3);
x_74 = lean_st_ref_take(x_73, x_18);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = l_Lake_BuildInfo_key(x_15);
x_78 = l_Lake_BuildKey_toSimpleString(x_77);
x_79 = 0;
x_80 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_80, 0, x_68);
lean_ctor_set(x_80, 1, x_69);
lean_ctor_set(x_80, 2, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*3, x_79);
lean_inc_ref(x_80);
x_81 = l_Lake_Job_toOpaque___redArg(x_80);
x_82 = lean_array_push(x_75, x_81);
x_83 = lean_st_ref_set(x_73, x_82, x_76);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l_Lake_Job_renew___redArg(x_80);
x_21 = x_85;
x_22 = x_49;
x_23 = x_84;
goto block_29;
}
}
}
else
{
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_15);
x_30 = x_16;
goto block_47;
}
block_29:
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_24 = l_Lake_Job_toOpaque___redArg(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_2, x_25);
x_27 = lean_array_uset(x_20, x_2, x_24);
x_2 = x_26;
x_3 = x_27;
x_9 = x_22;
x_10 = x_23;
goto _start;
}
block_47:
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec_ref(x_31);
x_21 = x_33;
x_22 = x_34;
x_23 = x_32;
goto block_29;
}
else
{
uint8_t x_35; 
lean_dec_ref(x_20);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_30, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
return x_30;
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
lean_ctor_set(x_30, 0, x_40);
return x_30;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_44 = x_31;
} else {
 lean_dec_ref(x_31);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
}
}
}
}
static lean_object* _init_l_Lake_buildSpecs___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<collection>", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSpecs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_buildSpecs_spec__0(x_9, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = l_Lake_buildSpecs___closed__0;
x_18 = l_Lake_Job_mixArray___redArg(x_16, x_17);
lean_dec(x_16);
lean_ctor_set(x_12, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = l_Lake_buildSpecs___closed__0;
x_22 = l_Lake_Job_mixArray___redArg(x_19, x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_27 = x_12;
} else {
 lean_dec_ref(x_12);
 x_27 = lean_box(0);
}
x_28 = l_Lake_buildSpecs___closed__0;
x_29 = l_Lake_Job_mixArray___redArg(x_25, x_28);
lean_dec(x_25);
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_11, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_11, 0, x_37);
return x_11;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_dec(x_11);
x_39 = lean_ctor_get(x_12, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_41 = x_12;
} else {
 lean_dec_ref(x_12);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_buildSpecs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_buildSpecs_spec__0(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_querySpecs_spec__0___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(x_2);
x_7 = lean_apply_2(x_1, x_6, x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_box(x_2);
x_11 = lean_apply_2(x_1, x_10, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec_ref(x_1);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_querySpecs_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
lean_dec(x_15);
lean_inc_ref(x_5);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_16);
x_18 = lean_apply_7(x_5, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 2);
x_26 = lean_ctor_get(x_20, 1);
lean_dec(x_26);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_uset(x_4, x_3, x_27);
x_37 = lean_box(0);
x_38 = lean_box(x_1);
x_39 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_querySpecs_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(x_39, 0, x_17);
lean_closure_set(x_39, 1, x_38);
x_40 = 0;
x_41 = lean_task_map(x_39, x_24, x_27, x_40);
x_42 = lean_string_utf8_byte_size(x_25);
x_43 = lean_nat_dec_eq(x_42, x_27);
lean_dec(x_42);
if (x_43 == 0)
{
lean_dec_ref(x_16);
lean_ctor_set(x_20, 1, x_37);
lean_ctor_set(x_20, 0, x_41);
x_29 = x_20;
x_30 = x_22;
x_31 = x_21;
goto block_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_25);
x_44 = lean_ctor_get(x_9, 3);
x_45 = lean_st_ref_take(x_44, x_21);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l_Lake_BuildInfo_key(x_16);
x_49 = l_Lake_BuildKey_toSimpleString(x_48);
lean_ctor_set(x_20, 2, x_49);
lean_ctor_set(x_20, 1, x_37);
lean_ctor_set(x_20, 0, x_41);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_40);
lean_inc_ref(x_20);
x_50 = l_Lake_Job_toOpaque___redArg(x_20);
x_51 = lean_array_push(x_46, x_50);
x_52 = lean_st_ref_set(x_44, x_51, x_47);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l_Lake_Job_renew___redArg(x_20);
x_29 = x_54;
x_30 = x_22;
x_31 = x_53;
goto block_36;
}
block_36:
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 1;
x_33 = lean_usize_add(x_3, x_32);
x_34 = lean_array_uset(x_28, x_3, x_29);
x_3 = x_33;
x_4 = x_34;
x_10 = x_30;
x_11 = x_31;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 2);
x_57 = lean_ctor_get_uint8(x_20, sizeof(void*)*3);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_uset(x_4, x_3, x_58);
x_68 = lean_box(0);
x_69 = lean_box(x_1);
x_70 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_querySpecs_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(x_70, 0, x_17);
lean_closure_set(x_70, 1, x_69);
x_71 = 0;
x_72 = lean_task_map(x_70, x_55, x_58, x_71);
x_73 = lean_string_utf8_byte_size(x_56);
x_74 = lean_nat_dec_eq(x_73, x_58);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec_ref(x_16);
x_75 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_68);
lean_ctor_set(x_75, 2, x_56);
lean_ctor_set_uint8(x_75, sizeof(void*)*3, x_57);
x_60 = x_75;
x_61 = x_22;
x_62 = x_21;
goto block_67;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_56);
x_76 = lean_ctor_get(x_9, 3);
x_77 = lean_st_ref_take(x_76, x_21);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = l_Lake_BuildInfo_key(x_16);
x_81 = l_Lake_BuildKey_toSimpleString(x_80);
x_82 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_68);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*3, x_71);
lean_inc_ref(x_82);
x_83 = l_Lake_Job_toOpaque___redArg(x_82);
x_84 = lean_array_push(x_78, x_83);
x_85 = lean_st_ref_set(x_76, x_84, x_79);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = l_Lake_Job_renew___redArg(x_82);
x_60 = x_87;
x_61 = x_22;
x_62 = x_86;
goto block_67;
}
block_67:
{
size_t x_63; size_t x_64; lean_object* x_65; 
x_63 = 1;
x_64 = lean_usize_add(x_3, x_63);
x_65 = lean_array_uset(x_59, x_3, x_60);
x_3 = x_64;
x_4 = x_65;
x_10 = x_61;
x_11 = x_62;
goto _start;
}
}
}
else
{
uint8_t x_88; 
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_88 = !lean_is_exclusive(x_18);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_18, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_19);
if (x_90 == 0)
{
return x_18;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_19, 0);
x_92 = lean_ctor_get(x_19, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_19);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_18, 0, x_93);
return x_18;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_18, 1);
lean_inc(x_94);
lean_dec(x_18);
x_95 = lean_ctor_get(x_19, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_19, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_97 = x_19;
} else {
 lean_dec_ref(x_19);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
return x_99;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_querySpecs(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_size(x_1);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_querySpecs_spec__0(x_2, x_10, x_11, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = l_Lake_buildSpecs___closed__0;
x_19 = l_Lake_Job_collectArray___redArg(x_17, x_18);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_Lake_buildSpecs___closed__0;
x_23 = l_Lake_Job_collectArray___redArg(x_20, x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_12, 0, x_24);
return x_12;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_28 = x_13;
} else {
 lean_dec_ref(x_13);
 x_28 = lean_box(0);
}
x_29 = l_Lake_buildSpecs___closed__0;
x_30 = l_Lake_Job_collectArray___redArg(x_26, x_29);
lean_dec(x_26);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_12, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_12, 0, x_38);
return x_12;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_dec(x_12);
x_40 = lean_ctor_get(x_13, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_13, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_42 = x_13;
} else {
 lean_dec_ref(x_13);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_querySpecs_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_querySpecs_spec__0___lam__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_querySpecs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_querySpecs_spec__0(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_querySpecs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_querySpecs(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_parsePackageSpec_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = l_Lean_Name_quickCmp(x_2, x_3);
switch (x_7) {
case 0:
{
x_1 = x_5;
goto _start;
}
case 1:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
default: 
{
x_1 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_parsePackageSpec_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_parsePackageSpec_spec__0___redArg(x_3, x_4);
return x_5;
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
x_6 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_2);
x_7 = l_Lake_stringToLegalOrSimpleName(x_2);
x_8 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_parsePackageSpec_spec__0___redArg(x_6, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_parsePackageSpec_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_parsePackageSpec_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_parsePackageSpec_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_parsePackageSpec_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_parsePackageSpec(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Json_compress(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec_ref(x_2);
x_8 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0;
x_9 = lean_alloc_ctor(14, 2, 0);
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*4);
x_15 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_15);
lean_dec(x_12);
lean_inc(x_13);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_13);
x_16 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_2);
lean_ctor_set(x_16, 3, x_6);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_14);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get_uint8(x_19, sizeof(void*)*4);
x_22 = lean_ctor_get(x_19, 3);
lean_inc_ref(x_22);
lean_dec(x_19);
lean_inc(x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_24 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_2);
lean_ctor_set(x_24, 3, x_6);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_21);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_alloc_closure((void*)(l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0___boxed), 2, 0);
x_29 = l_Lake_Module_leanArtsFacet;
lean_inc(x_27);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_31 = l_Lake_Module_keyword;
x_32 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_2);
lean_ctor_set(x_32, 3, x_29);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_4);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Name_isAnonymous(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_6 = lean_alloc_ctor(20, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_5);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("default", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_9 = x_4;
} else {
 lean_dec_ref(x_4);
 x_9 = lean_box(0);
}
x_10 = l_Lean_Name_isAnonymous(x_7);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; uint8_t x_41; 
lean_dec(x_3);
x_11 = 1;
x_41 = l_Lean_Name_isAnonymous(x_5);
if (x_41 == 0)
{
x_12 = x_5;
goto block_40;
}
else
{
lean_object* x_42; 
lean_dec(x_5);
x_42 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__2;
x_12 = x_42;
goto block_40;
}
block_40:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_7);
x_13 = l_Lean_Name_append(x_7, x_12);
x_14 = l_Lake_Workspace_findFacetConfig_x3f(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_2);
x_15 = l_Lean_Name_toString(x_7, x_11);
x_16 = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_19, sizeof(void*)*4);
x_22 = lean_ctor_get(x_19, 3);
lean_inc_ref(x_22);
lean_dec(x_19);
lean_inc(x_6);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_8);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_6);
if (lean_is_scalar(x_9)) {
 x_25 = lean_alloc_ctor(1, 4, 0);
} else {
 x_25 = x_9;
 lean_ctor_set_tag(x_25, 1);
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_13);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_21);
x_27 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_28 = lean_array_push(x_27, x_26);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_29, sizeof(void*)*4);
x_32 = lean_ctor_get(x_29, 3);
lean_inc_ref(x_32);
lean_dec(x_29);
lean_inc(x_6);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_6);
lean_ctor_set(x_33, 2, x_8);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_6);
if (lean_is_scalar(x_9)) {
 x_35 = lean_alloc_ctor(1, 4, 0);
} else {
 x_35 = x_9;
 lean_ctor_set_tag(x_35, 1);
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_13);
x_36 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_31);
x_37 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_38 = lean_array_push(x_37, x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_43 = l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(x_2, x_3, x_5, x_8);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_50 = lean_array_push(x_49, x_48);
lean_ctor_set(x_43, 0, x_50);
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
x_52 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_53 = lean_array_push(x_52, x_51);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("library", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Workspace_findLibraryFacetConfig_x3f(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_5 = l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__0;
x_6 = lean_alloc_ctor(14, 2, 0);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*4);
x_14 = lean_ctor_get(x_10, 3);
lean_inc_ref(x_14);
lean_dec(x_10);
lean_inc(x_11);
lean_inc(x_12);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_11);
x_16 = l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__2;
x_17 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_3);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_13);
lean_ctor_set(x_4, 0, x_18);
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
lean_dec(x_4);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get_uint8(x_20, sizeof(void*)*4);
x_24 = lean_ctor_get(x_20, 3);
lean_inc_ref(x_24);
lean_dec(x_20);
lean_inc(x_21);
lean_inc(x_22);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_21);
x_26 = l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__2;
x_27 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_2);
lean_ctor_set(x_27, 3, x_3);
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_23);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_resolveLibTarget_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_5, x_4);
lean_inc_ref(x_2);
x_9 = l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet(x_1, x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec_ref(x_9);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_5, x_4, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
x_18 = lean_array_uset(x_15, x_4, x_13);
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
x_5 = l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__2;
x_6 = l_Lean_Name_append(x_5, x_3);
x_7 = l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet(x_1, x_2, x_6);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_14 = lean_array_push(x_13, x_12);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_17 = lean_array_push(x_16, x_15);
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
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_19, 7);
lean_inc_ref(x_20);
x_21 = lean_array_size(x_20);
x_22 = 0;
x_23 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_resolveLibTarget_spec__0(x_1, x_2, x_21, x_22, x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_resolveLibTarget_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_resolveLibTarget_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_resolveLibTarget(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveExeTarget_spec__0(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveExeTarget_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("executable", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exe", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_18; 
x_3 = lean_alloc_closure((void*)(l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___lam__0___boxed), 2, 0);
x_18 = l_Lean_Name_isAnonymous(x_2);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__2;
x_20 = lean_name_eq(x_2, x_19);
x_4 = x_20;
goto block_17;
}
else
{
x_4 = x_18;
goto block_17;
}
block_17:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__0;
x_6 = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lake_LeanExe_exeFacet;
lean_inc(x_9);
lean_inc(x_10);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
x_13 = l_Lake_LeanExe_keyword;
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_1);
lean_ctor_set(x_14, 3, x_11);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveExeTarget_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveExeTarget_spec__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___lam__0(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shared", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("external library", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("static", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_29; 
x_3 = l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__0;
x_29 = l_Lean_Name_isAnonymous(x_2);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__5;
x_31 = lean_name_eq(x_2, x_30);
x_4 = x_31;
goto block_28;
}
else
{
x_4 = x_29;
goto block_28;
}
block_28:
{
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__2;
x_6 = lean_name_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_1);
x_7 = l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__3;
x_8 = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lake_ExternLib_sharedFacet;
lean_inc(x_11);
lean_inc(x_12);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_11);
x_15 = l_Lake_ExternLib_keyword;
x_16 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_1);
lean_ctor_set(x_16, 3, x_13);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_6);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lake_ExternLib_staticFacet;
lean_inc(x_20);
lean_inc(x_21);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_20);
x_24 = l_Lake_ExternLib_keyword;
x_25 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_1);
lean_ctor_set(x_25, 3, x_22);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_4);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_findTargetDecl_x3f(x_3, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_inc_ref(x_2);
lean_inc(x_3);
x_6 = l_Lake_Package_findTargetModule_x3f(x_3, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = 0;
x_9 = l_Lean_Name_toString(x_3, x_8);
x_10 = lean_alloc_ctor(17, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec_ref(x_6);
x_13 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_12, x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_20 = lean_array_push(x_19, x_18);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_23 = lean_array_push(x_22, x_21);
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
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
lean_dec_ref(x_5);
x_26 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(x_1, x_2, x_3, x_25, x_4);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_uget(x_3, x_4);
x_14 = lean_box(0);
lean_inc_ref(x_2);
x_15 = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(x_1, x_2, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_dec_ref(x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_dec_ref(x_2);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_7 = x_16;
goto block_11;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Array_append___redArg(x_6, x_17);
lean_dec(x_17);
x_7 = x_18;
goto block_11;
}
}
else
{
lean_object* x_19; 
lean_dec_ref(x_2);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
x_6 = x_7;
goto _start;
}
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 12);
lean_inc_ref(x_3);
x_4 = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_6, x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_10 = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1;
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(x_1, x_2, x_3, x_11, x_12, x_4);
lean_dec_ref(x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec_ref(x_2);
x_8 = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0;
x_9 = lean_alloc_ctor(14, 2, 0);
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*4);
x_15 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_15);
lean_dec(x_12);
lean_inc(x_13);
lean_ctor_set(x_7, 0, x_13);
x_16 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_2);
lean_ctor_set(x_16, 3, x_6);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_14);
x_18 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_19 = lean_array_push(x_18, x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get_uint8(x_21, sizeof(void*)*4);
x_24 = lean_ctor_get(x_21, 3);
lean_inc_ref(x_24);
lean_dec(x_21);
lean_inc(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_26 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 2, x_2);
lean_ctor_set(x_26, 3, x_6);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_23);
x_28 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_29 = lean_array_push(x_28, x_27);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_3);
x_31 = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(x_1, x_2);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Workspace_findTargetDecl_x3f(x_2, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 4);
x_6 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_parsePackageSpec_spec__0___redArg(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_inc(x_2);
x_7 = l_Lake_Workspace_findTargetModule_x3f(x_2, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(15, 1, 0);
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
lean_dec_ref(x_7);
x_11 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_10, x_3);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_18 = lean_array_push(x_17, x_16);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_21 = lean_array_push(x_20, x_19);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec_ref(x_6);
x_24 = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(x_1, x_23, x_3);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec_ref(x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(x_1, x_26, x_2, x_27, x_3);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static uint8_t _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0;
x_2 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("+", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_27; uint8_t x_28; 
x_27 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0;
x_28 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1;
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_box(0);
x_31 = l_String_splitOnAux(x_2, x_27, x_29, x_29, x_29, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_26;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec_ref(x_2);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec_ref(x_31);
x_6 = x_33;
goto block_20;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 1);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_2);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec_ref(x_31);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec_ref(x_32);
x_37 = l_Lake_parsePackageSpec(x_1, x_35);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_36);
lean_dec(x_3);
lean_dec_ref(x_1);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_string_utf8_byte_size(x_36);
x_44 = lean_nat_dec_eq(x_43, x_29);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_43);
lean_inc(x_36);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_29);
lean_ctor_set(x_45, 2, x_43);
x_46 = lean_unsigned_to_nat(1u);
x_47 = l_Substring_nextn(x_45, x_46, x_29);
lean_dec_ref(x_45);
lean_inc(x_47);
lean_inc(x_36);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_29);
lean_ctor_set(x_48, 2, x_47);
x_49 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__4;
x_50 = l_Substring_beq(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_47);
lean_dec(x_43);
lean_free_object(x_37);
x_51 = l_Lake_stringToLegalOrSimpleName(x_36);
x_52 = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(x_1, x_42, x_51, x_3);
lean_dec_ref(x_1);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_string_utf8_extract(x_36, x_47, x_43);
lean_dec(x_43);
lean_dec(x_47);
lean_dec(x_36);
x_54 = l_String_toName(x_53);
lean_inc(x_54);
x_55 = l_Lake_Package_findTargetModule_x3f(x_54, x_42);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_56 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_tag(x_37, 0);
lean_ctor_set(x_37, 0, x_56);
return x_37;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_54);
lean_free_object(x_37);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_57, x_3);
lean_dec_ref(x_1);
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
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_65 = lean_array_push(x_64, x_63);
lean_ctor_set(x_58, 0, x_65);
return x_58;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
lean_dec(x_58);
x_67 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_68 = lean_array_push(x_67, x_66);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_43);
lean_free_object(x_37);
lean_dec(x_36);
x_70 = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(x_1, x_42, x_3);
lean_dec_ref(x_1);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_37, 0);
lean_inc(x_71);
lean_dec(x_37);
x_72 = lean_string_utf8_byte_size(x_36);
x_73 = lean_nat_dec_eq(x_72, x_29);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_inc(x_72);
lean_inc(x_36);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_36);
lean_ctor_set(x_74, 1, x_29);
lean_ctor_set(x_74, 2, x_72);
x_75 = lean_unsigned_to_nat(1u);
x_76 = l_Substring_nextn(x_74, x_75, x_29);
lean_dec_ref(x_74);
lean_inc(x_76);
lean_inc(x_36);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_36);
lean_ctor_set(x_77, 1, x_29);
lean_ctor_set(x_77, 2, x_76);
x_78 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__4;
x_79 = l_Substring_beq(x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_76);
lean_dec(x_72);
x_80 = l_Lake_stringToLegalOrSimpleName(x_36);
x_81 = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(x_1, x_71, x_80, x_3);
lean_dec_ref(x_1);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_string_utf8_extract(x_36, x_76, x_72);
lean_dec(x_72);
lean_dec(x_76);
lean_dec(x_36);
x_83 = l_String_toName(x_82);
lean_inc(x_83);
x_84 = l_Lake_Package_findTargetModule_x3f(x_83, x_71);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_85 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_85, 0, x_83);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_83);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec_ref(x_84);
x_88 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_87, x_3);
lean_dec_ref(x_1);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 1, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_88, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_93 = x_88;
} else {
 lean_dec_ref(x_88);
 x_93 = lean_box(0);
}
x_94 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_95 = lean_array_push(x_94, x_92);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_93;
}
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_97; 
lean_dec(x_72);
lean_dec(x_36);
x_97 = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(x_1, x_71, x_3);
lean_dec_ref(x_1);
return x_97;
}
}
}
}
else
{
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_26;
}
}
}
}
else
{
x_6 = x_2;
goto block_20;
}
block_20:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_string_utf8_byte_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
if (x_5 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lake_stringToLegalOrSimpleName(x_6);
x_11 = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(x_1, x_10, x_3);
lean_dec_ref(x_1);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lake_parsePackageSpec(x_1, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec_ref(x_12);
x_17 = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(x_1, x_16, x_3);
lean_dec_ref(x_1);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_6);
x_18 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_18);
x_19 = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(x_1, x_18, x_3);
lean_dec_ref(x_1);
return x_19;
}
}
block_26:
{
if (x_4 == 0)
{
uint32_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 47;
x_22 = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set_uint32(x_22, sizeof(void*)*1, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_24, 0, x_2);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_4);
x_7 = lean_unbox(x_5);
x_8 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_2);
lean_inc(x_6);
lean_inc_ref(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Substring_nextn(x_7, x_8, x_5);
lean_dec_ref(x_7);
lean_inc(x_9);
lean_inc_ref(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_9);
x_11 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__2;
lean_inc_ref(x_10);
x_12 = l_Substring_beq(x_10, x_11);
x_13 = 1;
if (x_12 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__4;
x_15 = l_Substring_beq(x_10, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_6);
lean_inc_ref(x_2);
x_16 = l_Lake_resolvePath(x_2, x_4);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_string_utf8_byte_size(x_18);
x_21 = lean_nat_dec_eq(x_20, x_5);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_free_object(x_16);
x_22 = l_System_FilePath_isDir(x_18, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = l_Lake_Workspace_findModuleBySrc_x3f(x_18, x_1);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; lean_object* x_29; 
x_28 = lean_unbox(x_23);
lean_dec(x_23);
x_29 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_2, x_3, x_13, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec_ref(x_29);
lean_ctor_set(x_22, 0, x_31);
return x_22;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_23);
lean_dec_ref(x_2);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec_ref(x_27);
x_33 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_32, x_3);
lean_dec_ref(x_1);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_34);
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_37 = lean_array_push(x_36, x_35);
lean_ctor_set(x_22, 0, x_37);
return x_22;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = l_Lake_Workspace_findModuleBySrc_x3f(x_18, x_1);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; lean_object* x_41; 
x_40 = lean_unbox(x_23);
lean_dec(x_23);
x_41 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_2, x_3, x_13, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec_ref(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_23);
lean_dec_ref(x_2);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec_ref(x_39);
x_47 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_46, x_3);
lean_dec_ref(x_1);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_38);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec_ref(x_47);
x_51 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_52 = lean_array_push(x_51, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_38);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_23);
lean_dec(x_18);
x_54 = !lean_is_exclusive(x_22);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_22, 0);
lean_dec(x_55);
x_56 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_2, x_3, x_15, x_15);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_57);
return x_22;
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec_ref(x_56);
lean_ctor_set(x_22, 0, x_58);
return x_22;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_22, 1);
lean_inc(x_59);
lean_dec(x_22);
x_60 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_2, x_3, x_15, x_15);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec_ref(x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_18);
x_65 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_2, x_3, x_13, x_15);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_66);
return x_16;
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec_ref(x_65);
lean_ctor_set(x_16, 0, x_67);
return x_16;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_16, 0);
x_69 = lean_ctor_get(x_16, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_16);
x_70 = lean_string_utf8_byte_size(x_68);
x_71 = lean_nat_dec_eq(x_70, x_5);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_System_FilePath_isDir(x_68, x_69);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = l_Lake_Workspace_findModuleBySrc_x3f(x_68, x_1);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; lean_object* x_79; 
x_78 = lean_unbox(x_73);
lean_dec(x_73);
x_79 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_2, x_3, x_13, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_76;
 lean_ctor_set_tag(x_81, 1);
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_75);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
lean_dec_ref(x_79);
if (lean_is_scalar(x_76)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_76;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_73);
lean_dec_ref(x_2);
x_84 = lean_ctor_get(x_77, 0);
lean_inc(x_84);
lean_dec_ref(x_77);
x_85 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_84, x_3);
lean_dec_ref(x_1);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
if (lean_is_scalar(x_76)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_76;
 lean_ctor_set_tag(x_87, 1);
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_75);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
lean_dec_ref(x_85);
x_89 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_90 = lean_array_push(x_89, x_88);
if (lean_is_scalar(x_76)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_76;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_75);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_73);
lean_dec(x_68);
x_92 = lean_ctor_get(x_72, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_93 = x_72;
} else {
 lean_dec_ref(x_72);
 x_93 = lean_box(0);
}
x_94 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_2, x_3, x_15, x_15);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_93;
 lean_ctor_set_tag(x_96, 1);
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
lean_dec_ref(x_94);
if (lean_is_scalar(x_93)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_93;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_92);
return x_98;
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_68);
x_99 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_2, x_3, x_13, x_15);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_69);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
lean_dec_ref(x_99);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_69);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_string_utf8_extract(x_2, x_9, x_6);
lean_dec(x_6);
lean_dec(x_9);
lean_dec_ref(x_2);
x_105 = l_String_toName(x_104);
lean_inc(x_105);
x_106 = l_Lake_Workspace_findTargetModule_x3f(x_105, x_1);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_107 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_107, 0, x_105);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_4);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_105);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
lean_dec_ref(x_106);
x_110 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_109, x_3);
lean_dec_ref(x_1);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_4);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
lean_dec_ref(x_110);
x_114 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_115 = lean_array_push(x_114, x_113);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_4);
return x_116;
}
}
}
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
lean_dec_ref(x_10);
x_117 = lean_string_utf8_extract(x_2, x_9, x_6);
lean_dec(x_6);
lean_dec(x_9);
lean_dec_ref(x_2);
x_118 = 0;
x_119 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_117, x_3, x_118, x_13);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_4);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
lean_dec_ref(x_119);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_4);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_10; lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0;
x_20 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1;
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_box(0);
x_23 = l_String_splitOnAux(x_2, x_19, x_21, x_21, x_21, x_22);
if (lean_obj_tag(x_23) == 0)
{
goto block_9;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec_ref(x_23);
x_10 = x_25;
goto block_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec_ref(x_23);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec_ref(x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_57 = lean_string_utf8_byte_size(x_26);
lean_inc(x_57);
lean_inc(x_26);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_26);
lean_ctor_set(x_58, 1, x_21);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = l_Substring_nextn(x_58, x_59, x_21);
lean_dec_ref(x_58);
lean_inc(x_60);
lean_inc(x_26);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_26);
lean_ctor_set(x_61, 1, x_21);
lean_ctor_set(x_61, 2, x_60);
x_62 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__2;
x_63 = l_Substring_beq(x_61, x_62);
if (x_63 == 0)
{
lean_dec(x_60);
lean_dec(x_57);
x_29 = x_26;
goto block_56;
}
else
{
lean_object* x_64; 
x_64 = lean_string_utf8_extract(x_26, x_60, x_57);
lean_dec(x_57);
lean_dec(x_60);
lean_dec(x_26);
x_29 = x_64;
goto block_56;
}
}
else
{
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec(x_26);
goto block_9;
}
block_56:
{
lean_object* x_30; 
x_30 = l_Lake_parsePackageSpec(x_1, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_27);
lean_dec_ref(x_2);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = l_Lake_stringToLegalOrSimpleName(x_27);
x_37 = l_Lake_Package_findTargetDecl_x3f(x_36, x_35);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_free_object(x_30);
lean_dec(x_35);
goto block_5;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lake_LeanExe_keyword;
x_43 = lean_name_eq(x_40, x_42);
lean_dec(x_40);
if (x_43 == 0)
{
lean_dec(x_41);
lean_dec(x_39);
lean_free_object(x_30);
lean_dec(x_35);
goto block_5;
}
else
{
lean_object* x_44; 
lean_dec_ref(x_2);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set(x_30, 0, x_44);
return x_30;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
lean_inc(x_45);
lean_dec(x_30);
x_46 = l_Lake_stringToLegalOrSimpleName(x_27);
x_47 = l_Lake_Package_findTargetDecl_x3f(x_46, x_45);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_dec(x_45);
goto block_5;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 3);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l_Lake_LeanExe_keyword;
x_53 = lean_name_eq(x_50, x_52);
lean_dec(x_50);
if (x_53 == 0)
{
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_45);
goto block_5;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_2);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 2, x_51);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
}
}
}
}
else
{
lean_inc_ref(x_2);
x_10 = x_2;
goto block_18;
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
block_9:
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 47;
x_7 = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set_uint32(x_7, sizeof(void*)*1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_18:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lake_stringToLegalOrSimpleName(x_10);
x_12 = l_Lake_Workspace_findLeanExe_x3f(x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec_ref(x_2);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
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
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_parseTargetSpec___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static uint8_t _init_l_Lake_parseTargetSpec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0;
x_2 = l_Lake_parseTargetSpec___closed__0;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_13; uint8_t x_14; 
x_13 = l_Lake_parseTargetSpec___closed__0;
x_14 = l_Lake_parseTargetSpec___closed__1;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_box(0);
x_17 = l_String_splitOnAux(x_2, x_13, x_15, x_15, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_1);
x_8 = x_3;
goto block_12;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
x_4 = x_19;
goto block_7;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 1);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_2);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec_ref(x_17);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec_ref(x_18);
x_23 = l_String_toName(x_22);
x_24 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(x_1, x_21, x_23, x_3);
return x_24;
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_1);
x_8 = x_3;
goto block_12;
}
}
}
}
else
{
x_4 = x_2;
goto block_7;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(x_1, x_4, x_5, x_3);
return x_6;
}
block_12:
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 58;
x_10 = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set_uint32(x_10, sizeof(void*)*1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lake_parseTargetSpecs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_8 = l_Lake_parseTargetSpec(x_1, x_6, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Array_append___redArg(x_3, x_9);
lean_dec(x_9);
x_2 = x_7;
x_3 = x_11;
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lake_parseTargetSpecs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___Lake_parseTargetSpecs_spec__0___redArg(x_1, x_3, x_4, x_6);
return x_7;
}
}
static lean_object* _init_l_Lake_parseTargetSpecs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lake_parseTargetSpecs___closed__0;
lean_inc_ref(x_1);
x_5 = l_List_forIn_x27_loop___at___Lake_parseTargetSpecs_spec__0___redArg(x_1, x_2, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = l_Array_isEmpty___redArg(x_6);
lean_dec(x_6);
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_1);
return x_5;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
x_13 = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(x_1, x_12);
lean_dec_ref(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
x_17 = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(x_1, x_16);
lean_dec_ref(x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec_ref(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
}
}
else
{
lean_dec_ref(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lake_parseTargetSpecs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___Lake_parseTargetSpecs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Lake_CLI_Error(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Build(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_CLI_Error(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Workspace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Infos(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Register(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_buildSpecs___closed__0 = _init_l_Lake_buildSpecs___closed__0();
lean_mark_persistent(l_Lake_buildSpecs___closed__0);
l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0 = _init_l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0);
l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1 = _init_l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lake_formatQuery___at_____private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1);
l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1 = _init_l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1);
l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__2 = _init_l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__2);
l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__1 = _init_l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__1);
l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__2 = _init_l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__2);
l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__1 = _init_l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__1);
l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__2 = _init_l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__2);
l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__1 = _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__1);
l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__2 = _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__2);
l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__3 = _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__3);
l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__4 = _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__4);
l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__5 = _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__5();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__5);
l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1 = _init_l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1);
l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1 = _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1();
l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2 = _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2);
l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__3 = _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__3);
l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__4 = _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__4);
l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1 = _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1);
l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__2 = _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__2);
l_Lake_parseTargetSpec___closed__0 = _init_l_Lake_parseTargetSpec___closed__0();
lean_mark_persistent(l_Lake_parseTargetSpec___closed__0);
l_Lake_parseTargetSpec___closed__1 = _init_l_Lake_parseTargetSpec___closed__1();
l_Lake_parseTargetSpecs___closed__0 = _init_l_Lake_parseTargetSpecs___closed__0();
lean_mark_persistent(l_Lake_parseTargetSpecs___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
