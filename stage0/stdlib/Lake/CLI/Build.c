// Lean compiler output
// Module: Lake.CLI.Build
// Imports: public import Lake.CLI.Error public import Lake.Config.Workspace import Lake.Config.Monad import Lake.Build.Infos import Lake.Build.Job.Monad public import Lake.Build.Job.Register import Lake.Util.IO import Init.Data.String.Search
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
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__3;
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_mkBuildSpec___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_parseTargetSpec___closed__0;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0;
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_BuildInfo_key(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__2;
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_sharedFacet;
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_resolveLibTarget_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lake_Package_keyword;
static lean_object* l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(uint8_t);
lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__1;
LEAN_EXPORT lean_object* l_Lake_querySpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__0;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__4;
lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__2;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_exeFacet;
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lake_Package_findTargetModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveExeTarget_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Module_leanArtsFacet;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
static lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1;
static lean_object* l_Lake_parseTargetSpecs___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1;
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_parseTargetSpec_spec__0___boxed(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__2;
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveExeTarget_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lake_BuildKey_toSimpleString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(uint8_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__0;
static lean_object* l_Lake_parsePackageSpec___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_parseTargetSpec_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_mkBuildSpec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__3;
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_querySpecs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(uint8_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveLibTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lam__0(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_resolveLibTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_Lake_Job_mixArray___redArg(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec(lean_object*, lean_object*);
lean_object* l_String_Slice_toName(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_staticFacet;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___boxed(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__0;
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___boxed(lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1;
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_formatQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildSpecs___closed__0;
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
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_mkConfigBuildSpec___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
lean_inc_ref(x_6);
lean_inc_ref(x_9);
x_10 = lean_apply_7(x_2, x_9, x_3, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 2);
x_17 = lean_string_utf8_byte_size(x_16);
lean_dec_ref(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_free_object(x_11);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
return x_10;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_10, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_6, 3);
lean_inc(x_23);
lean_dec_ref(x_6);
x_24 = lean_st_ref_take(x_23);
x_25 = l_Lake_BuildInfo_key(x_9);
x_26 = l_Lake_BuildKey_toSimpleString(x_25);
x_27 = 0;
lean_ctor_set(x_11, 2, x_26);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_27);
lean_inc_ref(x_11);
x_28 = l_Lake_Job_toOpaque___redArg(x_11);
x_29 = lean_array_push(x_24, x_28);
x_30 = lean_st_ref_set(x_23, x_29);
lean_dec(x_23);
x_31 = l_Lake_Job_renew___redArg(x_11);
lean_ctor_set(x_10, 0, x_31);
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_10);
x_32 = lean_ctor_get(x_6, 3);
lean_inc(x_32);
lean_dec_ref(x_6);
x_33 = lean_st_ref_take(x_32);
x_34 = l_Lake_BuildInfo_key(x_9);
x_35 = l_Lake_BuildKey_toSimpleString(x_34);
x_36 = 0;
lean_ctor_set(x_11, 2, x_35);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_36);
lean_inc_ref(x_11);
x_37 = l_Lake_Job_toOpaque___redArg(x_11);
x_38 = lean_array_push(x_33, x_37);
x_39 = lean_st_ref_set(x_32, x_38);
lean_dec(x_32);
x_40 = l_Lake_Job_renew___redArg(x_11);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_12);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
x_44 = lean_ctor_get(x_11, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_45 = lean_string_utf8_byte_size(x_44);
lean_dec_ref(x_44);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_eq(x_45, x_46);
if (x_47 == 0)
{
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_12);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
return x_10;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_48 = x_10;
} else {
 lean_dec_ref(x_10);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_6, 3);
lean_inc(x_49);
lean_dec_ref(x_6);
x_50 = lean_st_ref_take(x_49);
x_51 = l_Lake_BuildInfo_key(x_9);
x_52 = l_Lake_BuildKey_toSimpleString(x_51);
x_53 = 0;
x_54 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_54, 0, x_42);
lean_ctor_set(x_54, 1, x_43);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_53);
lean_inc_ref(x_54);
x_55 = l_Lake_Job_toOpaque___redArg(x_54);
x_56 = lean_array_push(x_50, x_55);
x_57 = lean_st_ref_set(x_49, x_56);
lean_dec(x_49);
x_58 = l_Lake_Job_renew___redArg(x_54);
if (lean_is_scalar(x_48)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_48;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_12);
return x_59;
}
}
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_BuildSpec_fetch(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
lean_inc_ref(x_6);
lean_inc_ref(x_15);
x_16 = lean_apply_7(x_2, x_15, x_3, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 2);
x_22 = lean_string_utf8_byte_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_dec_ref(x_15);
lean_dec_ref(x_6);
x_9 = x_17;
x_10 = x_18;
x_11 = lean_box(0);
goto block_14;
}
else
{
uint8_t x_25; 
lean_inc(x_20);
lean_inc_ref(x_19);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_17, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_17, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_17, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_6, 3);
lean_inc(x_29);
lean_dec_ref(x_6);
x_30 = lean_st_ref_take(x_29);
x_31 = l_Lake_BuildInfo_key(x_15);
x_32 = l_Lake_BuildKey_toSimpleString(x_31);
x_33 = 0;
lean_ctor_set(x_17, 2, x_32);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_33);
lean_inc_ref(x_17);
x_34 = l_Lake_Job_toOpaque___redArg(x_17);
x_35 = lean_array_push(x_30, x_34);
x_36 = lean_st_ref_set(x_29, x_35);
lean_dec(x_29);
x_37 = l_Lake_Job_renew___redArg(x_17);
x_9 = x_37;
x_10 = x_18;
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_17);
x_38 = lean_ctor_get(x_6, 3);
lean_inc(x_38);
lean_dec_ref(x_6);
x_39 = lean_st_ref_take(x_38);
x_40 = l_Lake_BuildInfo_key(x_15);
x_41 = l_Lake_BuildKey_toSimpleString(x_40);
x_42 = 0;
x_43 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_43, 0, x_19);
lean_ctor_set(x_43, 1, x_20);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_42);
lean_inc_ref(x_43);
x_44 = l_Lake_Job_toOpaque___redArg(x_43);
x_45 = lean_array_push(x_39, x_44);
x_46 = lean_st_ref_set(x_38, x_45);
lean_dec(x_38);
x_47 = l_Lake_Job_renew___redArg(x_43);
x_9 = x_47;
x_10 = x_18;
x_11 = lean_box(0);
goto block_14;
}
}
}
else
{
lean_dec_ref(x_15);
lean_dec_ref(x_6);
return x_16;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lake_Job_toOpaque___redArg(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_BuildSpec_build(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
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
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lake_BuildSpec_query___lam__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
lean_inc_ref(x_10);
x_12 = l_Lake_BuildInfo_key(x_10);
lean_inc_ref(x_7);
x_13 = lean_apply_7(x_3, x_10, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 2);
x_19 = lean_ctor_get(x_15, 1);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_box(x_2);
x_22 = lean_alloc_closure((void*)(l_Lake_BuildSpec_query___lam__0___boxed), 3, 2);
lean_closure_set(x_22, 0, x_11);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = 0;
x_25 = lean_task_map(x_22, x_17, x_23, x_24);
x_26 = lean_string_utf8_byte_size(x_18);
x_27 = lean_nat_dec_eq(x_26, x_23);
if (x_27 == 0)
{
lean_dec_ref(x_12);
lean_dec_ref(x_7);
lean_ctor_set(x_15, 1, x_20);
lean_ctor_set(x_15, 0, x_25);
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_18);
x_28 = lean_ctor_get(x_7, 3);
lean_inc(x_28);
lean_dec_ref(x_7);
x_29 = lean_st_ref_take(x_28);
x_30 = l_Lake_BuildKey_toSimpleString(x_12);
lean_ctor_set(x_15, 2, x_30);
lean_ctor_set(x_15, 1, x_20);
lean_ctor_set(x_15, 0, x_25);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_24);
lean_inc_ref(x_15);
x_31 = l_Lake_Job_toOpaque___redArg(x_15);
x_32 = lean_array_push(x_29, x_31);
x_33 = lean_st_ref_set(x_28, x_32);
lean_dec(x_28);
x_34 = l_Lake_Job_renew___redArg(x_15);
lean_ctor_set(x_13, 0, x_34);
return x_13;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 2);
x_37 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_38 = lean_box(0);
x_39 = lean_box(x_2);
x_40 = lean_alloc_closure((void*)(l_Lake_BuildSpec_query___lam__0___boxed), 3, 2);
lean_closure_set(x_40, 0, x_11);
lean_closure_set(x_40, 1, x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = 0;
x_43 = lean_task_map(x_40, x_35, x_41, x_42);
x_44 = lean_string_utf8_byte_size(x_36);
x_45 = lean_nat_dec_eq(x_44, x_41);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec_ref(x_12);
lean_dec_ref(x_7);
x_46 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_37);
lean_ctor_set(x_13, 0, x_46);
return x_13;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_36);
x_47 = lean_ctor_get(x_7, 3);
lean_inc(x_47);
lean_dec_ref(x_7);
x_48 = lean_st_ref_take(x_47);
x_49 = l_Lake_BuildKey_toSimpleString(x_12);
x_50 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_38);
lean_ctor_set(x_50, 2, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_42);
lean_inc_ref(x_50);
x_51 = l_Lake_Job_toOpaque___redArg(x_50);
x_52 = lean_array_push(x_48, x_51);
x_53 = lean_st_ref_set(x_47, x_52);
lean_dec(x_47);
x_54 = l_Lake_Job_renew___redArg(x_50);
lean_ctor_set(x_13, 0, x_54);
return x_13;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_ctor_get(x_55, 0);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_55, 2);
lean_inc_ref(x_58);
x_59 = lean_ctor_get_uint8(x_55, sizeof(void*)*3);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 x_60 = x_55;
} else {
 lean_dec_ref(x_55);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
x_62 = lean_box(x_2);
x_63 = lean_alloc_closure((void*)(l_Lake_BuildSpec_query___lam__0___boxed), 3, 2);
lean_closure_set(x_63, 0, x_11);
lean_closure_set(x_63, 1, x_62);
x_64 = lean_unsigned_to_nat(0u);
x_65 = 0;
x_66 = lean_task_map(x_63, x_57, x_64, x_65);
x_67 = lean_string_utf8_byte_size(x_58);
x_68 = lean_nat_dec_eq(x_67, x_64);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_12);
lean_dec_ref(x_7);
if (lean_is_scalar(x_60)) {
 x_69 = lean_alloc_ctor(0, 3, 1);
} else {
 x_69 = x_60;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_58);
lean_ctor_set_uint8(x_69, sizeof(void*)*3, x_59);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_56);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_58);
x_71 = lean_ctor_get(x_7, 3);
lean_inc(x_71);
lean_dec_ref(x_7);
x_72 = lean_st_ref_take(x_71);
x_73 = l_Lake_BuildKey_toSimpleString(x_12);
if (lean_is_scalar(x_60)) {
 x_74 = lean_alloc_ctor(0, 3, 1);
} else {
 x_74 = x_60;
}
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_61);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*3, x_65);
lean_inc_ref(x_74);
x_75 = l_Lake_Job_toOpaque___redArg(x_74);
x_76 = lean_array_push(x_72, x_75);
x_77 = lean_st_ref_set(x_71, x_76);
lean_dec(x_71);
x_78 = l_Lake_Job_renew___redArg(x_74);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_56);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
x_80 = !lean_is_exclusive(x_13);
if (x_80 == 0)
{
return x_13;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_13, 0);
x_82 = lean_ctor_get(x_13, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_13);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_BuildSpec_query(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
lean_inc_ref(x_4);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_14);
x_15 = lean_apply_7(x_4, x_14, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_32; uint8_t x_33; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_16, 2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_uset(x_3, x_2, x_21);
x_32 = lean_string_utf8_byte_size(x_20);
x_33 = lean_nat_dec_eq(x_32, x_21);
if (x_33 == 0)
{
lean_dec_ref(x_14);
x_23 = x_16;
x_24 = x_17;
x_25 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_34; 
lean_inc(x_19);
lean_inc_ref(x_18);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_16, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_16, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_16, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_8, 3);
x_39 = lean_st_ref_take(x_38);
x_40 = l_Lake_BuildInfo_key(x_14);
x_41 = l_Lake_BuildKey_toSimpleString(x_40);
x_42 = 0;
lean_ctor_set(x_16, 2, x_41);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_42);
lean_inc_ref(x_16);
x_43 = l_Lake_Job_toOpaque___redArg(x_16);
x_44 = lean_array_push(x_39, x_43);
x_45 = lean_st_ref_set(x_38, x_44);
x_46 = l_Lake_Job_renew___redArg(x_16);
x_23 = x_46;
x_24 = x_17;
x_25 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_16);
x_47 = lean_ctor_get(x_8, 3);
x_48 = lean_st_ref_take(x_47);
x_49 = l_Lake_BuildInfo_key(x_14);
x_50 = l_Lake_BuildKey_toSimpleString(x_49);
x_51 = 0;
x_52 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_52, 0, x_18);
lean_ctor_set(x_52, 1, x_19);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_51);
lean_inc_ref(x_52);
x_53 = l_Lake_Job_toOpaque___redArg(x_52);
x_54 = lean_array_push(x_48, x_53);
x_55 = lean_st_ref_set(x_47, x_54);
x_56 = l_Lake_Job_renew___redArg(x_52);
x_23 = x_56;
x_24 = x_17;
x_25 = lean_box(0);
goto block_31;
}
}
block_31:
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_26 = l_Lake_Job_toOpaque___redArg(x_23);
x_27 = 1;
x_28 = lean_usize_add(x_2, x_27);
x_29 = lean_array_uset(x_22, x_2, x_26);
x_2 = x_28;
x_3 = x_29;
x_9 = x_24;
goto _start;
}
}
else
{
uint8_t x_57; 
lean_dec_ref(x_14);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_57 = !lean_is_exclusive(x_15);
if (x_57 == 0)
{
return x_15;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_15, 0);
x_59 = lean_ctor_get(x_15, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_15);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
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
LEAN_EXPORT lean_object* l_Lake_buildSpecs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(x_9, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lake_buildSpecs___closed__0;
x_15 = l_Lake_Job_mixArray___redArg(x_13, x_14);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = l_Lake_buildSpecs___closed__0;
x_19 = l_Lake_Job_mixArray___redArg(x_16, x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSpecs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_buildSpecs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
lean_dec(x_14);
lean_inc_ref(x_15);
x_17 = l_Lake_BuildInfo_key(x_15);
lean_inc_ref(x_5);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = lean_apply_7(x_5, x_15, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 2);
x_24 = lean_ctor_get(x_19, 1);
lean_dec(x_24);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_uset(x_4, x_3, x_25);
x_35 = lean_box(0);
x_36 = lean_box(x_1);
x_37 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(x_37, 0, x_16);
lean_closure_set(x_37, 1, x_36);
x_38 = 0;
x_39 = lean_task_map(x_37, x_22, x_25, x_38);
x_40 = lean_string_utf8_byte_size(x_23);
x_41 = lean_nat_dec_eq(x_40, x_25);
if (x_41 == 0)
{
lean_dec_ref(x_17);
lean_ctor_set(x_19, 1, x_35);
lean_ctor_set(x_19, 0, x_39);
x_27 = x_19;
x_28 = x_20;
x_29 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_23);
x_42 = lean_ctor_get(x_9, 3);
x_43 = lean_st_ref_take(x_42);
x_44 = l_Lake_BuildKey_toSimpleString(x_17);
lean_ctor_set(x_19, 2, x_44);
lean_ctor_set(x_19, 1, x_35);
lean_ctor_set(x_19, 0, x_39);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_38);
lean_inc_ref(x_19);
x_45 = l_Lake_Job_toOpaque___redArg(x_19);
x_46 = lean_array_push(x_43, x_45);
x_47 = lean_st_ref_set(x_42, x_46);
x_48 = l_Lake_Job_renew___redArg(x_19);
x_27 = x_48;
x_28 = x_20;
x_29 = lean_box(0);
goto block_34;
}
block_34:
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_32 = lean_array_uset(x_26, x_3, x_27);
x_3 = x_31;
x_4 = x_32;
x_10 = x_28;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 2);
x_51 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_array_uset(x_4, x_3, x_52);
x_62 = lean_box(0);
x_63 = lean_box(x_1);
x_64 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(x_64, 0, x_16);
lean_closure_set(x_64, 1, x_63);
x_65 = 0;
x_66 = lean_task_map(x_64, x_49, x_52, x_65);
x_67 = lean_string_utf8_byte_size(x_50);
x_68 = lean_nat_dec_eq(x_67, x_52);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec_ref(x_17);
x_69 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_62);
lean_ctor_set(x_69, 2, x_50);
lean_ctor_set_uint8(x_69, sizeof(void*)*3, x_51);
x_54 = x_69;
x_55 = x_20;
x_56 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_50);
x_70 = lean_ctor_get(x_9, 3);
x_71 = lean_st_ref_take(x_70);
x_72 = l_Lake_BuildKey_toSimpleString(x_17);
x_73 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_62);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*3, x_65);
lean_inc_ref(x_73);
x_74 = l_Lake_Job_toOpaque___redArg(x_73);
x_75 = lean_array_push(x_71, x_74);
x_76 = lean_st_ref_set(x_70, x_75);
x_77 = l_Lake_Job_renew___redArg(x_73);
x_54 = x_77;
x_55 = x_20;
x_56 = lean_box(0);
goto block_61;
}
block_61:
{
size_t x_57; size_t x_58; lean_object* x_59; 
x_57 = 1;
x_58 = lean_usize_add(x_3, x_57);
x_59 = lean_array_uset(x_53, x_3, x_54);
x_3 = x_58;
x_4 = x_59;
x_10 = x_55;
goto _start;
}
}
}
else
{
uint8_t x_78; 
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_78 = !lean_is_exclusive(x_18);
if (x_78 == 0)
{
return x_18;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_18, 0);
x_80 = lean_ctor_get(x_18, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_18);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_querySpecs(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_array_size(x_1);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(x_2, x_10, x_11, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lake_buildSpecs___closed__0;
x_16 = l_Lake_Job_collectArray___redArg(x_14, x_15);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = l_Lake_buildSpecs___closed__0;
x_20 = l_Lake_Job_collectArray___redArg(x_17, x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_querySpecs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_querySpecs(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_inc_ref(x_7);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_uget(x_4, x_6);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_name_eq(x_10, x_1);
lean_dec(x_10);
if (x_11 == 0)
{
size_t x_12; size_t x_13; 
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_6, x_12);
{
size_t _tmp_5 = x_13;
lean_object* _tmp_6 = x_2;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_9);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lake_parsePackageSpec___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_string_utf8_byte_size(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_2);
x_10 = l_Lake_stringToLegalOrSimpleName(x_2);
x_11 = lean_box(0);
x_12 = l_Lake_parsePackageSpec___closed__0;
x_13 = lean_array_size(x_9);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(x_10, x_12, x_11, x_9, x_13, x_14, x_12);
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
if (lean_obj_tag(x_16) == 0)
{
goto block_5;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
if (lean_obj_tag(x_17) == 0)
{
goto block_5;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_2);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
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
static lean_object* _init_l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Json_compress(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(x_1);
return x_3;
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
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0___boxed), 2, 0);
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
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_10, 2);
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*4);
x_15 = lean_ctor_get(x_11, 3);
lean_inc_ref(x_15);
lean_dec(x_11);
lean_inc(x_12);
lean_inc(x_13);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_12);
x_17 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_6);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_14);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_20, 2);
x_24 = lean_ctor_get_uint8(x_21, sizeof(void*)*4);
x_25 = lean_ctor_get(x_21, 3);
lean_inc_ref(x_25);
lean_dec(x_21);
lean_inc(x_22);
lean_inc(x_23);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_2);
lean_ctor_set(x_27, 3, x_6);
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_24);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
lean_dec_ref(x_2);
x_30 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0;
x_31 = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_3);
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_33, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_34, 2);
x_37 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1;
x_38 = l_Lake_Module_leanArtsFacet;
lean_inc(x_35);
lean_inc(x_36);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_35);
x_40 = l_Lake_Module_keyword;
x_41 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_2);
lean_ctor_set(x_41, 3, x_38);
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_4);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
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
if (lean_obj_tag(x_14) == 1)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
x_19 = lean_ctor_get(x_16, 3);
lean_inc_ref(x_19);
lean_dec(x_16);
lean_inc(x_6);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_8);
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_6);
if (lean_is_scalar(x_9)) {
 x_22 = lean_alloc_ctor(1, 4, 0);
} else {
 x_22 = x_9;
 lean_ctor_set_tag(x_22, 1);
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_13);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_18);
x_24 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_25 = lean_array_push(x_24, x_23);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_26, sizeof(void*)*4);
x_29 = lean_ctor_get(x_26, 3);
lean_inc_ref(x_29);
lean_dec(x_26);
lean_inc(x_6);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 2, x_8);
x_31 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_6);
if (lean_is_scalar(x_9)) {
 x_32 = lean_alloc_ctor(1, 4, 0);
} else {
 x_32 = x_9;
 lean_ctor_set_tag(x_32, 1);
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_13);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_28);
x_34 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_35 = lean_array_push(x_34, x_33);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_2);
x_37 = l_Lean_Name_toString(x_7, x_11);
x_38 = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_12);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
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
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("library", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Workspace_findLibraryFacetConfig_x3f(x_3, x_1);
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 2);
x_10 = lean_ctor_get_uint8(x_7, sizeof(void*)*4);
x_11 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_11);
lean_dec(x_7);
lean_inc(x_8);
lean_inc(x_9);
x_12 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
x_13 = l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__1;
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_2);
lean_ctor_set(x_14, 3, x_3);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_10);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_16, 2);
x_20 = lean_ctor_get_uint8(x_17, sizeof(void*)*4);
x_21 = lean_ctor_get(x_17, 3);
lean_inc_ref(x_21);
lean_dec(x_17);
lean_inc(x_18);
lean_inc(x_19);
x_22 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_18);
x_23 = l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__1;
x_24 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_2);
lean_ctor_set(x_24, 3, x_3);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
lean_dec_ref(x_2);
x_27 = l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__2;
x_28 = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_resolveLibTarget_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_resolveLibTarget_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_resolveLibTarget_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_1);
return x_8;
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
x_5 = l___private_Lake_CLI_Build_0__Lake_resolveLibTarget_resolveFacet___closed__1;
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
x_23 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_resolveLibTarget_spec__0(x_1, x_2, x_21, x_22, x_20);
return x_23;
}
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
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveExeTarget_spec__0(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveExeTarget_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveExeTarget_spec__0(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveExeTarget_spec__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("executable", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exe", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExeTarget(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_18; 
x_3 = l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__0;
x_18 = l_Lean_Name_isAnonymous(x_2);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__3;
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
lean_dec_ref(x_1);
x_5 = l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__1;
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
x_10 = lean_ctor_get(x_8, 2);
x_11 = l_Lake_LeanExe_exeFacet;
lean_inc(x_9);
lean_inc(x_10);
x_12 = lean_alloc_ctor(3, 2, 0);
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
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shared", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("external library", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("static", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_29; 
x_3 = l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__0;
x_29 = l_Lean_Name_isAnonymous(x_2);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__4;
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
x_5 = l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__1;
x_6 = lean_name_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_1);
x_7 = l___private_Lake_CLI_Build_0__Lake_resolveExternLibTarget___closed__2;
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
x_12 = lean_ctor_get(x_10, 2);
x_13 = l_Lake_ExternLib_sharedFacet;
lean_inc(x_11);
lean_inc(x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
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
x_21 = lean_ctor_get(x_19, 2);
x_22 = l_Lake_ExternLib_staticFacet;
lean_inc(x_20);
lean_inc(x_21);
x_23 = lean_alloc_ctor(3, 2, 0);
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
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(x_1, x_2, x_3, x_6, x_4);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
lean_inc_ref(x_2);
lean_inc(x_3);
x_8 = l_Lake_Package_findTargetModule_x3f(x_3, x_2);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
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
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_17 = lean_array_push(x_16, x_15);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_20 = lean_array_push(x_19, x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_4);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec_ref(x_2);
x_23 = 0;
x_24 = l_Lean_Name_toString(x_3, x_23);
x_25 = lean_alloc_ctor(17, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
x_3 = lean_ctor_get(x_2, 15);
lean_inc_ref(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0;
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
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
if (x_7 == 0)
{
lean_object* x_10; 
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
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(x_1, x_2, x_3, x_11, x_12, x_5);
lean_dec_ref(x_3);
return x_13;
}
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_6);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(x_1, x_2, x_3, x_14, x_15, x_5);
lean_dec_ref(x_3);
return x_16;
}
}
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
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get_uint8(x_9, sizeof(void*)*4);
x_12 = lean_ctor_get(x_9, 3);
lean_inc_ref(x_12);
lean_dec(x_9);
lean_inc(x_10);
lean_ctor_set(x_7, 0, x_10);
x_13 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_13, 3, x_6);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_11);
x_15 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_16 = lean_array_push(x_15, x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
x_21 = lean_ctor_get(x_18, 3);
lean_inc_ref(x_21);
lean_dec(x_18);
lean_inc(x_19);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set(x_23, 2, x_2);
lean_ctor_set(x_23, 3, x_6);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_20);
x_25 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_26 = lean_array_push(x_25, x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_7);
lean_dec_ref(x_2);
x_28 = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0;
x_29 = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
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
lean_object* x_21; 
x_21 = l_Lake_Workspace_findTargetDecl_x3f(x_2, x_1);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(x_1, x_23, x_2, x_24, x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_1, 4);
x_27 = lean_box(0);
x_28 = l_Lake_parsePackageSpec___closed__0;
x_29 = lean_array_size(x_26);
x_30 = 0;
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(x_2, x_28, x_27, x_26, x_29, x_30, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
if (lean_obj_tag(x_32) == 0)
{
goto block_20;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(x_1, x_34, x_3);
return x_35;
}
else
{
lean_dec(x_33);
goto block_20;
}
}
}
block_20:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lake_Workspace_findTargetModule_x3f(x_2, x_1);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_13 = lean_array_push(x_12, x_11);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_16 = lean_array_push(x_15, x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(x_18, 0, x_2);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
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
static lean_object* _init_l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_nat_sub(x_16, x_15);
x_18 = lean_nat_dec_eq(x_14, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_string_utf8_next_fast(x_3, x_14);
x_20 = lean_string_utf8_get_fast(x_3, x_14);
x_21 = lean_uint32_dec_eq(x_20, x_1);
if (x_21 == 0)
{
lean_dec(x_14);
lean_ctor_set(x_5, 1, x_19);
goto _start;
}
else
{
lean_object* x_23; 
lean_inc_ref(x_2);
x_23 = l_String_Slice_slice_x21(x_2, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
lean_ctor_set(x_5, 1, x_19);
lean_ctor_set(x_5, 0, x_19);
x_7 = x_5;
x_8 = x_23;
goto block_11;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_5);
lean_dec(x_14);
lean_inc(x_4);
lean_inc_ref(x_3);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_4);
x_25 = lean_box(1);
x_7 = x_25;
x_8 = x_24;
goto block_11;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_nat_sub(x_29, x_28);
x_31 = lean_nat_dec_eq(x_27, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint32_t x_33; uint8_t x_34; 
x_32 = lean_string_utf8_next_fast(x_3, x_27);
x_33 = lean_string_utf8_get_fast(x_3, x_27);
x_34 = lean_uint32_dec_eq(x_33, x_1);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_27);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_32);
x_5 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_inc_ref(x_2);
x_37 = l_String_Slice_slice_x21(x_2, x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_32);
x_7 = x_38;
x_8 = x_37;
goto block_11;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_27);
lean_inc(x_4);
lean_inc_ref(x_3);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_4);
x_40 = lean_box(1);
x_7 = x_40;
x_8 = x_39;
goto block_11;
}
}
}
else
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
block_11:
{
lean_object* x_9; 
x_9 = lean_array_push(x_6, x_8);
x_5 = x_7;
x_6 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("+", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5) {
_start:
{
uint32_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = 47;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_string_utf8_byte_size(x_2);
lean_inc_ref(x_2);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(x_15);
x_17 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0;
lean_inc_ref(x_2);
x_18 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(x_12, x_15, x_2, x_14, x_16, x_17);
x_19 = lean_array_to_list(x_18);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec_ref(x_2);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 2);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_nat_sub(x_24, x_23);
x_26 = lean_nat_dec_eq(x_25, x_13);
lean_dec(x_25);
if (x_26 == 0)
{
if (x_5 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_string_utf8_extract(x_22, x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
x_28 = l_Lake_stringToLegalOrSimpleName(x_27);
x_29 = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(x_1, x_28, x_3);
lean_dec_ref(x_1);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_string_utf8_extract(x_22, x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
x_31 = l_Lake_parsePackageSpec(x_1, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec_ref(x_31);
x_36 = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(x_1, x_35, x_3);
lean_dec_ref(x_1);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
x_37 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_37);
x_38 = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(x_1, x_37, x_3);
lean_dec_ref(x_1);
return x_38;
}
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_20, 1);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_2);
x_40 = lean_ctor_get(x_19, 0);
lean_inc(x_40);
lean_dec_ref(x_19);
x_41 = lean_ctor_get(x_20, 0);
lean_inc(x_41);
lean_dec_ref(x_20);
x_42 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_string_utf8_extract(x_42, x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
x_46 = l_Lake_parsePackageSpec(x_1, x_45);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_3);
lean_dec_ref(x_1);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_81; uint8_t x_82; 
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_41, 2);
lean_inc(x_54);
x_81 = lean_nat_sub(x_54, x_53);
x_82 = lean_nat_dec_eq(x_81, x_13);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1;
x_84 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2;
x_85 = lean_nat_dec_le(x_84, x_81);
lean_dec(x_81);
if (x_85 == 0)
{
x_55 = x_82;
goto block_80;
}
else
{
uint8_t x_86; 
x_86 = lean_string_memcmp(x_52, x_83, x_53, x_13, x_84);
x_55 = x_86;
goto block_80;
}
}
else
{
lean_object* x_87; 
lean_dec(x_81);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec(x_41);
x_87 = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(x_1, x_50, x_3);
lean_dec_ref(x_1);
return x_87;
}
block_80:
{
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
lean_dec(x_41);
x_56 = lean_string_utf8_extract(x_52, x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
x_57 = l_Lake_stringToLegalOrSimpleName(x_56);
x_58 = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(x_1, x_50, x_57, x_3);
lean_dec_ref(x_1);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_unsigned_to_nat(1u);
x_60 = l_String_Slice_Pos_nextn(x_41, x_13, x_59);
lean_dec(x_41);
x_61 = lean_nat_add(x_53, x_60);
lean_dec(x_60);
lean_dec(x_53);
x_62 = lean_string_utf8_extract(x_52, x_61, x_54);
lean_dec(x_54);
lean_dec(x_61);
lean_dec_ref(x_52);
x_63 = l_String_toName(x_62);
lean_inc(x_63);
x_64 = l_Lake_Package_findTargetModule_x3f(x_63, x_50);
if (lean_obj_tag(x_64) == 1)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_63);
lean_dec(x_51);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_65, x_3);
lean_dec_ref(x_1);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
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
x_72 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_73 = lean_array_push(x_72, x_71);
lean_ctor_set(x_66, 0, x_73);
return x_66;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
lean_dec(x_66);
x_75 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_76 = lean_array_push(x_75, x_74);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_64);
lean_dec(x_3);
lean_dec_ref(x_1);
x_78 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_78, 0, x_63);
if (lean_is_scalar(x_51)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_51;
 lean_ctor_set_tag(x_79, 0);
}
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
}
}
else
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_11;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_11;
}
block_11:
{
if (x_4 == 0)
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
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(x_1, x_2, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint32_t x_10; lean_object* x_11; 
x_10 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_11 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
return x_11;
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_48; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0;
x_79 = lean_string_utf8_byte_size(x_2);
x_80 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1;
x_81 = lean_nat_dec_le(x_80, x_79);
if (x_81 == 0)
{
x_48 = x_81;
goto block_77;
}
else
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_string_memcmp(x_2, x_78, x_82, x_82, x_80);
if (x_83 == 0)
{
x_48 = x_83;
goto block_77;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_84 = lean_unsigned_to_nat(1u);
lean_inc_ref(x_2);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_2);
lean_ctor_set(x_85, 1, x_82);
lean_ctor_set(x_85, 2, x_79);
x_86 = l_String_Slice_Pos_nextn(x_85, x_82, x_84);
lean_dec_ref(x_85);
x_87 = lean_string_utf8_extract(x_2, x_86, x_79);
lean_dec(x_86);
lean_dec_ref(x_2);
x_88 = 0;
x_89 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_87, x_3, x_88, x_83);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_ctor_set_tag(x_89, 1);
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_ctor(1, 1, 0);
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
lean_ctor_set_tag(x_89, 0);
return x_89;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
lean_dec(x_89);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
}
block_47:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc_ref(x_2);
x_7 = l_Lake_resolvePath(x_2);
x_8 = lean_string_utf8_byte_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_System_FilePath_isDir(x_7);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lake_Workspace_findModuleBySrc_x3f(x_7, x_1);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_13, x_3);
lean_dec_ref(x_1);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 1);
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_21 = lean_array_push(x_20, x_19);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_24 = lean_array_push(x_23, x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_12);
x_26 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_2, x_3, x_5, x_11);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 1);
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_ctor_set_tag(x_26, 0);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; 
lean_dec_ref(x_7);
x_33 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_2, x_3, x_6, x_6);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_ctor_set_tag(x_33, 1);
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(1, 1, 0);
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
lean_ctor_set_tag(x_33, 0);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec_ref(x_7);
x_40 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(x_1, x_2, x_3, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_ctor_set_tag(x_40, 1);
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_ctor_set_tag(x_40, 0);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
block_77:
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = 1;
x_50 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1;
x_51 = lean_string_utf8_byte_size(x_2);
x_52 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2;
x_53 = lean_nat_dec_le(x_52, x_51);
if (x_53 == 0)
{
x_5 = x_49;
x_6 = x_48;
goto block_47;
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_string_memcmp(x_2, x_50, x_54, x_54, x_52);
if (x_55 == 0)
{
x_5 = x_49;
x_6 = x_55;
goto block_47;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_unsigned_to_nat(1u);
lean_inc_ref(x_2);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_51);
x_58 = l_String_Slice_Pos_nextn(x_57, x_54, x_56);
lean_dec_ref(x_57);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_2);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_51);
x_60 = l_String_Slice_toName(x_59);
lean_dec_ref(x_59);
lean_inc(x_60);
x_61 = l_Lake_Workspace_findTargetModule_x3f(x_60, x_1);
if (lean_obj_tag(x_61) == 1)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(x_1, x_62, x_3);
lean_dec_ref(x_1);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_ctor_set_tag(x_63, 1);
return x_63;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_alloc_ctor(1, 1, 0);
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
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 0);
x_69 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_70 = lean_array_push(x_69, x_68);
lean_ctor_set_tag(x_63, 0);
lean_ctor_set(x_63, 0, x_70);
return x_63;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
lean_dec(x_63);
x_72 = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0;
x_73 = lean_array_push(x_72, x_71);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_61);
lean_dec(x_3);
lean_dec_ref(x_1);
x_75 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_75, 0, x_60);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = 47;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_byte_size(x_2);
lean_inc_ref(x_2);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(x_13);
x_15 = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0;
lean_inc_ref(x_2);
x_16 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(x_10, x_13, x_2, x_12, x_14, x_15);
x_17 = lean_array_to_list(x_16);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 2);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_string_utf8_extract(x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
x_24 = l_Lake_stringToLegalOrSimpleName(x_23);
x_25 = l_Lake_Workspace_findLeanExe_x3f(x_24, x_1);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(x_26, 0, x_2);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec_ref(x_2);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_17, 0);
lean_inc(x_31);
lean_dec_ref(x_17);
x_32 = lean_ctor_get(x_18, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec_ref(x_18);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_88 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_31, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_31, 2);
lean_inc(x_90);
x_91 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0;
x_92 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1;
x_93 = lean_nat_sub(x_90, x_89);
x_94 = lean_nat_dec_le(x_92, x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_dec(x_31);
x_34 = x_88;
x_35 = x_89;
x_36 = x_90;
goto block_87;
}
else
{
uint8_t x_95; 
x_95 = lean_string_memcmp(x_88, x_91, x_89, x_11, x_92);
if (x_95 == 0)
{
lean_dec(x_31);
x_34 = x_88;
x_35 = x_89;
x_36 = x_90;
goto block_87;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_unsigned_to_nat(1u);
x_97 = l_String_Slice_Pos_nextn(x_31, x_11, x_96);
lean_dec(x_31);
x_98 = lean_nat_add(x_89, x_97);
lean_dec(x_97);
lean_dec(x_89);
x_34 = x_88;
x_35 = x_98;
x_36 = x_90;
goto block_87;
}
}
}
else
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
goto block_9;
}
block_87:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_string_utf8_extract(x_34, x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
x_38 = l_Lake_parsePackageSpec(x_1, x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_32);
lean_dec_ref(x_2);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_32);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_32, 0);
x_46 = lean_ctor_get(x_32, 1);
x_47 = lean_ctor_get(x_32, 2);
x_48 = lean_string_utf8_extract(x_45, x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
x_49 = l_Lake_stringToLegalOrSimpleName(x_48);
x_50 = l_Lake_Package_findTargetDecl_x3f(x_49, x_44);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_free_object(x_32);
lean_free_object(x_38);
lean_dec(x_44);
goto block_5;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 3);
lean_inc(x_54);
lean_dec(x_51);
x_55 = l_Lake_LeanExe_keyword;
x_56 = lean_name_eq(x_53, x_55);
lean_dec(x_53);
if (x_56 == 0)
{
lean_dec(x_54);
lean_dec(x_52);
lean_free_object(x_32);
lean_free_object(x_38);
lean_dec(x_44);
goto block_5;
}
else
{
lean_dec_ref(x_2);
lean_ctor_set(x_32, 2, x_54);
lean_ctor_set(x_32, 1, x_52);
lean_ctor_set(x_32, 0, x_44);
lean_ctor_set(x_38, 0, x_32);
return x_38;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_32, 0);
x_59 = lean_ctor_get(x_32, 1);
x_60 = lean_ctor_get(x_32, 2);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_32);
x_61 = lean_string_utf8_extract(x_58, x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
x_62 = l_Lake_stringToLegalOrSimpleName(x_61);
x_63 = l_Lake_Package_findTargetDecl_x3f(x_62, x_57);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_free_object(x_38);
lean_dec(x_57);
goto block_5;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 3);
lean_inc(x_67);
lean_dec(x_64);
x_68 = l_Lake_LeanExe_keyword;
x_69 = lean_name_eq(x_66, x_68);
lean_dec(x_66);
if (x_69 == 0)
{
lean_dec(x_67);
lean_dec(x_65);
lean_free_object(x_38);
lean_dec(x_57);
goto block_5;
}
else
{
lean_object* x_70; 
lean_dec_ref(x_2);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_57);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set(x_70, 2, x_67);
lean_ctor_set(x_38, 0, x_70);
return x_38;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_38, 0);
lean_inc(x_71);
lean_dec(x_38);
x_72 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_32, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_32, 2);
lean_inc(x_74);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_75 = x_32;
} else {
 lean_dec_ref(x_32);
 x_75 = lean_box(0);
}
x_76 = lean_string_utf8_extract(x_72, x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
x_77 = l_Lake_stringToLegalOrSimpleName(x_76);
x_78 = l_Lake_Package_findTargetDecl_x3f(x_77, x_71);
lean_dec(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_dec(x_75);
lean_dec(x_71);
goto block_5;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 3);
lean_inc(x_82);
lean_dec(x_79);
x_83 = l_Lake_LeanExe_keyword;
x_84 = lean_name_eq(x_81, x_83);
lean_dec(x_81);
if (x_84 == 0)
{
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_75);
lean_dec(x_71);
goto block_5;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_2);
if (lean_is_scalar(x_75)) {
 x_85 = lean_alloc_ctor(0, 3, 0);
} else {
 x_85 = x_75;
}
lean_ctor_set(x_85, 0, x_71);
lean_ctor_set(x_85, 1, x_80);
lean_ctor_set(x_85, 2, x_82);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
}
}
}
}
else
{
lean_dec(x_17);
goto block_9;
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
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_parseTargetSpec_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_parseTargetSpec_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00Lake_parseTargetSpec_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_nat_sub(x_19, x_18);
x_21 = lean_nat_dec_eq(x_17, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_22 = lean_string_utf8_next_fast(x_3, x_17);
x_23 = lean_string_utf8_get_fast(x_3, x_17);
x_24 = lean_uint32_dec_eq(x_23, x_1);
if (x_24 == 0)
{
lean_dec(x_17);
lean_ctor_set(x_5, 1, x_22);
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_2);
x_26 = l_String_Slice_slice_x21(x_2, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
lean_ctor_set(x_5, 1, x_22);
lean_ctor_set(x_5, 0, x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 2);
lean_inc(x_29);
lean_dec_ref(x_26);
x_7 = x_5;
x_8 = x_27;
x_9 = x_28;
x_10 = x_29;
goto block_14;
}
}
else
{
lean_object* x_30; 
lean_free_object(x_5);
lean_dec(x_17);
x_30 = lean_box(1);
lean_inc(x_4);
lean_inc_ref(x_3);
x_7 = x_30;
x_8 = x_3;
x_9 = x_16;
x_10 = x_4;
goto block_14;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
x_33 = lean_ctor_get(x_2, 1);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_nat_sub(x_34, x_33);
x_36 = lean_nat_dec_eq(x_32, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint32_t x_38; uint8_t x_39; 
x_37 = lean_string_utf8_next_fast(x_3, x_32);
x_38 = lean_string_utf8_get_fast(x_3, x_32);
x_39 = lean_uint32_dec_eq(x_38, x_1);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_32);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_37);
x_5 = x_40;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc_ref(x_2);
x_42 = l_String_Slice_slice_x21(x_2, x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_37);
x_44 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 2);
lean_inc(x_46);
lean_dec_ref(x_42);
x_7 = x_43;
x_8 = x_44;
x_9 = x_45;
x_10 = x_46;
goto block_14;
}
}
else
{
lean_object* x_47; 
lean_dec(x_32);
x_47 = lean_box(1);
lean_inc(x_4);
lean_inc_ref(x_3);
x_7 = x_47;
x_8 = x_3;
x_9 = x_31;
x_10 = x_4;
goto block_14;
}
}
}
else
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
block_14:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_string_utf8_extract(x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_12 = lean_array_push(x_6, x_11);
x_5 = x_7;
x_6 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lake_parseTargetSpec___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = 58;
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_utf8_byte_size(x_2);
lean_inc_ref(x_2);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_String_Slice_split___at___00Lake_parseTargetSpec_spec__0(x_11);
x_13 = l_Lake_parseTargetSpec___closed__0;
lean_inc_ref(x_2);
x_14 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(x_4, x_11, x_2, x_10, x_12, x_13);
x_15 = lean_array_to_list(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_2);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_box(0);
x_19 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(x_1, x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_16, 1);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_2);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec_ref(x_15);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec_ref(x_16);
x_23 = l_String_toName(x_22);
x_24 = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(x_1, x_21, x_23);
return x_24;
}
else
{
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_1);
x_5 = lean_box(0);
goto block_8;
}
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_1);
x_5 = lean_box(0);
goto block_8;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set_uint32(x_6, sizeof(void*)*1, x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_parseTargetSpec(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(x_1, x_2, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint32_t x_10; lean_object* x_11; 
x_10 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_11 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
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
x_8 = l_Lake_parseTargetSpec(x_1, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Array_append___redArg(x_3, x_9);
lean_dec(x_9);
x_2 = x_7;
x_3 = x_10;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(x_1, x_2, x_3);
return x_5;
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
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lake_parseTargetSpecs___closed__0;
lean_inc_ref(x_1);
x_5 = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = l_Array_isEmpty___redArg(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(x_1, x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
x_15 = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(x_1, x_14);
lean_dec_ref(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
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
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_parseTargetSpecs(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(x_1, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Lake_CLI_Error(uint8_t builtin);
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Build(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_CLI_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Register(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_buildSpecs___closed__0 = _init_l_Lake_buildSpecs___closed__0();
lean_mark_persistent(l_Lake_buildSpecs___closed__0);
l_Lake_parsePackageSpec___closed__0 = _init_l_Lake_parsePackageSpec___closed__0();
lean_mark_persistent(l_Lake_parsePackageSpec___closed__0);
l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0 = _init_l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0);
l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1 = _init_l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1);
l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1 = _init_l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1);
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
l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__3 = _init_l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveExeTarget___closed__3);
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
l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1 = _init_l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1);
l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0);
l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0 = _init_l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0();
lean_mark_persistent(l_String_Slice_split___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1 = _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1);
l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2 = _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2);
l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0 = _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0);
l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1 = _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1);
l_Lake_parseTargetSpec___closed__0 = _init_l_Lake_parseTargetSpec___closed__0();
lean_mark_persistent(l_Lake_parseTargetSpec___closed__0);
l_Lake_parseTargetSpecs___closed__0 = _init_l_Lake_parseTargetSpecs___closed__0();
lean_mark_persistent(l_Lake_parseTargetSpecs___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
