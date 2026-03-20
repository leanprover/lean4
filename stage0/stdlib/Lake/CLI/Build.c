// Lean compiler output
// Module: Lake.CLI.Build
// Imports: public import Lake.CLI.Error public import Lake.Config.Workspace import Lake.Build.Infos import Lake.Build.Job.Monad public import Lake.Build.Job.Register import Lake.Util.IO import Init.Data.Iterators.Consumers
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lake_Package_findTargetModule_x3f(lean_object*, lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
extern lean_object* l_Lake_Module_leanArtsFacet;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lake_BuildInfo_key(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lake_BuildKey_toSimpleString(lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lake_Package_keyword;
lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toName(lean_object*);
lean_object* l_Lake_formatQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mixArray___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_mkBuildSpec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_mkBuildSpec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildSpecs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "<collection>"};
static const lean_object* l_Lake_buildSpecs___closed__0 = (const lean_object*)&l_Lake_buildSpecs___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_querySpecs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_querySpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0 = (const lean_object*)&l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0 = (const lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0_value;
static const lean_closure_object l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1 = (const lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0 = (const lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 214, 131, 210, 10, 90, 37, 134)}};
static const lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1 = (const lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0 = (const lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0_value)}};
static const lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1 = (const lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "package"};
static const lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0 = (const lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0 = (const lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1 = (const lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1_value;
static lean_once_cell_t l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0 = (const lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0_value;
static lean_once_cell_t l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_parseTargetSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_parseTargetSpec___closed__0 = (const lean_object*)&l_Lake_parseTargetSpec___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_parseTargetSpecs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_parseTargetSpecs___closed__0 = (const lean_object*)&l_Lake_parseTargetSpecs___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_mkBuildSpec___redArg(lean_object* v_info_1_, lean_object* v_inst_2_){
_start:
{
uint8_t v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = 1;
v___x_4_ = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(v___x_4_, 0, lean_box(0));
lean_closure_set(v___x_4_, 1, v_inst_2_);
v___x_5_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5_, 0, v_info_1_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
lean_ctor_set_uint8(v___x_5_, sizeof(void*)*2, v___x_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_mkBuildSpec(lean_object* v_00_u03b1_6_, lean_object* v_info_7_, lean_object* v_inst_8_, lean_object* v_h_9_){
_start:
{
uint8_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = 1;
v___x_11_ = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(v___x_11_, 0, lean_box(0));
lean_closure_set(v___x_11_, 1, v_inst_8_);
v___x_12_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_12_, 0, v_info_7_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2, v___x_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___redArg(lean_object* v_info_13_, lean_object* v_config_14_){
_start:
{
uint8_t v_buildable_15_; lean_object* v_format_16_; lean_object* v___x_17_; 
v_buildable_15_ = lean_ctor_get_uint8(v_config_14_, sizeof(void*)*4);
v_format_16_ = lean_ctor_get(v_config_14_, 3);
lean_inc_ref(v_format_16_);
v___x_17_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_17_, 0, v_info_13_);
lean_ctor_set(v___x_17_, 1, v_format_16_);
lean_ctor_set_uint8(v___x_17_, sizeof(void*)*2, v_buildable_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___redArg___boxed(lean_object* v_info_18_, lean_object* v_config_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lake_mkConfigBuildSpec___redArg(v_info_18_, v_config_19_);
lean_dec_ref(v_config_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec(lean_object* v_facet_21_, lean_object* v_info_22_, lean_object* v_config_23_, lean_object* v_h_24_){
_start:
{
uint8_t v_buildable_25_; lean_object* v_format_26_; lean_object* v___x_27_; 
v_buildable_25_ = lean_ctor_get_uint8(v_config_23_, sizeof(void*)*4);
v_format_26_ = lean_ctor_get(v_config_23_, 3);
lean_inc_ref(v_format_26_);
v___x_27_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_27_, 0, v_info_22_);
lean_ctor_set(v___x_27_, 1, v_format_26_);
lean_ctor_set_uint8(v___x_27_, sizeof(void*)*2, v_buildable_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkConfigBuildSpec___boxed(lean_object* v_facet_28_, lean_object* v_info_29_, lean_object* v_config_30_, lean_object* v_h_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lake_mkConfigBuildSpec(v_facet_28_, v_info_29_, v_config_30_, v_h_31_);
lean_dec_ref(v_config_30_);
lean_dec(v_facet_28_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch(lean_object* v_self_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_info_41_; lean_object* v___x_42_; 
v_info_41_ = lean_ctor_get(v_self_33_, 0);
lean_inc_ref(v_info_41_);
lean_dec_ref(v_self_33_);
lean_inc_ref(v_a_38_);
lean_inc_ref(v_info_41_);
v___x_42_ = lean_apply_7(v_a_34_, v_info_41_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, lean_box(0));
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; lean_object* v_a_44_; lean_object* v_task_45_; lean_object* v_kind_46_; lean_object* v_caption_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_75_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_a_43_);
v_a_44_ = lean_ctor_get(v___x_42_, 1);
lean_inc(v_a_44_);
v_task_45_ = lean_ctor_get(v_a_43_, 0);
v_kind_46_ = lean_ctor_get(v_a_43_, 1);
v_caption_47_ = lean_ctor_get(v_a_43_, 2);
v_isSharedCheck_75_ = !lean_is_exclusive(v_a_43_);
if (v_isSharedCheck_75_ == 0)
{
v___x_49_ = v_a_43_;
v_isShared_50_ = v_isSharedCheck_75_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_caption_47_);
lean_inc(v_kind_46_);
lean_inc(v_task_45_);
lean_dec(v_a_43_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_75_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_51_ = lean_string_utf8_byte_size(v_caption_47_);
lean_dec_ref(v_caption_47_);
v___x_52_ = lean_unsigned_to_nat(0u);
v___x_53_ = lean_nat_dec_eq(v___x_51_, v___x_52_);
if (v___x_53_ == 0)
{
lean_del_object(v___x_49_);
lean_dec(v_kind_46_);
lean_dec_ref(v_task_45_);
lean_dec(v_a_44_);
lean_dec_ref(v_info_41_);
lean_dec_ref(v_a_38_);
return v___x_42_;
}
else
{
lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_72_; 
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_72_ == 0)
{
lean_object* v_unused_73_; lean_object* v_unused_74_; 
v_unused_73_ = lean_ctor_get(v___x_42_, 1);
lean_dec(v_unused_73_);
v_unused_74_ = lean_ctor_get(v___x_42_, 0);
lean_dec(v_unused_74_);
v___x_55_ = v___x_42_;
v_isShared_56_ = v_isSharedCheck_72_;
goto v_resetjp_54_;
}
else
{
lean_dec(v___x_42_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_72_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v_registeredJobs_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; lean_object* v_job_63_; 
v_registeredJobs_57_ = lean_ctor_get(v_a_38_, 3);
lean_inc(v_registeredJobs_57_);
lean_dec_ref(v_a_38_);
v___x_58_ = lean_st_ref_take(v_registeredJobs_57_);
v___x_59_ = l_Lake_BuildInfo_key(v_info_41_);
v___x_60_ = l_Lake_BuildKey_toSimpleString(v___x_59_);
v___x_61_ = 0;
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 2, v___x_60_);
v_job_63_ = v___x_49_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_task_45_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_kind_46_);
lean_ctor_set(v_reuseFailAlloc_71_, 2, v___x_60_);
v_job_63_ = v_reuseFailAlloc_71_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_69_; 
lean_ctor_set_uint8(v_job_63_, sizeof(void*)*3, v___x_61_);
lean_inc_ref(v_job_63_);
v___x_64_ = l_Lake_Job_toOpaque___redArg(v_job_63_);
v___x_65_ = lean_array_push(v___x_58_, v___x_64_);
v___x_66_ = lean_st_ref_set(v_registeredJobs_57_, v___x_65_);
lean_dec(v_registeredJobs_57_);
v___x_67_ = l_Lake_Job_renew___redArg(v_job_63_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_67_);
v___x_69_ = v___x_55_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_a_44_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_info_41_);
lean_dec_ref(v_a_38_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch___boxed(lean_object* v_self_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lake_BuildSpec_fetch(v_self_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build(lean_object* v_self_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_a_94_; lean_object* v_a_95_; lean_object* v_info_98_; lean_object* v___x_99_; 
v_info_98_ = lean_ctor_get(v_self_85_, 0);
lean_inc_ref(v_info_98_);
lean_dec_ref(v_self_85_);
lean_inc_ref(v_a_90_);
lean_inc_ref(v_info_98_);
v___x_99_ = lean_apply_7(v_a_86_, v_info_98_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, lean_box(0));
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v_a_101_; lean_object* v_task_102_; lean_object* v_kind_103_; lean_object* v_caption_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
v_a_101_ = lean_ctor_get(v___x_99_, 1);
lean_inc(v_a_101_);
lean_dec_ref(v___x_99_);
v_task_102_ = lean_ctor_get(v_a_100_, 0);
v_kind_103_ = lean_ctor_get(v_a_100_, 1);
v_caption_104_ = lean_ctor_get(v_a_100_, 2);
v___x_105_ = lean_string_utf8_byte_size(v_caption_104_);
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_nat_dec_eq(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_dec_ref(v_info_98_);
lean_dec_ref(v_a_90_);
v_a_94_ = v_a_100_;
v_a_95_ = v_a_101_;
goto v___jp_93_;
}
else
{
lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_123_; 
lean_inc(v_kind_103_);
lean_inc_ref(v_task_102_);
v_isSharedCheck_123_ = !lean_is_exclusive(v_a_100_);
if (v_isSharedCheck_123_ == 0)
{
lean_object* v_unused_124_; lean_object* v_unused_125_; lean_object* v_unused_126_; 
v_unused_124_ = lean_ctor_get(v_a_100_, 2);
lean_dec(v_unused_124_);
v_unused_125_ = lean_ctor_get(v_a_100_, 1);
lean_dec(v_unused_125_);
v_unused_126_ = lean_ctor_get(v_a_100_, 0);
lean_dec(v_unused_126_);
v___x_109_ = v_a_100_;
v_isShared_110_ = v_isSharedCheck_123_;
goto v_resetjp_108_;
}
else
{
lean_dec(v_a_100_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_123_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v_registeredJobs_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; lean_object* v_job_117_; 
v_registeredJobs_111_ = lean_ctor_get(v_a_90_, 3);
lean_inc(v_registeredJobs_111_);
lean_dec_ref(v_a_90_);
v___x_112_ = lean_st_ref_take(v_registeredJobs_111_);
v___x_113_ = l_Lake_BuildInfo_key(v_info_98_);
v___x_114_ = l_Lake_BuildKey_toSimpleString(v___x_113_);
v___x_115_ = 0;
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 2, v___x_114_);
v_job_117_ = v___x_109_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_task_102_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_kind_103_);
lean_ctor_set(v_reuseFailAlloc_122_, 2, v___x_114_);
v_job_117_ = v_reuseFailAlloc_122_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
lean_ctor_set_uint8(v_job_117_, sizeof(void*)*3, v___x_115_);
lean_inc_ref(v_job_117_);
v___x_118_ = l_Lake_Job_toOpaque___redArg(v_job_117_);
v___x_119_ = lean_array_push(v___x_112_, v___x_118_);
v___x_120_ = lean_st_ref_set(v_registeredJobs_111_, v___x_119_);
lean_dec(v_registeredJobs_111_);
v___x_121_ = l_Lake_Job_renew___redArg(v_job_117_);
v_a_94_ = v___x_121_;
v_a_95_ = v_a_101_;
goto v___jp_93_;
}
}
}
}
else
{
lean_dec_ref(v_info_98_);
lean_dec_ref(v_a_90_);
return v___x_99_;
}
v___jp_93_:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = l_Lake_Job_toOpaque___redArg(v_a_94_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_a_95_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build___boxed(lean_object* v_self_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lake_BuildSpec_build(v_self_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lam__0(lean_object* v_format_136_, uint8_t v_fmt_137_, lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_149_; 
v_a_139_ = lean_ctor_get(v_x_138_, 0);
v_a_140_ = lean_ctor_get(v_x_138_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_149_ == 0)
{
v___x_142_ = v_x_138_;
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_inc(v_a_139_);
lean_dec(v_x_138_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_144_ = lean_box(v_fmt_137_);
v___x_145_ = lean_apply_2(v_format_136_, v___x_144_, v_a_139_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_145_);
v___x_147_ = v___x_142_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_a_140_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
else
{
lean_object* v_a_150_; lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec_ref(v_format_136_);
v_a_150_ = lean_ctor_get(v_x_138_, 0);
v_a_151_ = lean_ctor_get(v_x_138_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v_x_138_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_inc(v_a_150_);
lean_dec(v_x_138_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_150_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lam__0___boxed(lean_object* v_format_159_, lean_object* v_fmt_160_, lean_object* v_x_161_){
_start:
{
uint8_t v_fmt_boxed_162_; lean_object* v_res_163_; 
v_fmt_boxed_162_ = lean_unbox(v_fmt_160_);
v_res_163_ = l_Lake_BuildSpec_query___lam__0(v_format_159_, v_fmt_boxed_162_, v_x_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query(lean_object* v_self_164_, uint8_t v_fmt_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_info_173_; lean_object* v_format_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_info_173_ = lean_ctor_get(v_self_164_, 0);
lean_inc_ref(v_info_173_);
v_format_174_ = lean_ctor_get(v_self_164_, 1);
lean_inc_ref(v_format_174_);
lean_dec_ref(v_self_164_);
lean_inc_ref(v_info_173_);
v___x_175_ = l_Lake_BuildInfo_key(v_info_173_);
lean_inc_ref(v_a_170_);
v___x_176_ = lean_apply_7(v_a_166_, v_info_173_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, lean_box(0));
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_217_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_a_178_ = lean_ctor_get(v___x_176_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_217_ == 0)
{
v___x_180_ = v___x_176_;
v_isShared_181_ = v_isSharedCheck_217_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_217_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_task_182_; lean_object* v_caption_183_; uint8_t v_optional_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_215_; 
v_task_182_ = lean_ctor_get(v_a_177_, 0);
v_caption_183_ = lean_ctor_get(v_a_177_, 2);
v_optional_184_ = lean_ctor_get_uint8(v_a_177_, sizeof(void*)*3);
v_isSharedCheck_215_ = !lean_is_exclusive(v_a_177_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; 
v_unused_216_ = lean_ctor_get(v_a_177_, 1);
lean_dec(v_unused_216_);
v___x_186_ = v_a_177_;
v_isShared_187_ = v_isSharedCheck_215_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_caption_183_);
lean_inc(v_task_182_);
lean_dec(v_a_177_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_215_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___f_190_; lean_object* v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_188_ = lean_box(0);
v___x_189_ = lean_box(v_fmt_165_);
v___f_190_ = lean_alloc_closure((void*)(l_Lake_BuildSpec_query___lam__0___boxed), 3, 2);
lean_closure_set(v___f_190_, 0, v_format_174_);
lean_closure_set(v___f_190_, 1, v___x_189_);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = 0;
v___x_193_ = lean_task_map(v___f_190_, v_task_182_, v___x_191_, v___x_192_);
v___x_194_ = lean_string_utf8_byte_size(v_caption_183_);
v___x_195_ = lean_nat_dec_eq(v___x_194_, v___x_191_);
if (v___x_195_ == 0)
{
lean_object* v___x_197_; 
lean_dec_ref(v___x_175_);
lean_dec_ref(v_a_170_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v___x_188_);
lean_ctor_set(v___x_186_, 0, v___x_193_);
v___x_197_ = v___x_186_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_caption_183_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, sizeof(void*)*3, v_optional_184_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_199_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_197_);
v___x_199_ = v___x_180_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_a_178_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
else
{
lean_object* v_registeredJobs_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_job_206_; 
lean_dec_ref(v_caption_183_);
v_registeredJobs_202_ = lean_ctor_get(v_a_170_, 3);
lean_inc(v_registeredJobs_202_);
lean_dec_ref(v_a_170_);
v___x_203_ = lean_st_ref_take(v_registeredJobs_202_);
v___x_204_ = l_Lake_BuildKey_toSimpleString(v___x_175_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 2, v___x_204_);
lean_ctor_set(v___x_186_, 1, v___x_188_);
lean_ctor_set(v___x_186_, 0, v___x_193_);
v_job_206_ = v___x_186_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v___x_204_);
v_job_206_ = v_reuseFailAlloc_214_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
lean_ctor_set_uint8(v_job_206_, sizeof(void*)*3, v___x_192_);
lean_inc_ref(v_job_206_);
v___x_207_ = l_Lake_Job_toOpaque___redArg(v_job_206_);
v___x_208_ = lean_array_push(v___x_203_, v___x_207_);
v___x_209_ = lean_st_ref_set(v_registeredJobs_202_, v___x_208_);
lean_dec(v_registeredJobs_202_);
v___x_210_ = l_Lake_Job_renew___redArg(v_job_206_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_210_);
v___x_212_ = v___x_180_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_a_178_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
}
else
{
lean_object* v_a_218_; lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec_ref(v___x_175_);
lean_dec_ref(v_format_174_);
lean_dec_ref(v_a_170_);
v_a_218_ = lean_ctor_get(v___x_176_, 0);
v_a_219_ = lean_ctor_get(v___x_176_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_176_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_inc(v_a_218_);
lean_dec(v___x_176_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_218_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___boxed(lean_object* v_self_227_, lean_object* v_fmt_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
uint8_t v_fmt_boxed_236_; lean_object* v_res_237_; 
v_fmt_boxed_236_ = lean_unbox(v_fmt_228_);
v_res_237_ = l_Lake_BuildSpec_query(v_self_227_, v_fmt_boxed_236_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(size_t v_sz_238_, size_t v_i_239_, lean_object* v_bs_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
uint8_t v___x_248_; 
v___x_248_ = lean_usize_dec_lt(v_i_239_, v_sz_238_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; 
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v_bs_240_);
lean_ctor_set(v___x_249_, 1, v___y_246_);
return v___x_249_;
}
else
{
lean_object* v_v_250_; lean_object* v_info_251_; lean_object* v___x_252_; 
v_v_250_ = lean_array_uget_borrowed(v_bs_240_, v_i_239_);
v_info_251_ = lean_ctor_get(v_v_250_, 0);
lean_inc_ref(v_info_251_);
lean_inc_ref(v___y_241_);
lean_inc_ref(v___y_245_);
lean_inc(v___y_244_);
lean_inc(v___y_243_);
lean_inc(v___y_242_);
lean_inc_ref(v_info_251_);
v___x_252_ = lean_apply_7(v___y_241_, v_info_251_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, lean_box(0));
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v_a_254_; lean_object* v_task_255_; lean_object* v_kind_256_; lean_object* v_caption_257_; lean_object* v___x_258_; lean_object* v_bs_x27_259_; lean_object* v_a_261_; lean_object* v_a_262_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
v_a_254_ = lean_ctor_get(v___x_252_, 1);
lean_inc(v_a_254_);
lean_dec_ref(v___x_252_);
v_task_255_ = lean_ctor_get(v_a_253_, 0);
v_kind_256_ = lean_ctor_get(v_a_253_, 1);
v_caption_257_ = lean_ctor_get(v_a_253_, 2);
v___x_258_ = lean_unsigned_to_nat(0u);
v_bs_x27_259_ = lean_array_uset(v_bs_240_, v_i_239_, v___x_258_);
v___x_268_ = lean_string_utf8_byte_size(v_caption_257_);
v___x_269_ = lean_nat_dec_eq(v___x_268_, v___x_258_);
if (v___x_269_ == 0)
{
lean_dec_ref(v_info_251_);
v_a_261_ = v_a_253_;
v_a_262_ = v_a_254_;
goto v___jp_260_;
}
else
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_285_; 
lean_inc(v_kind_256_);
lean_inc_ref(v_task_255_);
v_isSharedCheck_285_ = !lean_is_exclusive(v_a_253_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; lean_object* v_unused_287_; lean_object* v_unused_288_; 
v_unused_286_ = lean_ctor_get(v_a_253_, 2);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_a_253_, 1);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_a_253_, 0);
lean_dec(v_unused_288_);
v___x_271_ = v_a_253_;
v_isShared_272_ = v_isSharedCheck_285_;
goto v_resetjp_270_;
}
else
{
lean_dec(v_a_253_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_285_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v_registeredJobs_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; lean_object* v_job_279_; 
v_registeredJobs_273_ = lean_ctor_get(v___y_245_, 3);
v___x_274_ = lean_st_ref_take(v_registeredJobs_273_);
v___x_275_ = l_Lake_BuildInfo_key(v_info_251_);
v___x_276_ = l_Lake_BuildKey_toSimpleString(v___x_275_);
v___x_277_ = 0;
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 2, v___x_276_);
v_job_279_ = v___x_271_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_task_255_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_kind_256_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v___x_276_);
v_job_279_ = v_reuseFailAlloc_284_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
lean_ctor_set_uint8(v_job_279_, sizeof(void*)*3, v___x_277_);
lean_inc_ref(v_job_279_);
v___x_280_ = l_Lake_Job_toOpaque___redArg(v_job_279_);
v___x_281_ = lean_array_push(v___x_274_, v___x_280_);
v___x_282_ = lean_st_ref_set(v_registeredJobs_273_, v___x_281_);
v___x_283_ = l_Lake_Job_renew___redArg(v_job_279_);
v_a_261_ = v___x_283_;
v_a_262_ = v_a_254_;
goto v___jp_260_;
}
}
}
v___jp_260_:
{
lean_object* v___x_263_; size_t v___x_264_; size_t v___x_265_; lean_object* v___x_266_; 
v___x_263_ = l_Lake_Job_toOpaque___redArg(v_a_261_);
v___x_264_ = ((size_t)1ULL);
v___x_265_ = lean_usize_add(v_i_239_, v___x_264_);
v___x_266_ = lean_array_uset(v_bs_x27_259_, v_i_239_, v___x_263_);
v_i_239_ = v___x_265_;
v_bs_240_ = v___x_266_;
v___y_246_ = v_a_262_;
goto _start;
}
}
else
{
lean_object* v_a_289_; lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref(v_info_251_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec_ref(v_bs_240_);
v_a_289_ = lean_ctor_get(v___x_252_, 0);
v_a_290_ = lean_ctor_get(v___x_252_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_252_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_inc(v_a_289_);
lean_dec(v___x_252_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_289_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0___boxed(lean_object* v_sz_298_, lean_object* v_i_299_, lean_object* v_bs_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
size_t v_sz_boxed_308_; size_t v_i_boxed_309_; lean_object* v_res_310_; 
v_sz_boxed_308_ = lean_unbox_usize(v_sz_298_);
lean_dec(v_sz_298_);
v_i_boxed_309_ = lean_unbox_usize(v_i_299_);
lean_dec(v_i_299_);
v_res_310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(v_sz_boxed_308_, v_i_boxed_309_, v_bs_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSpecs(lean_object* v_specs_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
size_t v_sz_320_; size_t v___x_321_; lean_object* v___x_322_; 
v_sz_320_ = lean_array_size(v_specs_312_);
v___x_321_ = ((size_t)0ULL);
v___x_322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(v_sz_320_, v___x_321_, v_specs_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_333_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v_a_324_ = lean_ctor_get(v___x_322_, 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_333_ == 0)
{
v___x_326_ = v___x_322_;
v_isShared_327_ = v_isSharedCheck_333_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_inc(v_a_323_);
lean_dec(v___x_322_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_333_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_328_ = ((lean_object*)(l_Lake_buildSpecs___closed__0));
v___x_329_ = l_Lake_Job_mixArray___redArg(v_a_323_, v___x_328_);
lean_dec(v_a_323_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_329_);
v___x_331_ = v___x_326_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_a_324_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
else
{
lean_object* v_a_334_; lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
v_a_334_ = lean_ctor_get(v___x_322_, 0);
v_a_335_ = lean_ctor_get(v___x_322_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_322_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_inc(v_a_334_);
lean_dec(v___x_322_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_334_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSpecs___boxed(lean_object* v_specs_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lake_buildSpecs(v_specs_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0(lean_object* v_format_352_, uint8_t v_fmt_353_, lean_object* v_x_354_){
_start:
{
if (lean_obj_tag(v_x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_365_; 
v_a_355_ = lean_ctor_get(v_x_354_, 0);
v_a_356_ = lean_ctor_get(v_x_354_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v_x_354_);
if (v_isSharedCheck_365_ == 0)
{
v___x_358_ = v_x_354_;
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_inc(v_a_355_);
lean_dec(v_x_354_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_360_ = lean_box(v_fmt_353_);
v___x_361_ = lean_apply_2(v_format_352_, v___x_360_, v_a_355_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_361_);
v___x_363_ = v___x_358_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_a_356_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_object* v_a_366_; lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec_ref(v_format_352_);
v_a_366_ = lean_ctor_get(v_x_354_, 0);
v_a_367_ = lean_ctor_get(v_x_354_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_x_354_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v_x_354_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_inc(v_a_366_);
lean_dec(v_x_354_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_366_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0___boxed(lean_object* v_format_375_, lean_object* v_fmt_376_, lean_object* v_x_377_){
_start:
{
uint8_t v_fmt_boxed_378_; lean_object* v_res_379_; 
v_fmt_boxed_378_ = lean_unbox(v_fmt_376_);
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0(v_format_375_, v_fmt_boxed_378_, v_x_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(uint8_t v_fmt_380_, size_t v_sz_381_, size_t v_i_382_, lean_object* v_bs_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = lean_usize_dec_lt(v_i_382_, v_sz_381_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_bs_383_);
lean_ctor_set(v___x_392_, 1, v___y_389_);
return v___x_392_;
}
else
{
lean_object* v_v_393_; lean_object* v_info_394_; lean_object* v_format_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_v_393_ = lean_array_uget_borrowed(v_bs_383_, v_i_382_);
v_info_394_ = lean_ctor_get(v_v_393_, 0);
v_format_395_ = lean_ctor_get(v_v_393_, 1);
lean_inc_ref(v_format_395_);
lean_inc_ref(v_info_394_);
v___x_396_ = l_Lake_BuildInfo_key(v_info_394_);
lean_inc_ref(v___y_384_);
lean_inc_ref(v___y_388_);
lean_inc(v___y_387_);
lean_inc(v___y_386_);
lean_inc(v___y_385_);
lean_inc_ref(v_info_394_);
v___x_397_ = lean_apply_7(v___y_384_, v_info_394_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, lean_box(0));
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v_a_399_; lean_object* v_task_400_; lean_object* v_caption_401_; uint8_t v_optional_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_435_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
v_a_399_ = lean_ctor_get(v___x_397_, 1);
lean_inc(v_a_399_);
lean_dec_ref(v___x_397_);
v_task_400_ = lean_ctor_get(v_a_398_, 0);
v_caption_401_ = lean_ctor_get(v_a_398_, 2);
v_optional_402_ = lean_ctor_get_uint8(v_a_398_, sizeof(void*)*3);
v_isSharedCheck_435_ = !lean_is_exclusive(v_a_398_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; 
v_unused_436_ = lean_ctor_get(v_a_398_, 1);
lean_dec(v_unused_436_);
v___x_404_ = v_a_398_;
v_isShared_405_ = v_isSharedCheck_435_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_caption_401_);
lean_inc(v_task_400_);
lean_dec(v_a_398_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_435_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v_bs_x27_407_; lean_object* v_a_409_; lean_object* v_a_410_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___f_417_; uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v_bs_x27_407_ = lean_array_uset(v_bs_383_, v_i_382_, v___x_406_);
v___x_415_ = lean_box(0);
v___x_416_ = lean_box(v_fmt_380_);
v___f_417_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_417_, 0, v_format_395_);
lean_closure_set(v___f_417_, 1, v___x_416_);
v___x_418_ = 0;
v___x_419_ = lean_task_map(v___f_417_, v_task_400_, v___x_406_, v___x_418_);
v___x_420_ = lean_string_utf8_byte_size(v_caption_401_);
v___x_421_ = lean_nat_dec_eq(v___x_420_, v___x_406_);
if (v___x_421_ == 0)
{
lean_object* v___x_423_; 
lean_dec_ref(v___x_396_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_415_);
lean_ctor_set(v___x_404_, 0, v___x_419_);
v___x_423_ = v___x_404_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_caption_401_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*3, v_optional_402_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
v_a_409_ = v___x_423_;
v_a_410_ = v_a_399_;
goto v___jp_408_;
}
}
else
{
lean_object* v_registeredJobs_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v_job_429_; 
lean_dec_ref(v_caption_401_);
v_registeredJobs_425_ = lean_ctor_get(v___y_388_, 3);
v___x_426_ = lean_st_ref_take(v_registeredJobs_425_);
v___x_427_ = l_Lake_BuildKey_toSimpleString(v___x_396_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 2, v___x_427_);
lean_ctor_set(v___x_404_, 1, v___x_415_);
lean_ctor_set(v___x_404_, 0, v___x_419_);
v_job_429_ = v___x_404_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v___x_427_);
v_job_429_ = v_reuseFailAlloc_434_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_ctor_set_uint8(v_job_429_, sizeof(void*)*3, v___x_418_);
lean_inc_ref(v_job_429_);
v___x_430_ = l_Lake_Job_toOpaque___redArg(v_job_429_);
v___x_431_ = lean_array_push(v___x_426_, v___x_430_);
v___x_432_ = lean_st_ref_set(v_registeredJobs_425_, v___x_431_);
v___x_433_ = l_Lake_Job_renew___redArg(v_job_429_);
v_a_409_ = v___x_433_;
v_a_410_ = v_a_399_;
goto v___jp_408_;
}
}
v___jp_408_:
{
size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; 
v___x_411_ = ((size_t)1ULL);
v___x_412_ = lean_usize_add(v_i_382_, v___x_411_);
v___x_413_ = lean_array_uset(v_bs_x27_407_, v_i_382_, v_a_409_);
v_i_382_ = v___x_412_;
v_bs_383_ = v___x_413_;
v___y_389_ = v_a_410_;
goto _start;
}
}
}
else
{
lean_object* v_a_437_; lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec_ref(v___x_396_);
lean_dec_ref(v_format_395_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec_ref(v_bs_383_);
v_a_437_ = lean_ctor_get(v___x_397_, 0);
v_a_438_ = lean_ctor_get(v___x_397_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_397_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_inc(v_a_437_);
lean_dec(v___x_397_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_437_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___boxed(lean_object* v_fmt_446_, lean_object* v_sz_447_, lean_object* v_i_448_, lean_object* v_bs_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
uint8_t v_fmt_boxed_457_; size_t v_sz_boxed_458_; size_t v_i_boxed_459_; lean_object* v_res_460_; 
v_fmt_boxed_457_ = lean_unbox(v_fmt_446_);
v_sz_boxed_458_ = lean_unbox_usize(v_sz_447_);
lean_dec(v_sz_447_);
v_i_boxed_459_ = lean_unbox_usize(v_i_448_);
lean_dec(v_i_448_);
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(v_fmt_boxed_457_, v_sz_boxed_458_, v_i_boxed_459_, v_bs_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lake_querySpecs(lean_object* v_specs_461_, uint8_t v_fmt_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
size_t v_sz_470_; size_t v___x_471_; lean_object* v___x_472_; 
v_sz_470_ = lean_array_size(v_specs_461_);
v___x_471_ = ((size_t)0ULL);
v___x_472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(v_fmt_462_, v_sz_470_, v___x_471_, v_specs_461_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_483_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_a_474_ = lean_ctor_get(v___x_472_, 1);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_483_ == 0)
{
v___x_476_ = v___x_472_;
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_478_ = ((lean_object*)(l_Lake_buildSpecs___closed__0));
v___x_479_ = l_Lake_Job_collectArray___redArg(v_a_473_, v___x_478_);
lean_dec(v_a_473_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_479_);
v___x_481_ = v___x_476_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_a_474_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_object* v_a_484_; lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
v_a_484_ = lean_ctor_get(v___x_472_, 0);
v_a_485_ = lean_ctor_get(v___x_472_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_472_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_inc(v_a_484_);
lean_dec(v___x_472_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_484_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_querySpecs___boxed(lean_object* v_specs_493_, lean_object* v_fmt_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
uint8_t v_fmt_boxed_502_; lean_object* v_res_503_; 
v_fmt_boxed_502_ = lean_unbox(v_fmt_494_);
v_res_503_ = l_Lake_querySpecs(v_specs_493_, v_fmt_boxed_502_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(lean_object* v___x_507_, lean_object* v_as_508_, size_t v_sz_509_, size_t v_i_510_, lean_object* v_b_511_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_lt(v_i_510_, v_sz_509_);
if (v___x_512_ == 0)
{
return v_b_511_;
}
else
{
lean_object* v_a_513_; lean_object* v_baseName_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
lean_dec_ref(v_b_511_);
v_a_513_ = lean_array_uget_borrowed(v_as_508_, v_i_510_);
v_baseName_514_ = lean_ctor_get(v_a_513_, 1);
v___x_515_ = lean_box(0);
v___x_516_ = lean_name_eq(v_baseName_514_, v___x_507_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; size_t v___x_518_; size_t v___x_519_; 
v___x_517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0));
v___x_518_ = ((size_t)1ULL);
v___x_519_ = lean_usize_add(v_i_510_, v___x_518_);
v_i_510_ = v___x_519_;
v_b_511_ = v___x_517_;
goto _start;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_inc(v_a_513_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v_a_513_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v___x_515_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___boxed(lean_object* v___x_524_, lean_object* v_as_525_, lean_object* v_sz_526_, lean_object* v_i_527_, lean_object* v_b_528_){
_start:
{
size_t v_sz_boxed_529_; size_t v_i_boxed_530_; lean_object* v_res_531_; 
v_sz_boxed_529_ = lean_unbox_usize(v_sz_526_);
lean_dec(v_sz_526_);
v_i_boxed_530_ = lean_unbox_usize(v_i_527_);
lean_dec(v_i_527_);
v_res_531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v___x_524_, v_as_525_, v_sz_boxed_529_, v_i_boxed_530_, v_b_528_);
lean_dec_ref(v_as_525_);
lean_dec(v___x_524_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec(lean_object* v_ws_532_, lean_object* v_spec_533_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_537_ = lean_string_utf8_byte_size(v_spec_533_);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_nat_dec_eq(v___x_537_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v_packages_540_; lean_object* v___x_541_; lean_object* v___x_542_; size_t v_sz_543_; size_t v___x_544_; lean_object* v___x_545_; lean_object* v_fst_546_; 
v_packages_540_ = lean_ctor_get(v_ws_532_, 5);
lean_inc_ref(v_spec_533_);
v___x_541_ = l_Lake_stringToLegalOrSimpleName(v_spec_533_);
v___x_542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0));
v_sz_543_ = lean_array_size(v_packages_540_);
v___x_544_ = ((size_t)0ULL);
v___x_545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v___x_541_, v_packages_540_, v_sz_543_, v___x_544_, v___x_542_);
lean_dec(v___x_541_);
v_fst_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_fst_546_);
lean_dec_ref(v___x_545_);
if (lean_obj_tag(v_fst_546_) == 0)
{
goto v___jp_534_;
}
else
{
lean_object* v_val_547_; 
v_val_547_ = lean_ctor_get(v_fst_546_, 0);
lean_inc(v_val_547_);
lean_dec_ref(v_fst_546_);
if (lean_obj_tag(v_val_547_) == 0)
{
goto v___jp_534_;
}
else
{
lean_object* v_val_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec_ref(v_spec_533_);
v_val_548_ = lean_ctor_get(v_val_547_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v_val_547_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v_val_547_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_val_548_);
lean_dec(v_val_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_val_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
else
{
lean_object* v_root_556_; lean_object* v___x_557_; 
lean_dec_ref(v_spec_533_);
v_root_556_ = lean_ctor_get(v_ws_532_, 0);
lean_inc_ref(v_root_556_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v_root_556_);
return v___x_557_;
}
v___jp_534_:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_535_, 0, v_spec_533_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec___boxed(lean_object* v_ws_558_, lean_object* v_spec_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lake_parsePackageSpec(v_ws_558_, v_spec_559_);
lean_dec_ref(v_ws_558_);
return v_res_560_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_box(0);
v___x_563_ = l_Lean_Json_compress(v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(uint8_t v_fmt_564_){
_start:
{
if (v_fmt_564_ == 0)
{
lean_object* v___x_565_; 
v___x_565_ = ((lean_object*)(l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0));
return v___x_565_;
}
else
{
lean_object* v___x_566_; 
v___x_566_ = lean_obj_once(&l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1, &l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1_once, _init_l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___boxed(lean_object* v_fmt_567_){
_start:
{
uint8_t v_fmt_boxed_568_; lean_object* v_res_569_; 
v_fmt_boxed_568_ = lean_unbox(v_fmt_567_);
v_res_569_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(v_fmt_boxed_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(uint8_t v_fmt_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(v_fmt_570_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___boxed(lean_object* v_fmt_573_, lean_object* v_a_574_){
_start:
{
uint8_t v_fmt_boxed_575_; lean_object* v_res_576_; 
v_fmt_boxed_575_ = lean_unbox(v_fmt_573_);
v_res_576_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(v_fmt_boxed_575_, v_a_574_);
lean_dec_ref(v_a_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(uint8_t v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(v___y_577_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0___boxed(lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
uint8_t v___y_370__boxed_582_; lean_object* v_res_583_; 
v___y_370__boxed_582_ = lean_unbox(v___y_580_);
v_res_583_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(v___y_370__boxed_582_, v___y_581_);
lean_dec_ref(v___y_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(lean_object* v_ws_586_, lean_object* v_mod_587_, lean_object* v_facet_588_){
_start:
{
uint8_t v___x_589_; 
v___x_589_ = l_Lean_Name_isAnonymous(v_facet_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = l_Lake_Module_keyword;
lean_inc(v_facet_588_);
v___x_591_ = l_Lean_Name_append(v___x_590_, v_facet_588_);
v___x_592_ = l_Lake_Workspace_findModuleFacetConfig_x3f(v___x_591_, v_ws_586_);
if (lean_obj_tag(v___x_592_) == 1)
{
lean_object* v_lib_593_; lean_object* v_pkg_594_; lean_object* v_val_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_609_; 
lean_dec(v_facet_588_);
v_lib_593_ = lean_ctor_get(v_mod_587_, 0);
v_pkg_594_ = lean_ctor_get(v_lib_593_, 0);
v_val_595_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_609_ == 0)
{
v___x_597_ = v___x_592_;
v_isShared_598_ = v_isSharedCheck_609_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_val_595_);
lean_dec(v___x_592_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_609_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v_name_599_; lean_object* v_keyName_600_; uint8_t v_buildable_601_; lean_object* v_format_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
v_name_599_ = lean_ctor_get(v_mod_587_, 1);
v_keyName_600_ = lean_ctor_get(v_pkg_594_, 2);
v_buildable_601_ = lean_ctor_get_uint8(v_val_595_, sizeof(void*)*4);
v_format_602_ = lean_ctor_get(v_val_595_, 3);
lean_inc_ref(v_format_602_);
lean_dec(v_val_595_);
lean_inc(v_name_599_);
lean_inc(v_keyName_600_);
v___x_603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_603_, 0, v_keyName_600_);
lean_ctor_set(v___x_603_, 1, v_name_599_);
v___x_604_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___x_590_);
lean_ctor_set(v___x_604_, 2, v_mod_587_);
lean_ctor_set(v___x_604_, 3, v___x_591_);
v___x_605_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v_format_602_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*2, v_buildable_601_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_605_);
v___x_607_ = v___x_597_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec(v___x_592_);
lean_dec(v___x_591_);
lean_dec_ref(v_mod_587_);
v___x_610_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0));
v___x_611_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v_facet_588_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
}
else
{
lean_object* v_lib_613_; lean_object* v_pkg_614_; lean_object* v_name_615_; lean_object* v_keyName_616_; lean_object* v___f_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec(v_facet_588_);
v_lib_613_ = lean_ctor_get(v_mod_587_, 0);
v_pkg_614_ = lean_ctor_get(v_lib_613_, 0);
v_name_615_ = lean_ctor_get(v_mod_587_, 1);
v_keyName_616_ = lean_ctor_get(v_pkg_614_, 2);
v___f_617_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1));
v___x_618_ = l_Lake_Module_leanArtsFacet;
lean_inc(v_name_615_);
lean_inc(v_keyName_616_);
v___x_619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_619_, 0, v_keyName_616_);
lean_ctor_set(v___x_619_, 1, v_name_615_);
v___x_620_ = l_Lake_Module_keyword;
v___x_621_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
lean_ctor_set(v___x_621_, 2, v_mod_587_);
lean_ctor_set(v___x_621_, 3, v___x_618_);
v___x_622_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v___f_617_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*2, v___x_589_);
v___x_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___boxed(lean_object* v_ws_624_, lean_object* v_mod_625_, lean_object* v_facet_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_624_, v_mod_625_, v_facet_626_);
lean_dec_ref(v_ws_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(lean_object* v_pkg_628_, lean_object* v_name_629_, lean_object* v_facet_630_, lean_object* v_config_631_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = l_Lean_Name_isAnonymous(v_facet_630_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec_ref(v_config_631_);
lean_dec_ref(v_pkg_628_);
v___x_633_ = lean_alloc_ctor(20, 2, 0);
lean_ctor_set(v___x_633_, 0, v_name_629_);
lean_ctor_set(v___x_633_, 1, v_facet_630_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
else
{
lean_object* v_format_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_644_; 
lean_dec(v_facet_630_);
v_format_635_ = lean_ctor_get(v_config_631_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v_config_631_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; 
v_unused_645_ = lean_ctor_get(v_config_631_, 0);
lean_dec(v_unused_645_);
v___x_637_ = v_config_631_;
v_isShared_638_ = v_isSharedCheck_644_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_format_635_);
lean_dec(v_config_631_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_644_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_name_629_);
lean_ctor_set(v___x_637_, 0, v_pkg_628_);
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_pkg_628_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_name_629_);
v___x_640_ = v_reuseFailAlloc_643_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v_format_635_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*2, v___x_632_);
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(lean_object* v_ws_649_, lean_object* v_pkg_650_, lean_object* v_target_651_, lean_object* v_decl_652_, lean_object* v_facet_653_){
_start:
{
lean_object* v_name_654_; lean_object* v_kind_655_; lean_object* v_config_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_711_; 
v_name_654_ = lean_ctor_get(v_decl_652_, 1);
v_kind_655_ = lean_ctor_get(v_decl_652_, 2);
v_config_656_ = lean_ctor_get(v_decl_652_, 3);
v_isSharedCheck_711_ = !lean_is_exclusive(v_decl_652_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; 
v_unused_712_ = lean_ctor_get(v_decl_652_, 0);
lean_dec(v_unused_712_);
v___x_658_ = v_decl_652_;
v_isShared_659_ = v_isSharedCheck_711_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_config_656_);
lean_inc(v_kind_655_);
lean_inc(v_name_654_);
lean_dec(v_decl_652_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_711_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
uint8_t v___x_660_; 
v___x_660_ = l_Lean_Name_isAnonymous(v_kind_655_);
if (v___x_660_ == 0)
{
uint8_t v___x_661_; lean_object* v___y_663_; uint8_t v___x_689_; 
lean_dec(v_target_651_);
v___x_661_ = 1;
v___x_689_ = l_Lean_Name_isAnonymous(v_facet_653_);
if (v___x_689_ == 0)
{
v___y_663_ = v_facet_653_;
goto v___jp_662_;
}
else
{
lean_object* v___x_690_; 
lean_dec(v_facet_653_);
v___x_690_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1));
v___y_663_ = v___x_690_;
goto v___jp_662_;
}
v___jp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
lean_inc(v___y_663_);
lean_inc(v_kind_655_);
v___x_664_ = l_Lean_Name_append(v_kind_655_, v___y_663_);
v___x_665_ = l_Lake_Workspace_findFacetConfig_x3f(v___x_664_, v_ws_649_);
if (lean_obj_tag(v___x_665_) == 1)
{
lean_object* v_val_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_685_; 
lean_dec(v___y_663_);
v_val_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_685_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_685_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_val_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_685_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_keyName_670_; uint8_t v_buildable_671_; lean_object* v_format_672_; lean_object* v_tgt_673_; lean_object* v___x_674_; lean_object* v_info_676_; 
v_keyName_670_ = lean_ctor_get(v_pkg_650_, 2);
lean_inc(v_keyName_670_);
v_buildable_671_ = lean_ctor_get_uint8(v_val_666_, sizeof(void*)*4);
v_format_672_ = lean_ctor_get(v_val_666_, 3);
lean_inc_ref(v_format_672_);
lean_dec(v_val_666_);
lean_inc(v_name_654_);
v_tgt_673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_tgt_673_, 0, v_pkg_650_);
lean_ctor_set(v_tgt_673_, 1, v_name_654_);
lean_ctor_set(v_tgt_673_, 2, v_config_656_);
v___x_674_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_674_, 0, v_keyName_670_);
lean_ctor_set(v___x_674_, 1, v_name_654_);
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 1);
lean_ctor_set(v___x_658_, 3, v___x_664_);
lean_ctor_set(v___x_658_, 2, v_tgt_673_);
lean_ctor_set(v___x_658_, 1, v_kind_655_);
lean_ctor_set(v___x_658_, 0, v___x_674_);
v_info_676_ = v___x_658_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_kind_655_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v_tgt_673_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v___x_664_);
v_info_676_ = v_reuseFailAlloc_684_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_677_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_677_, 0, v_info_676_);
lean_ctor_set(v___x_677_, 1, v_format_672_);
lean_ctor_set_uint8(v___x_677_, sizeof(void*)*2, v_buildable_671_);
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_mk_empty_array_with_capacity(v___x_678_);
v___x_680_ = lean_array_push(v___x_679_, v___x_677_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_680_);
v___x_682_ = v___x_668_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_del_object(v___x_658_);
lean_dec(v_config_656_);
lean_dec(v_name_654_);
lean_dec_ref(v_pkg_650_);
v___x_686_ = l_Lean_Name_toString(v_kind_655_, v___x_661_);
v___x_687_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___y_663_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
}
else
{
lean_object* v___x_691_; 
lean_del_object(v___x_658_);
lean_dec(v_kind_655_);
lean_dec(v_name_654_);
v___x_691_ = l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(v_pkg_650_, v_target_651_, v_facet_653_, v_config_656_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_710_; 
v_a_700_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_710_ == 0)
{
v___x_702_ = v___x_691_;
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_691_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___x_706_ = lean_array_push(v___x_705_, v_a_700_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_706_);
v___x_708_ = v___x_702_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___boxed(lean_object* v_ws_713_, lean_object* v_pkg_714_, lean_object* v_target_715_, lean_object* v_decl_716_, lean_object* v_facet_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_713_, v_pkg_714_, v_target_715_, v_decl_716_, v_facet_717_);
lean_dec_ref(v_ws_713_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(lean_object* v_ws_719_, lean_object* v_pkg_720_, lean_object* v_target_721_, lean_object* v_facet_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lake_Package_findTargetDecl_x3f(v_target_721_, v_pkg_720_);
if (lean_obj_tag(v___x_723_) == 1)
{
lean_object* v_val_724_; lean_object* v___x_725_; 
v_val_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_val_724_);
lean_dec_ref(v___x_723_);
v___x_725_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_719_, v_pkg_720_, v_target_721_, v_val_724_, v_facet_722_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; 
lean_dec(v___x_723_);
lean_inc_ref(v_pkg_720_);
lean_inc(v_target_721_);
v___x_726_ = l_Lake_Package_findTargetModule_x3f(v_target_721_, v_pkg_720_);
if (lean_obj_tag(v___x_726_) == 1)
{
lean_object* v_val_727_; lean_object* v___x_728_; 
lean_dec(v_target_721_);
lean_dec_ref(v_pkg_720_);
v_val_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_val_727_);
lean_dec_ref(v___x_726_);
v___x_728_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_719_, v_val_727_, v_facet_722_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_747_; 
v_a_737_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_747_ == 0)
{
v___x_739_ = v___x_728_;
v_isShared_740_ = v_isSharedCheck_747_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_728_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_747_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = lean_mk_empty_array_with_capacity(v___x_741_);
v___x_743_ = lean_array_push(v___x_742_, v_a_737_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_743_);
v___x_745_ = v___x_739_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_baseName_748_; uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec(v___x_726_);
lean_dec(v_facet_722_);
v_baseName_748_ = lean_ctor_get(v_pkg_720_, 1);
lean_inc(v_baseName_748_);
lean_dec_ref(v_pkg_720_);
v___x_749_ = 0;
v___x_750_ = l_Lean_Name_toString(v_target_721_, v___x_749_);
v___x_751_ = lean_alloc_ctor(17, 2, 0);
lean_ctor_set(v___x_751_, 0, v_baseName_748_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage___boxed(lean_object* v_ws_753_, lean_object* v_pkg_754_, lean_object* v_target_755_, lean_object* v_facet_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_753_, v_pkg_754_, v_target_755_, v_facet_756_);
lean_dec_ref(v_ws_753_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(lean_object* v_ws_758_, lean_object* v_pkg_759_, lean_object* v_as_760_, size_t v_i_761_, size_t v_stop_762_, lean_object* v_b_763_){
_start:
{
lean_object* v_a_765_; uint8_t v___x_769_; 
v___x_769_ = lean_usize_dec_eq(v_i_761_, v_stop_762_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_array_uget_borrowed(v_as_760_, v_i_761_);
v___x_771_ = lean_box(0);
lean_inc(v___x_770_);
lean_inc_ref(v_pkg_759_);
v___x_772_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_758_, v_pkg_759_, v___x_770_, v___x_771_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_dec_ref(v_b_763_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_dec_ref(v_pkg_759_);
return v___x_772_;
}
else
{
lean_object* v_a_773_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_772_);
v_a_765_ = v_a_773_;
goto v___jp_764_;
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_775_; 
v_a_774_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_774_);
lean_dec_ref(v___x_772_);
v___x_775_ = l_Array_append___redArg(v_b_763_, v_a_774_);
lean_dec(v_a_774_);
v_a_765_ = v___x_775_;
goto v___jp_764_;
}
}
else
{
lean_object* v___x_776_; 
lean_dec_ref(v_pkg_759_);
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v_b_763_);
return v___x_776_;
}
v___jp_764_:
{
size_t v___x_766_; size_t v___x_767_; 
v___x_766_ = ((size_t)1ULL);
v___x_767_ = lean_usize_add(v_i_761_, v___x_766_);
v_i_761_ = v___x_767_;
v_b_763_ = v_a_765_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0___boxed(lean_object* v_ws_777_, lean_object* v_pkg_778_, lean_object* v_as_779_, lean_object* v_i_780_, lean_object* v_stop_781_, lean_object* v_b_782_){
_start:
{
size_t v_i_boxed_783_; size_t v_stop_boxed_784_; lean_object* v_res_785_; 
v_i_boxed_783_ = lean_unbox_usize(v_i_780_);
lean_dec(v_i_780_);
v_stop_boxed_784_ = lean_unbox_usize(v_stop_781_);
lean_dec(v_stop_781_);
v_res_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_777_, v_pkg_778_, v_as_779_, v_i_boxed_783_, v_stop_boxed_784_, v_b_782_);
lean_dec_ref(v_as_779_);
lean_dec_ref(v_ws_777_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(lean_object* v_ws_790_, lean_object* v_pkg_791_){
_start:
{
lean_object* v_defaultTargets_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_defaultTargets_792_ = lean_ctor_get(v_pkg_791_, 15);
lean_inc_ref(v_defaultTargets_792_);
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0));
v___x_795_ = lean_array_get_size(v_defaultTargets_792_);
v___x_796_ = lean_nat_dec_lt(v___x_793_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; 
lean_dec_ref(v_defaultTargets_792_);
lean_dec_ref(v_pkg_791_);
v___x_797_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1));
return v___x_797_;
}
else
{
uint8_t v___x_798_; 
v___x_798_ = lean_nat_dec_le(v___x_795_, v___x_795_);
if (v___x_798_ == 0)
{
if (v___x_796_ == 0)
{
lean_object* v___x_799_; 
lean_dec_ref(v_defaultTargets_792_);
lean_dec_ref(v_pkg_791_);
v___x_799_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1));
return v___x_799_;
}
else
{
size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; 
v___x_800_ = ((size_t)0ULL);
v___x_801_ = lean_usize_of_nat(v___x_795_);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_790_, v_pkg_791_, v_defaultTargets_792_, v___x_800_, v___x_801_, v___x_794_);
lean_dec_ref(v_defaultTargets_792_);
return v___x_802_;
}
}
else
{
size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; 
v___x_803_ = ((size_t)0ULL);
v___x_804_ = lean_usize_of_nat(v___x_795_);
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_790_, v_pkg_791_, v_defaultTargets_792_, v___x_803_, v___x_804_, v___x_794_);
lean_dec_ref(v_defaultTargets_792_);
return v___x_805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___boxed(lean_object* v_ws_806_, lean_object* v_pkg_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_806_, v_pkg_807_);
lean_dec_ref(v_ws_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(lean_object* v_ws_810_, lean_object* v_pkg_811_, lean_object* v_facet_812_){
_start:
{
uint8_t v___x_813_; 
v___x_813_ = l_Lean_Name_isAnonymous(v_facet_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = l_Lake_Package_keyword;
lean_inc(v_facet_812_);
v___x_815_ = l_Lean_Name_append(v___x_814_, v_facet_812_);
v___x_816_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v___x_815_, v_ws_810_);
if (lean_obj_tag(v___x_816_) == 1)
{
lean_object* v_val_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_facet_812_);
v_val_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_833_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_833_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_val_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_833_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v_keyName_821_; uint8_t v_buildable_822_; lean_object* v_format_823_; lean_object* v___x_825_; 
v_keyName_821_ = lean_ctor_get(v_pkg_811_, 2);
v_buildable_822_ = lean_ctor_get_uint8(v_val_817_, sizeof(void*)*4);
v_format_823_ = lean_ctor_get(v_val_817_, 3);
lean_inc_ref(v_format_823_);
lean_dec(v_val_817_);
lean_inc(v_keyName_821_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v_keyName_821_);
v___x_825_ = v___x_819_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_keyName_821_);
v___x_825_ = v_reuseFailAlloc_832_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_826_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v___x_814_);
lean_ctor_set(v___x_826_, 2, v_pkg_811_);
lean_ctor_set(v___x_826_, 3, v___x_815_);
v___x_827_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v_format_823_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*2, v_buildable_822_);
v___x_828_ = lean_unsigned_to_nat(1u);
v___x_829_ = lean_mk_empty_array_with_capacity(v___x_828_);
v___x_830_ = lean_array_push(v___x_829_, v___x_827_);
v___x_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec(v___x_816_);
lean_dec(v___x_815_);
lean_dec_ref(v_pkg_811_);
v___x_834_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0));
v___x_835_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v_facet_812_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
else
{
lean_object* v___x_837_; 
lean_dec(v_facet_812_);
v___x_837_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_810_, v_pkg_811_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___boxed(lean_object* v_ws_838_, lean_object* v_pkg_839_, lean_object* v_facet_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_838_, v_pkg_839_, v_facet_840_);
lean_dec_ref(v_ws_838_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(lean_object* v_ws_842_, lean_object* v_target_843_, lean_object* v_facet_844_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lake_Workspace_findTargetDecl_x3f(v_target_843_, v_ws_842_);
if (lean_obj_tag(v___x_870_) == 1)
{
lean_object* v_val_871_; lean_object* v_fst_872_; lean_object* v_snd_873_; lean_object* v___x_874_; 
v_val_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_val_871_);
lean_dec_ref(v___x_870_);
v_fst_872_ = lean_ctor_get(v_val_871_, 0);
lean_inc(v_fst_872_);
v_snd_873_ = lean_ctor_get(v_val_871_, 1);
lean_inc(v_snd_873_);
lean_dec(v_val_871_);
v___x_874_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_842_, v_fst_872_, v_target_843_, v_snd_873_, v_facet_844_);
return v___x_874_;
}
else
{
lean_object* v_packages_875_; lean_object* v___x_876_; size_t v_sz_877_; size_t v___x_878_; lean_object* v___x_879_; lean_object* v_fst_880_; 
lean_dec(v___x_870_);
v_packages_875_ = lean_ctor_get(v_ws_842_, 5);
v___x_876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0));
v_sz_877_ = lean_array_size(v_packages_875_);
v___x_878_ = ((size_t)0ULL);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v_target_843_, v_packages_875_, v_sz_877_, v___x_878_, v___x_876_);
v_fst_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_fst_880_);
lean_dec_ref(v___x_879_);
if (lean_obj_tag(v_fst_880_) == 0)
{
goto v___jp_845_;
}
else
{
lean_object* v_val_881_; 
v_val_881_ = lean_ctor_get(v_fst_880_, 0);
lean_inc(v_val_881_);
lean_dec_ref(v_fst_880_);
if (lean_obj_tag(v_val_881_) == 1)
{
lean_object* v_val_882_; lean_object* v___x_883_; 
lean_dec(v_target_843_);
v_val_882_ = lean_ctor_get(v_val_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref(v_val_881_);
v___x_883_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_842_, v_val_882_, v_facet_844_);
return v___x_883_;
}
else
{
lean_dec(v_val_881_);
goto v___jp_845_;
}
}
}
v___jp_845_:
{
lean_object* v___x_846_; 
lean_inc(v_target_843_);
v___x_846_ = l_Lake_Workspace_findTargetModule_x3f(v_target_843_, v_ws_842_);
if (lean_obj_tag(v___x_846_) == 1)
{
lean_object* v_val_847_; lean_object* v___x_848_; 
lean_dec(v_target_843_);
v_val_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_val_847_);
lean_dec_ref(v___x_846_);
v___x_848_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_842_, v_val_847_, v_facet_844_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_867_; 
v_a_857_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_867_ == 0)
{
v___x_859_ = v___x_848_;
v_isShared_860_ = v_isSharedCheck_867_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_848_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_867_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_mk_empty_array_with_capacity(v___x_861_);
v___x_863_ = lean_array_push(v___x_862_, v_a_857_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_863_);
v___x_865_ = v___x_859_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_dec(v___x_846_);
lean_dec(v_facet_844_);
v___x_868_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v___x_868_, 0, v_target_843_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace___boxed(lean_object* v_ws_884_, lean_object* v_target_885_, lean_object* v_facet_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(v_ws_884_, v_target_885_, v_facet_886_);
lean_dec_ref(v_ws_884_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(lean_object* v_s_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0));
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___boxed(lean_object* v_s_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v_s_892_);
lean_dec_ref(v_s_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(lean_object* v_spec_894_, lean_object* v___x_895_, lean_object* v___x_896_, lean_object* v_a_897_, lean_object* v_b_898_){
_start:
{
lean_object* v_it_900_; lean_object* v_startInclusive_901_; lean_object* v_endExclusive_902_; 
if (lean_obj_tag(v_a_897_) == 0)
{
lean_object* v_currPos_906_; lean_object* v_searcher_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_933_; 
v_currPos_906_ = lean_ctor_get(v_a_897_, 0);
v_searcher_907_ = lean_ctor_get(v_a_897_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_a_897_);
if (v_isSharedCheck_933_ == 0)
{
v___x_909_ = v_a_897_;
v_isShared_910_ = v_isSharedCheck_933_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_searcher_907_);
lean_inc(v_currPos_906_);
lean_dec(v_a_897_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_933_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v_startInclusive_911_; lean_object* v_endExclusive_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_startInclusive_911_ = lean_ctor_get(v___x_895_, 1);
v_endExclusive_912_ = lean_ctor_get(v___x_895_, 2);
v___x_913_ = lean_nat_sub(v_endExclusive_912_, v_startInclusive_911_);
v___x_914_ = lean_nat_dec_eq(v_searcher_907_, v___x_913_);
lean_dec(v___x_913_);
if (v___x_914_ == 0)
{
uint32_t v___x_915_; uint32_t v___x_916_; uint8_t v___x_917_; 
v___x_915_ = 47;
v___x_916_ = lean_string_utf8_get_fast(v_spec_894_, v_searcher_907_);
v___x_917_ = lean_uint32_dec_eq(v___x_916_, v___x_915_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = lean_string_utf8_next_fast(v_spec_894_, v_searcher_907_);
lean_dec(v_searcher_907_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v___x_918_);
v___x_920_ = v___x_909_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_currPos_906_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___x_918_);
v___x_920_ = v_reuseFailAlloc_922_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
v_a_897_ = v___x_920_;
goto _start;
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_slice_926_; lean_object* v_nextIt_928_; 
v___x_923_ = lean_string_utf8_next_fast(v_spec_894_, v_searcher_907_);
v___x_924_ = lean_nat_sub(v___x_923_, v_searcher_907_);
v___x_925_ = lean_nat_add(v_searcher_907_, v___x_924_);
lean_dec(v___x_924_);
v_slice_926_ = l_String_Slice_subslice_x21(v___x_895_, v_currPos_906_, v_searcher_907_);
lean_inc(v___x_925_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v___x_925_);
lean_ctor_set(v___x_909_, 0, v___x_925_);
v_nextIt_928_ = v___x_909_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_925_);
v_nextIt_928_ = v_reuseFailAlloc_931_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v_startInclusive_929_; lean_object* v_endExclusive_930_; 
v_startInclusive_929_ = lean_ctor_get(v_slice_926_, 0);
lean_inc(v_startInclusive_929_);
v_endExclusive_930_ = lean_ctor_get(v_slice_926_, 1);
lean_inc(v_endExclusive_930_);
lean_dec_ref(v_slice_926_);
v_it_900_ = v_nextIt_928_;
v_startInclusive_901_ = v_startInclusive_929_;
v_endExclusive_902_ = v_endExclusive_930_;
goto v___jp_899_;
}
}
}
else
{
lean_object* v___x_932_; 
lean_del_object(v___x_909_);
lean_dec(v_searcher_907_);
v___x_932_ = lean_box(1);
lean_inc(v___x_896_);
v_it_900_ = v___x_932_;
v_startInclusive_901_ = v_currPos_906_;
v_endExclusive_902_ = v___x_896_;
goto v___jp_899_;
}
}
}
else
{
lean_dec(v___x_896_);
lean_dec_ref(v_spec_894_);
return v_b_898_;
}
v___jp_899_:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_inc_ref(v_spec_894_);
v___x_903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_903_, 0, v_spec_894_);
lean_ctor_set(v___x_903_, 1, v_startInclusive_901_);
lean_ctor_set(v___x_903_, 2, v_endExclusive_902_);
v___x_904_ = lean_array_push(v_b_898_, v___x_903_);
v_a_897_ = v_it_900_;
v_b_898_ = v___x_904_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg___boxed(lean_object* v_spec_934_, lean_object* v___x_935_, lean_object* v___x_936_, lean_object* v_a_937_, lean_object* v_b_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_934_, v___x_935_, v___x_936_, v_a_937_, v_b_938_);
lean_dec_ref(v___x_935_);
return v_res_939_;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_944_ = lean_string_utf8_byte_size(v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(lean_object* v_ws_945_, lean_object* v_spec_946_, lean_object* v_facet_947_, uint8_t v_isMaybePath_948_, uint8_t v_explicit_949_){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_string_utf8_byte_size(v_spec_946_);
lean_inc_ref(v_spec_946_);
v___x_958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_958_, 0, v_spec_946_);
lean_ctor_set(v___x_958_, 1, v___x_956_);
lean_ctor_set(v___x_958_, 2, v___x_957_);
v___x_959_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v___x_958_);
v___x_960_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0));
lean_inc_ref(v_spec_946_);
v___x_961_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_946_, v___x_958_, v___x_957_, v___x_959_, v___x_960_);
lean_dec_ref(v___x_958_);
v___x_962_ = lean_array_to_list(v___x_961_);
if (lean_obj_tag(v___x_962_) == 1)
{
lean_object* v_tail_963_; 
v_tail_963_ = lean_ctor_get(v___x_962_, 1);
lean_inc(v_tail_963_);
if (lean_obj_tag(v_tail_963_) == 0)
{
lean_object* v_head_964_; lean_object* v_str_965_; lean_object* v_startInclusive_966_; lean_object* v_endExclusive_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
lean_dec_ref(v_spec_946_);
v_head_964_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_head_964_);
lean_dec_ref(v___x_962_);
v_str_965_ = lean_ctor_get(v_head_964_, 0);
lean_inc_ref(v_str_965_);
v_startInclusive_966_ = lean_ctor_get(v_head_964_, 1);
lean_inc(v_startInclusive_966_);
v_endExclusive_967_ = lean_ctor_get(v_head_964_, 2);
lean_inc(v_endExclusive_967_);
lean_dec(v_head_964_);
v___x_968_ = lean_nat_sub(v_endExclusive_967_, v_startInclusive_966_);
v___x_969_ = lean_nat_dec_eq(v___x_968_, v___x_956_);
lean_dec(v___x_968_);
if (v___x_969_ == 0)
{
if (v_explicit_949_ == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_970_ = lean_string_utf8_extract(v_str_965_, v_startInclusive_966_, v_endExclusive_967_);
lean_dec(v_endExclusive_967_);
lean_dec(v_startInclusive_966_);
lean_dec_ref(v_str_965_);
v___x_971_ = l_Lake_stringToLegalOrSimpleName(v___x_970_);
v___x_972_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(v_ws_945_, v___x_971_, v_facet_947_);
lean_dec_ref(v_ws_945_);
return v___x_972_;
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_string_utf8_extract(v_str_965_, v_startInclusive_966_, v_endExclusive_967_);
lean_dec(v_endExclusive_967_);
lean_dec(v_startInclusive_966_);
lean_dec_ref(v_str_965_);
v___x_974_ = l_Lake_parsePackageSpec(v_ws_945_, v___x_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_facet_947_);
lean_dec_ref(v_ws_945_);
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_984_; 
v_a_983_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_983_);
lean_dec_ref(v___x_974_);
v___x_984_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_945_, v_a_983_, v_facet_947_);
lean_dec_ref(v_ws_945_);
return v___x_984_;
}
}
}
else
{
lean_object* v_root_985_; lean_object* v___x_986_; 
lean_dec(v_endExclusive_967_);
lean_dec(v_startInclusive_966_);
lean_dec_ref(v_str_965_);
v_root_985_ = lean_ctor_get(v_ws_945_, 0);
lean_inc_ref(v_root_985_);
v___x_986_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_945_, v_root_985_, v_facet_947_);
lean_dec_ref(v_ws_945_);
return v___x_986_;
}
}
else
{
lean_object* v_tail_987_; 
v_tail_987_ = lean_ctor_get(v_tail_963_, 1);
if (lean_obj_tag(v_tail_987_) == 0)
{
lean_object* v_head_988_; lean_object* v_head_989_; lean_object* v_str_990_; lean_object* v_startInclusive_991_; lean_object* v_endExclusive_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec_ref(v_spec_946_);
v_head_988_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_head_988_);
lean_dec_ref(v___x_962_);
v_head_989_ = lean_ctor_get(v_tail_963_, 0);
lean_inc(v_head_989_);
lean_dec_ref(v_tail_963_);
v_str_990_ = lean_ctor_get(v_head_988_, 0);
lean_inc_ref(v_str_990_);
v_startInclusive_991_ = lean_ctor_get(v_head_988_, 1);
lean_inc(v_startInclusive_991_);
v_endExclusive_992_ = lean_ctor_get(v_head_988_, 2);
lean_inc(v_endExclusive_992_);
lean_dec(v_head_988_);
v___x_993_ = lean_string_utf8_extract(v_str_990_, v_startInclusive_991_, v_endExclusive_992_);
lean_dec(v_endExclusive_992_);
lean_dec(v_startInclusive_991_);
lean_dec_ref(v_str_990_);
v___x_994_ = l_Lake_parsePackageSpec(v_ws_945_, v___x_993_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_head_989_);
lean_dec(v_facet_947_);
lean_dec_ref(v_ws_945_);
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1052_; 
v_a_1003_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1005_ = v___x_994_;
v_isShared_1006_ = v_isSharedCheck_1052_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_994_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1052_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_str_1007_; lean_object* v_startInclusive_1008_; lean_object* v_endExclusive_1009_; uint8_t v___y_1011_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_str_1007_ = lean_ctor_get(v_head_989_, 0);
lean_inc_ref(v_str_1007_);
v_startInclusive_1008_ = lean_ctor_get(v_head_989_, 1);
lean_inc(v_startInclusive_1008_);
v_endExclusive_1009_ = lean_ctor_get(v_head_989_, 2);
lean_inc(v_endExclusive_1009_);
v___x_1045_ = lean_nat_sub(v_endExclusive_1009_, v_startInclusive_1008_);
v___x_1046_ = lean_nat_dec_eq(v___x_1045_, v___x_956_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_1048_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2, &l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2);
v___x_1049_ = lean_nat_dec_le(v___x_1048_, v___x_1045_);
lean_dec(v___x_1045_);
if (v___x_1049_ == 0)
{
v___y_1011_ = v___x_1046_;
goto v___jp_1010_;
}
else
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_string_memcmp(v_str_1007_, v___x_1047_, v_startInclusive_1008_, v___x_956_, v___x_1048_);
v___y_1011_ = v___x_1050_;
goto v___jp_1010_;
}
}
else
{
lean_object* v___x_1051_; 
lean_dec(v___x_1045_);
lean_dec(v_endExclusive_1009_);
lean_dec(v_startInclusive_1008_);
lean_dec_ref(v_str_1007_);
lean_del_object(v___x_1005_);
lean_dec(v_head_989_);
v___x_1051_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_945_, v_a_1003_, v_facet_947_);
lean_dec_ref(v_ws_945_);
return v___x_1051_;
}
v___jp_1010_:
{
if (v___y_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_del_object(v___x_1005_);
lean_dec(v_head_989_);
v___x_1012_ = lean_string_utf8_extract(v_str_1007_, v_startInclusive_1008_, v_endExclusive_1009_);
lean_dec(v_endExclusive_1009_);
lean_dec(v_startInclusive_1008_);
lean_dec_ref(v_str_1007_);
v___x_1013_ = l_Lake_stringToLegalOrSimpleName(v___x_1012_);
v___x_1014_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_945_, v_a_1003_, v___x_1013_, v_facet_947_);
lean_dec_ref(v_ws_945_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = l_String_Slice_Pos_nextn(v_head_989_, v___x_956_, v___x_1015_);
lean_dec(v_head_989_);
v___x_1017_ = lean_nat_add(v_startInclusive_1008_, v___x_1016_);
lean_dec(v___x_1016_);
lean_dec(v_startInclusive_1008_);
v___x_1018_ = lean_string_utf8_extract(v_str_1007_, v___x_1017_, v_endExclusive_1009_);
lean_dec(v_endExclusive_1009_);
lean_dec(v___x_1017_);
lean_dec_ref(v_str_1007_);
v___x_1019_ = l_String_toName(v___x_1018_);
lean_inc(v___x_1019_);
v___x_1020_ = l_Lake_Package_findTargetModule_x3f(v___x_1019_, v_a_1003_);
if (lean_obj_tag(v___x_1020_) == 1)
{
lean_object* v_val_1021_; lean_object* v___x_1022_; 
lean_dec(v___x_1019_);
lean_del_object(v___x_1005_);
v_val_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_val_1021_);
lean_dec_ref(v___x_1020_);
v___x_1022_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_945_, v_val_1021_, v_facet_947_);
lean_dec_ref(v_ws_945_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1040_; 
v_a_1031_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1033_ = v___x_1022_;
v_isShared_1034_ = v_isSharedCheck_1040_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1022_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1040_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1035_ = lean_mk_empty_array_with_capacity(v___x_1015_);
v___x_1036_ = lean_array_push(v___x_1035_, v_a_1031_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1036_);
v___x_1038_ = v___x_1033_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1043_; 
lean_dec(v___x_1020_);
lean_dec(v_facet_947_);
lean_dec_ref(v_ws_945_);
v___x_1041_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1019_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set_tag(v___x_1005_, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1041_);
v___x_1043_ = v___x_1005_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_tail_963_);
lean_dec_ref(v___x_962_);
lean_dec(v_facet_947_);
lean_dec_ref(v_ws_945_);
goto v___jp_950_;
}
}
}
else
{
lean_dec(v___x_962_);
lean_dec(v_facet_947_);
lean_dec_ref(v_ws_945_);
goto v___jp_950_;
}
v___jp_950_:
{
if (v_isMaybePath_948_ == 0)
{
uint32_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = 47;
v___x_952_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_952_, 0, v_spec_946_);
lean_ctor_set_uint32(v___x_952_, sizeof(void*)*1, v___x_951_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_954_, 0, v_spec_946_);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___boxed(lean_object* v_ws_1053_, lean_object* v_spec_1054_, lean_object* v_facet_1055_, lean_object* v_isMaybePath_1056_, lean_object* v_explicit_1057_){
_start:
{
uint8_t v_isMaybePath_boxed_1058_; uint8_t v_explicit_boxed_1059_; lean_object* v_res_1060_; 
v_isMaybePath_boxed_1058_ = lean_unbox(v_isMaybePath_1056_);
v_explicit_boxed_1059_ = lean_unbox(v_explicit_1057_);
v_res_1060_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1053_, v_spec_1054_, v_facet_1055_, v_isMaybePath_boxed_1058_, v_explicit_boxed_1059_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(lean_object* v_spec_1061_, lean_object* v___x_1062_, lean_object* v___x_1063_, lean_object* v_inst_1064_, lean_object* v_R_1065_, lean_object* v_a_1066_, lean_object* v_b_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_1061_, v___x_1062_, v___x_1063_, v_a_1066_, v_b_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___boxed(lean_object* v_spec_1069_, lean_object* v___x_1070_, lean_object* v___x_1071_, lean_object* v_inst_1072_, lean_object* v_R_1073_, lean_object* v_a_1074_, lean_object* v_b_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(v_spec_1069_, v___x_1070_, v___x_1071_, v_inst_1072_, v_R_1073_, v_a_1074_, v_b_1075_);
lean_dec_ref(v___x_1070_);
return v_res_1076_;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1079_ = lean_string_utf8_byte_size(v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(lean_object* v_ws_1080_, lean_object* v_spec_1081_, lean_object* v_facet_1082_){
_start:
{
uint8_t v___y_1085_; uint8_t v___y_1086_; uint8_t v___y_1166_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1202_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1203_ = lean_string_utf8_byte_size(v_spec_1081_);
v___x_1204_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1, &l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1);
v___x_1205_ = lean_nat_dec_le(v___x_1204_, v___x_1203_);
if (v___x_1205_ == 0)
{
v___y_1166_ = v___x_1205_;
goto v___jp_1165_;
}
else
{
lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = lean_unsigned_to_nat(0u);
v___x_1207_ = lean_string_memcmp(v_spec_1081_, v___x_1202_, v___x_1206_, v___x_1206_, v___x_1204_);
if (v___x_1207_ == 0)
{
v___y_1166_ = v___x_1207_;
goto v___jp_1165_;
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; 
v___x_1208_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_spec_1081_);
v___x_1209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1209_, 0, v_spec_1081_);
lean_ctor_set(v___x_1209_, 1, v___x_1206_);
lean_ctor_set(v___x_1209_, 2, v___x_1203_);
v___x_1210_ = l_String_Slice_Pos_nextn(v___x_1209_, v___x_1206_, v___x_1208_);
lean_dec_ref(v___x_1209_);
v___x_1211_ = lean_string_utf8_extract(v_spec_1081_, v___x_1210_, v___x_1203_);
lean_dec(v___x_1210_);
lean_dec_ref(v_spec_1081_);
v___x_1212_ = 0;
v___x_1213_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1080_, v___x_1211_, v_facet_1082_, v___x_1212_, v___x_1207_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set_tag(v___x_1216_, 1);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
v_a_1222_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1213_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1213_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set_tag(v___x_1224_, 0);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
v___jp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
lean_inc_ref(v_spec_1081_);
v___x_1087_ = l_Lake_resolvePath(v_spec_1081_);
v___x_1088_ = lean_string_utf8_byte_size(v___x_1087_);
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = lean_nat_dec_eq(v___x_1088_, v___x_1089_);
if (v___x_1090_ == 0)
{
uint8_t v___x_1091_; 
v___x_1091_ = l_System_FilePath_isDir(v___x_1087_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lake_Workspace_findModuleBySrc_x3f(v___x_1087_, v_ws_1080_);
if (lean_obj_tag(v___x_1092_) == 1)
{
lean_object* v_val_1093_; lean_object* v___x_1094_; 
lean_dec_ref(v_spec_1081_);
v_val_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_val_1093_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_1080_, v_val_1093_, v_facet_1082_);
lean_dec_ref(v_ws_1080_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
lean_ctor_set_tag(v___x_1097_, 1);
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1113_; 
v_a_1103_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1105_ = v___x_1094_;
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1094_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1107_ = lean_unsigned_to_nat(1u);
v___x_1108_ = lean_mk_empty_array_with_capacity(v___x_1107_);
v___x_1109_ = lean_array_push(v___x_1108_, v_a_1103_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1109_);
v___x_1111_ = v___x_1105_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v___x_1114_; 
lean_dec(v___x_1092_);
v___x_1114_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1080_, v_spec_1081_, v_facet_1082_, v___y_1085_, v___x_1091_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 1);
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
v_a_1123_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1114_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1114_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 0);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
else
{
lean_object* v___x_1131_; 
lean_dec_ref(v___x_1087_);
v___x_1131_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1080_, v_spec_1081_, v_facet_1082_, v___y_1086_, v___y_1086_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 1);
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
v_a_1140_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1131_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1131_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set_tag(v___x_1142_, 0);
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
else
{
lean_object* v___x_1148_; 
lean_dec_ref(v___x_1087_);
v___x_1148_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1080_, v_spec_1081_, v_facet_1082_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 1);
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_a_1157_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1148_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1148_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set_tag(v___x_1159_, 0);
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
v___jp_1165_:
{
uint8_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1167_ = 1;
v___x_1168_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_1169_ = lean_string_utf8_byte_size(v_spec_1081_);
v___x_1170_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2, &l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2);
v___x_1171_ = lean_nat_dec_le(v___x_1170_, v___x_1169_);
if (v___x_1171_ == 0)
{
v___y_1085_ = v___x_1167_;
v___y_1086_ = v___y_1166_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = lean_string_memcmp(v_spec_1081_, v___x_1168_, v___x_1172_, v___x_1172_, v___x_1170_);
if (v___x_1173_ == 0)
{
v___y_1085_ = v___x_1167_;
v___y_1086_ = v___x_1173_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_mod_1178_; lean_object* v___x_1179_; 
v___x_1174_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_spec_1081_);
v___x_1175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1175_, 0, v_spec_1081_);
lean_ctor_set(v___x_1175_, 1, v___x_1172_);
lean_ctor_set(v___x_1175_, 2, v___x_1169_);
v___x_1176_ = l_String_Slice_Pos_nextn(v___x_1175_, v___x_1172_, v___x_1174_);
lean_dec_ref(v___x_1175_);
v___x_1177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1177_, 0, v_spec_1081_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
lean_ctor_set(v___x_1177_, 2, v___x_1169_);
v_mod_1178_ = l_String_Slice_toName(v___x_1177_);
lean_dec_ref(v___x_1177_);
lean_inc(v_mod_1178_);
v___x_1179_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_1178_, v_ws_1080_);
if (lean_obj_tag(v___x_1179_) == 1)
{
lean_object* v_val_1180_; lean_object* v___x_1181_; 
lean_dec(v_mod_1178_);
v_val_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_val_1180_);
lean_dec_ref(v___x_1179_);
v___x_1181_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_1080_, v_val_1180_, v_facet_1082_);
lean_dec_ref(v_ws_1080_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
lean_ctor_set_tag(v___x_1184_, 1);
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1199_; 
v_a_1190_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1192_ = v___x_1181_;
v_isShared_1193_ = v_isSharedCheck_1199_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1181_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1199_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1194_ = lean_mk_empty_array_with_capacity(v___x_1174_);
v___x_1195_ = lean_array_push(v___x_1194_, v_a_1190_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set_tag(v___x_1192_, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1195_);
v___x_1197_ = v___x_1192_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_dec(v___x_1179_);
lean_dec(v_facet_1082_);
lean_dec_ref(v_ws_1080_);
v___x_1200_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1200_, 0, v_mod_1178_);
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___boxed(lean_object* v_ws_1230_, lean_object* v_spec_1231_, lean_object* v_facet_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1230_, v_spec_1231_, v_facet_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object* v_ws_1235_, lean_object* v_spec_1236_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_string_utf8_byte_size(v_spec_1236_);
lean_inc_ref(v_spec_1236_);
v___x_1246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1246_, 0, v_spec_1236_);
lean_ctor_set(v___x_1246_, 1, v___x_1244_);
lean_ctor_set(v___x_1246_, 2, v___x_1245_);
v___x_1247_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v___x_1246_);
v___x_1248_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0));
lean_inc_ref(v_spec_1236_);
v___x_1249_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_1236_, v___x_1246_, v___x_1245_, v___x_1247_, v___x_1248_);
lean_dec_ref(v___x_1246_);
v___x_1250_ = lean_array_to_list(v___x_1249_);
if (lean_obj_tag(v___x_1250_) == 1)
{
lean_object* v_tail_1251_; 
v_tail_1251_ = lean_ctor_get(v___x_1250_, 1);
lean_inc(v_tail_1251_);
if (lean_obj_tag(v_tail_1251_) == 0)
{
lean_object* v_head_1252_; lean_object* v_str_1253_; lean_object* v_startInclusive_1254_; lean_object* v_endExclusive_1255_; lean_object* v___x_1256_; lean_object* v_targetName_1257_; lean_object* v___x_1258_; 
v_head_1252_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_head_1252_);
lean_dec_ref(v___x_1250_);
v_str_1253_ = lean_ctor_get(v_head_1252_, 0);
lean_inc_ref(v_str_1253_);
v_startInclusive_1254_ = lean_ctor_get(v_head_1252_, 1);
lean_inc(v_startInclusive_1254_);
v_endExclusive_1255_ = lean_ctor_get(v_head_1252_, 2);
lean_inc(v_endExclusive_1255_);
lean_dec(v_head_1252_);
v___x_1256_ = lean_string_utf8_extract(v_str_1253_, v_startInclusive_1254_, v_endExclusive_1255_);
lean_dec(v_endExclusive_1255_);
lean_dec(v_startInclusive_1254_);
lean_dec_ref(v_str_1253_);
v_targetName_1257_ = l_Lake_stringToLegalOrSimpleName(v___x_1256_);
v___x_1258_ = l_Lake_Workspace_findLeanExe_x3f(v_targetName_1257_, v_ws_1235_);
lean_dec(v_targetName_1257_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_1259_, 0, v_spec_1236_);
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
else
{
lean_object* v_val_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec_ref(v_spec_1236_);
v_val_1261_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1258_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_val_1261_);
lean_dec(v___x_1258_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_val_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_object* v_head_1269_; lean_object* v_head_1270_; lean_object* v_tail_1271_; lean_object* v_str_1273_; lean_object* v_startInclusive_1274_; lean_object* v_endExclusive_1275_; 
v_head_1269_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_head_1269_);
lean_dec_ref(v___x_1250_);
v_head_1270_ = lean_ctor_get(v_tail_1251_, 0);
lean_inc(v_head_1270_);
v_tail_1271_ = lean_ctor_get(v_tail_1251_, 1);
lean_inc(v_tail_1271_);
lean_dec_ref(v_tail_1251_);
if (lean_obj_tag(v_tail_1271_) == 0)
{
lean_object* v_str_1313_; lean_object* v_startInclusive_1314_; lean_object* v_endExclusive_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_str_1313_ = lean_ctor_get(v_head_1269_, 0);
lean_inc_ref(v_str_1313_);
v_startInclusive_1314_ = lean_ctor_get(v_head_1269_, 1);
lean_inc(v_startInclusive_1314_);
v_endExclusive_1315_ = lean_ctor_get(v_head_1269_, 2);
lean_inc(v_endExclusive_1315_);
v___x_1316_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1317_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1, &l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1);
v___x_1318_ = lean_nat_sub(v_endExclusive_1315_, v_startInclusive_1314_);
v___x_1319_ = lean_nat_dec_le(v___x_1317_, v___x_1318_);
lean_dec(v___x_1318_);
if (v___x_1319_ == 0)
{
lean_dec(v_head_1269_);
v_str_1273_ = v_str_1313_;
v_startInclusive_1274_ = v_startInclusive_1314_;
v_endExclusive_1275_ = v_endExclusive_1315_;
goto v___jp_1272_;
}
else
{
uint8_t v___x_1320_; 
v___x_1320_ = lean_string_memcmp(v_str_1313_, v___x_1316_, v_startInclusive_1314_, v___x_1244_, v___x_1317_);
if (v___x_1320_ == 0)
{
lean_dec(v_head_1269_);
v_str_1273_ = v_str_1313_;
v_startInclusive_1274_ = v_startInclusive_1314_;
v_endExclusive_1275_ = v_endExclusive_1315_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = lean_unsigned_to_nat(1u);
v___x_1322_ = l_String_Slice_Pos_nextn(v_head_1269_, v___x_1244_, v___x_1321_);
lean_dec(v_head_1269_);
v___x_1323_ = lean_nat_add(v_startInclusive_1314_, v___x_1322_);
lean_dec(v___x_1322_);
lean_dec(v_startInclusive_1314_);
v_str_1273_ = v_str_1313_;
v_startInclusive_1274_ = v___x_1323_;
v_endExclusive_1275_ = v_endExclusive_1315_;
goto v___jp_1272_;
}
}
}
else
{
lean_dec(v_tail_1271_);
lean_dec(v_head_1270_);
lean_dec(v_head_1269_);
goto v___jp_1240_;
}
v___jp_1272_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_string_utf8_extract(v_str_1273_, v_startInclusive_1274_, v_endExclusive_1275_);
lean_dec(v_endExclusive_1275_);
lean_dec(v_startInclusive_1274_);
lean_dec_ref(v_str_1273_);
v___x_1277_ = l_Lake_parsePackageSpec(v_ws_1235_, v___x_1276_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v_head_1270_);
lean_dec_ref(v_spec_1236_);
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1312_; 
v_a_1286_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1288_ = v___x_1277_;
v_isShared_1289_ = v_isSharedCheck_1312_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1277_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1312_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v_str_1290_; lean_object* v_startInclusive_1291_; lean_object* v_endExclusive_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1311_; 
v_str_1290_ = lean_ctor_get(v_head_1270_, 0);
v_startInclusive_1291_ = lean_ctor_get(v_head_1270_, 1);
v_endExclusive_1292_ = lean_ctor_get(v_head_1270_, 2);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_head_1270_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1294_ = v_head_1270_;
v_isShared_1295_ = v_isSharedCheck_1311_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_endExclusive_1292_);
lean_inc(v_startInclusive_1291_);
lean_inc(v_str_1290_);
lean_dec(v_head_1270_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1311_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_string_utf8_extract(v_str_1290_, v_startInclusive_1291_, v_endExclusive_1292_);
lean_dec(v_endExclusive_1292_);
lean_dec(v_startInclusive_1291_);
lean_dec_ref(v_str_1290_);
v___x_1297_ = l_Lake_stringToLegalOrSimpleName(v___x_1296_);
v___x_1298_ = l_Lake_Package_findTargetDecl_x3f(v___x_1297_, v_a_1286_);
lean_dec(v___x_1297_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_del_object(v___x_1294_);
lean_del_object(v___x_1288_);
lean_dec(v_a_1286_);
goto v___jp_1237_;
}
else
{
lean_object* v_val_1299_; lean_object* v_name_1300_; lean_object* v_kind_1301_; lean_object* v_config_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v_val_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_val_1299_);
lean_dec_ref(v___x_1298_);
v_name_1300_ = lean_ctor_get(v_val_1299_, 1);
lean_inc(v_name_1300_);
v_kind_1301_ = lean_ctor_get(v_val_1299_, 2);
lean_inc(v_kind_1301_);
v_config_1302_ = lean_ctor_get(v_val_1299_, 3);
lean_inc(v_config_1302_);
lean_dec(v_val_1299_);
v___x_1303_ = l_Lake_LeanExe_keyword;
v___x_1304_ = lean_name_eq(v_kind_1301_, v___x_1303_);
lean_dec(v_kind_1301_);
if (v___x_1304_ == 0)
{
lean_dec(v_config_1302_);
lean_dec(v_name_1300_);
lean_del_object(v___x_1294_);
lean_del_object(v___x_1288_);
lean_dec(v_a_1286_);
goto v___jp_1237_;
}
else
{
lean_object* v___x_1306_; 
lean_dec_ref(v_spec_1236_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 2, v_config_1302_);
lean_ctor_set(v___x_1294_, 1, v_name_1300_);
lean_ctor_set(v___x_1294_, 0, v_a_1286_);
v___x_1306_ = v___x_1294_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1286_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_name_1300_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_config_1302_);
v___x_1306_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1306_);
v___x_1308_ = v___x_1288_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
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
lean_dec(v___x_1250_);
goto v___jp_1240_;
}
v___jp_1237_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_1238_, 0, v_spec_1236_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
v___jp_1240_:
{
uint32_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = 47;
v___x_1242_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_1242_, 0, v_spec_1236_);
lean_ctor_set_uint32(v___x_1242_, sizeof(void*)*1, v___x_1241_);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed(lean_object* v_ws_1324_, lean_object* v_spec_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lake_parseExeTargetSpec(v_ws_1324_, v_spec_1325_);
lean_dec_ref(v_ws_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(lean_object* v_s_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0));
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___boxed(lean_object* v_s_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(v_s_1329_);
lean_dec_ref(v_s_1329_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(lean_object* v_spec_1331_, lean_object* v___x_1332_, lean_object* v___x_1333_, lean_object* v_a_1334_, lean_object* v_b_1335_){
_start:
{
lean_object* v_it_1337_; lean_object* v_startInclusive_1338_; lean_object* v_endExclusive_1339_; 
if (lean_obj_tag(v_a_1334_) == 0)
{
lean_object* v_currPos_1344_; lean_object* v_searcher_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1371_; 
v_currPos_1344_ = lean_ctor_get(v_a_1334_, 0);
v_searcher_1345_ = lean_ctor_get(v_a_1334_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_a_1334_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1347_ = v_a_1334_;
v_isShared_1348_ = v_isSharedCheck_1371_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_searcher_1345_);
lean_inc(v_currPos_1344_);
lean_dec(v_a_1334_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1371_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v_startInclusive_1349_; lean_object* v_endExclusive_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_startInclusive_1349_ = lean_ctor_get(v___x_1332_, 1);
v_endExclusive_1350_ = lean_ctor_get(v___x_1332_, 2);
v___x_1351_ = lean_nat_sub(v_endExclusive_1350_, v_startInclusive_1349_);
v___x_1352_ = lean_nat_dec_eq(v_searcher_1345_, v___x_1351_);
lean_dec(v___x_1351_);
if (v___x_1352_ == 0)
{
uint32_t v___x_1353_; uint32_t v___x_1354_; uint8_t v___x_1355_; 
v___x_1353_ = 58;
v___x_1354_ = lean_string_utf8_get_fast(v_spec_1331_, v_searcher_1345_);
v___x_1355_ = lean_uint32_dec_eq(v___x_1354_, v___x_1353_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = lean_string_utf8_next_fast(v_spec_1331_, v_searcher_1345_);
lean_dec(v_searcher_1345_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v___x_1356_);
v___x_1358_ = v___x_1347_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_currPos_1344_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
v_a_1334_ = v___x_1358_;
goto _start;
}
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v_slice_1364_; lean_object* v_nextIt_1366_; 
v___x_1361_ = lean_string_utf8_next_fast(v_spec_1331_, v_searcher_1345_);
v___x_1362_ = lean_nat_sub(v___x_1361_, v_searcher_1345_);
v___x_1363_ = lean_nat_add(v_searcher_1345_, v___x_1362_);
lean_dec(v___x_1362_);
v_slice_1364_ = l_String_Slice_subslice_x21(v___x_1332_, v_currPos_1344_, v_searcher_1345_);
lean_inc(v___x_1363_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v___x_1363_);
lean_ctor_set(v___x_1347_, 0, v___x_1363_);
v_nextIt_1366_ = v___x_1347_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v___x_1363_);
v_nextIt_1366_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v_startInclusive_1367_; lean_object* v_endExclusive_1368_; 
v_startInclusive_1367_ = lean_ctor_get(v_slice_1364_, 0);
lean_inc(v_startInclusive_1367_);
v_endExclusive_1368_ = lean_ctor_get(v_slice_1364_, 1);
lean_inc(v_endExclusive_1368_);
lean_dec_ref(v_slice_1364_);
v_it_1337_ = v_nextIt_1366_;
v_startInclusive_1338_ = v_startInclusive_1367_;
v_endExclusive_1339_ = v_endExclusive_1368_;
goto v___jp_1336_;
}
}
}
else
{
lean_object* v___x_1370_; 
lean_del_object(v___x_1347_);
lean_dec(v_searcher_1345_);
v___x_1370_ = lean_box(1);
lean_inc(v___x_1333_);
v_it_1337_ = v___x_1370_;
v_startInclusive_1338_ = v_currPos_1344_;
v_endExclusive_1339_ = v___x_1333_;
goto v___jp_1336_;
}
}
}
else
{
lean_dec(v___x_1333_);
lean_dec_ref(v_spec_1331_);
return v_b_1335_;
}
v___jp_1336_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_inc_ref(v_spec_1331_);
v___x_1340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1340_, 0, v_spec_1331_);
lean_ctor_set(v___x_1340_, 1, v_startInclusive_1338_);
lean_ctor_set(v___x_1340_, 2, v_endExclusive_1339_);
v___x_1341_ = l_String_Slice_toString(v___x_1340_);
lean_dec_ref(v___x_1340_);
v___x_1342_ = lean_array_push(v_b_1335_, v___x_1341_);
v_a_1334_ = v_it_1337_;
v_b_1335_ = v___x_1342_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg___boxed(lean_object* v_spec_1372_, lean_object* v___x_1373_, lean_object* v___x_1374_, lean_object* v_a_1375_, lean_object* v_b_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1372_, v___x_1373_, v___x_1374_, v_a_1375_, v_b_1376_);
lean_dec_ref(v___x_1373_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec(lean_object* v_ws_1380_, lean_object* v_spec_1381_){
_start:
{
uint32_t v___x_1383_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1383_ = 58;
v___x_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = lean_string_utf8_byte_size(v_spec_1381_);
lean_inc_ref(v_spec_1381_);
v___x_1389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1389_, 0, v_spec_1381_);
lean_ctor_set(v___x_1389_, 1, v___x_1387_);
lean_ctor_set(v___x_1389_, 2, v___x_1388_);
v___x_1390_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(v___x_1389_);
v___x_1391_ = ((lean_object*)(l_Lake_parseTargetSpec___closed__0));
lean_inc_ref(v_spec_1381_);
v___x_1392_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1381_, v___x_1389_, v___x_1388_, v___x_1390_, v___x_1391_);
lean_dec_ref(v___x_1389_);
v___x_1393_ = lean_array_to_list(v___x_1392_);
if (lean_obj_tag(v___x_1393_) == 1)
{
lean_object* v_tail_1394_; 
v_tail_1394_ = lean_ctor_get(v___x_1393_, 1);
lean_inc(v_tail_1394_);
if (lean_obj_tag(v_tail_1394_) == 0)
{
lean_object* v_head_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec_ref(v_spec_1381_);
v_head_1395_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_head_1395_);
lean_dec_ref(v___x_1393_);
v___x_1396_ = lean_box(0);
v___x_1397_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1380_, v_head_1395_, v___x_1396_);
return v___x_1397_;
}
else
{
lean_object* v_tail_1398_; 
v_tail_1398_ = lean_ctor_get(v_tail_1394_, 1);
if (lean_obj_tag(v_tail_1398_) == 0)
{
lean_object* v_head_1399_; lean_object* v_head_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec_ref(v_spec_1381_);
v_head_1399_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_head_1399_);
lean_dec_ref(v___x_1393_);
v_head_1400_ = lean_ctor_get(v_tail_1394_, 0);
lean_inc(v_head_1400_);
lean_dec_ref(v_tail_1394_);
v___x_1401_ = l_String_toName(v_head_1400_);
v___x_1402_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1380_, v_head_1399_, v___x_1401_);
return v___x_1402_;
}
else
{
lean_dec_ref(v_tail_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v_ws_1380_);
goto v___jp_1384_;
}
}
}
else
{
lean_dec(v___x_1393_);
lean_dec_ref(v_ws_1380_);
goto v___jp_1384_;
}
v___jp_1384_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_1385_, 0, v_spec_1381_);
lean_ctor_set_uint32(v___x_1385_, sizeof(void*)*1, v___x_1383_);
v___x_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec___boxed(lean_object* v_ws_1403_, lean_object* v_spec_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lake_parseTargetSpec(v_ws_1403_, v_spec_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(lean_object* v_spec_1407_, lean_object* v___x_1408_, lean_object* v___x_1409_, lean_object* v_inst_1410_, lean_object* v_R_1411_, lean_object* v_a_1412_, lean_object* v_b_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1407_, v___x_1408_, v___x_1409_, v_a_1412_, v_b_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___boxed(lean_object* v_spec_1415_, lean_object* v___x_1416_, lean_object* v___x_1417_, lean_object* v_inst_1418_, lean_object* v_R_1419_, lean_object* v_a_1420_, lean_object* v_b_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(v_spec_1415_, v___x_1416_, v___x_1417_, v_inst_1418_, v_R_1419_, v_a_1420_, v_b_1421_);
lean_dec_ref(v___x_1416_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(lean_object* v_ws_1423_, lean_object* v_as_x27_1424_, lean_object* v_b_1425_){
_start:
{
if (lean_obj_tag(v_as_x27_1424_) == 0)
{
lean_object* v___x_1427_; 
lean_dec_ref(v_ws_1423_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v_b_1425_);
return v___x_1427_;
}
else
{
lean_object* v_head_1428_; lean_object* v_tail_1429_; lean_object* v___x_1430_; 
v_head_1428_ = lean_ctor_get(v_as_x27_1424_, 0);
lean_inc(v_head_1428_);
v_tail_1429_ = lean_ctor_get(v_as_x27_1424_, 1);
lean_inc(v_tail_1429_);
lean_dec_ref(v_as_x27_1424_);
lean_inc_ref(v_ws_1423_);
v___x_1430_ = l_Lake_parseTargetSpec(v_ws_1423_, v_head_1428_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref(v___x_1430_);
v___x_1432_ = l_Array_append___redArg(v_b_1425_, v_a_1431_);
lean_dec(v_a_1431_);
v_as_x27_1424_ = v_tail_1429_;
v_b_1425_ = v___x_1432_;
goto _start;
}
else
{
lean_dec(v_tail_1429_);
lean_dec_ref(v_b_1425_);
lean_dec_ref(v_ws_1423_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg___boxed(lean_object* v_ws_1434_, lean_object* v_as_x27_1435_, lean_object* v_b_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1434_, v_as_x27_1435_, v_b_1436_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs(lean_object* v_ws_1441_, lean_object* v_specs_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v_results_1445_; lean_object* v___x_1446_; 
v___x_1444_ = lean_unsigned_to_nat(0u);
v_results_1445_ = ((lean_object*)(l_Lake_parseTargetSpecs___closed__0));
lean_inc_ref(v_ws_1441_);
v___x_1446_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1441_, v_specs_1442_, v_results_1445_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
v___x_1448_ = lean_array_get_size(v_a_1447_);
lean_dec(v_a_1447_);
v___x_1449_ = lean_nat_dec_eq(v___x_1448_, v___x_1444_);
if (v___x_1449_ == 0)
{
lean_dec_ref(v_ws_1441_);
return v___x_1446_;
}
else
{
lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1463_; 
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v___x_1446_, 0);
lean_dec(v_unused_1464_);
v___x_1451_ = v___x_1446_;
v_isShared_1452_ = v_isSharedCheck_1463_;
goto v_resetjp_1450_;
}
else
{
lean_dec(v___x_1446_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1463_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_root_1453_; lean_object* v___x_1454_; 
v_root_1453_ = lean_ctor_get(v_ws_1441_, 0);
lean_inc_ref(v_root_1453_);
v___x_1454_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_1441_, v_root_1453_);
lean_dec_ref(v_ws_1441_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref(v___x_1454_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set_tag(v___x_1451_, 1);
lean_ctor_set(v___x_1451_, 0, v_a_1455_);
v___x_1457_ = v___x_1451_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; 
v_a_1459_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1459_);
lean_dec_ref(v___x_1454_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v_a_1459_);
v___x_1461_ = v___x_1451_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
else
{
lean_dec_ref(v_ws_1441_);
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___boxed(lean_object* v_ws_1465_, lean_object* v_specs_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lake_parseTargetSpecs(v_ws_1465_, v_specs_1466_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(lean_object* v_ws_1469_, lean_object* v_as_1470_, lean_object* v_as_x27_1471_, lean_object* v_b_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1469_, v_as_x27_1471_, v_b_1472_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___boxed(lean_object* v_ws_1476_, lean_object* v_as_1477_, lean_object* v_as_x27_1478_, lean_object* v_b_1479_, lean_object* v_a_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(v_ws_1476_, v_as_1477_, v_as_x27_1478_, v_b_1479_, v_a_1480_);
lean_dec(v_as_1477_);
return v_res_1482_;
}
}
lean_object* runtime_initialize_Lake_CLI_Error(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Build(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_CLI_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Register(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_Build(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_CLI_Error(uint8_t builtin);
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
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
res = initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Build(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Build(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Build(builtin);
}
#ifdef __cplusplus
}
#endif
