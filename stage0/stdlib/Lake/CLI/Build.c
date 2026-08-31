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
lean_object* l_Lake_FacetConfigMap_get_x3f(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lake_Package_keyword;
lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
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
lean_inc_ref_n(v_info_41_, 2);
lean_dec_ref(v_self_33_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc(v_a_36_);
lean_inc(v_a_35_);
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
v_registeredJobs_57_ = lean_ctor_get(v_a_38_, 4);
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
v___x_66_ = lean_st_ref_put(v_registeredJobs_57_, v___x_65_);
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
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch___boxed(lean_object* v_self_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lake_BuildSpec_fetch(v_self_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec(v_a_79_);
lean_dec(v_a_78_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build(lean_object* v_self_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_a_94_; lean_object* v_a_95_; lean_object* v_info_98_; lean_object* v___x_99_; 
v_info_98_ = lean_ctor_get(v_self_85_, 0);
lean_inc_ref_n(v_info_98_, 2);
lean_dec_ref(v_self_85_);
lean_inc_ref(v_a_90_);
lean_inc(v_a_89_);
lean_inc(v_a_88_);
lean_inc(v_a_87_);
v___x_99_ = lean_apply_7(v_a_86_, v_info_98_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, lean_box(0));
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v_a_101_; lean_object* v_task_102_; lean_object* v_kind_103_; lean_object* v_caption_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
v_a_101_ = lean_ctor_get(v___x_99_, 1);
lean_inc(v_a_101_);
lean_dec_ref_known(v___x_99_, 2);
v_task_102_ = lean_ctor_get(v_a_100_, 0);
v_kind_103_ = lean_ctor_get(v_a_100_, 1);
v_caption_104_ = lean_ctor_get(v_a_100_, 2);
v___x_105_ = lean_string_utf8_byte_size(v_caption_104_);
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_nat_dec_eq(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_dec_ref(v_info_98_);
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
v_registeredJobs_111_ = lean_ctor_get(v_a_90_, 4);
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
v___x_120_ = lean_st_ref_put(v_registeredJobs_111_, v___x_119_);
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
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec(v_a_130_);
lean_dec(v_a_129_);
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
lean_inc_ref_n(v_info_173_, 2);
v_format_174_ = lean_ctor_get(v_self_164_, 1);
lean_inc_ref(v_format_174_);
lean_dec_ref(v_self_164_);
v___x_175_ = l_Lake_BuildInfo_key(v_info_173_);
lean_inc_ref(v_a_170_);
lean_inc(v_a_169_);
lean_inc(v_a_168_);
lean_inc(v_a_167_);
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
v_registeredJobs_202_ = lean_ctor_get(v_a_170_, 4);
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
v___x_209_ = lean_st_ref_put(v_registeredJobs_202_, v___x_208_);
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
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec(v_a_231_);
lean_dec(v_a_230_);
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
lean_inc_ref_n(v_info_251_, 2);
lean_inc_ref(v___y_241_);
lean_inc_ref(v___y_245_);
lean_inc(v___y_244_);
lean_inc(v___y_243_);
lean_inc(v___y_242_);
v___x_252_ = lean_apply_7(v___y_241_, v_info_251_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, lean_box(0));
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v_a_254_; lean_object* v_task_255_; lean_object* v_kind_256_; lean_object* v_caption_257_; lean_object* v___x_258_; lean_object* v_bs_x27_259_; lean_object* v_a_261_; lean_object* v_a_262_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
v_a_254_ = lean_ctor_get(v___x_252_, 1);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_252_, 2);
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
v_registeredJobs_273_ = lean_ctor_get(v___y_245_, 4);
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
v___x_282_ = lean_st_ref_put(v_registeredJobs_273_, v___x_281_);
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
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec(v___y_303_);
lean_dec(v___y_302_);
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
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec(v_a_346_);
lean_dec(v_a_345_);
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
lean_inc_ref_n(v_info_394_, 2);
v___x_396_ = l_Lake_BuildInfo_key(v_info_394_);
lean_inc_ref(v___y_384_);
lean_inc_ref(v___y_388_);
lean_inc(v___y_387_);
lean_inc(v___y_386_);
lean_inc(v___y_385_);
v___x_397_ = lean_apply_7(v___y_384_, v_info_394_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, lean_box(0));
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v_a_399_; lean_object* v_task_400_; lean_object* v_caption_401_; uint8_t v_optional_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_435_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
v_a_399_ = lean_ctor_get(v___x_397_, 1);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_397_, 2);
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
v_registeredJobs_425_ = lean_ctor_get(v___y_388_, 4);
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
v___x_432_ = lean_st_ref_put(v_registeredJobs_425_, v___x_431_);
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
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec(v___y_452_);
lean_dec(v___y_451_);
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
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec(v_a_497_);
lean_dec(v_a_496_);
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
lean_inc_ref(v_b_511_);
return v_b_511_;
}
else
{
lean_object* v_a_513_; lean_object* v_baseName_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
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
lean_dec_ref(v_b_528_);
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
v_packages_540_ = lean_ctor_get(v_ws_532_, 4);
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
lean_dec_ref_known(v_fst_546_, 1);
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
lean_object* v_packages_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec_ref(v_spec_533_);
v_packages_556_ = lean_ctor_get(v_ws_532_, 4);
v___x_557_ = lean_array_fget_borrowed(v_packages_556_, v___x_538_);
lean_inc(v___x_557_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
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
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec___boxed(lean_object* v_ws_559_, lean_object* v_spec_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lake_parsePackageSpec(v_ws_559_, v_spec_560_);
lean_dec_ref(v_ws_559_);
return v_res_561_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_box(0);
v___x_564_ = l_Lean_Json_compress(v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(uint8_t v_fmt_565_){
_start:
{
if (v_fmt_565_ == 0)
{
lean_object* v___x_566_; 
v___x_566_ = ((lean_object*)(l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0));
return v___x_566_;
}
else
{
lean_object* v___x_567_; 
v___x_567_ = lean_obj_once(&l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1, &l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1_once, _init_l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___boxed(lean_object* v_fmt_568_){
_start:
{
uint8_t v_fmt_boxed_569_; lean_object* v_res_570_; 
v_fmt_boxed_569_ = lean_unbox(v_fmt_568_);
v_res_570_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(v_fmt_boxed_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(uint8_t v_fmt_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(v_fmt_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___boxed(lean_object* v_fmt_574_, lean_object* v_a_575_){
_start:
{
uint8_t v_fmt_boxed_576_; lean_object* v_res_577_; 
v_fmt_boxed_576_ = lean_unbox(v_fmt_574_);
v_res_577_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(v_fmt_boxed_576_, v_a_575_);
lean_dec_ref(v_a_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(uint8_t v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(v___y_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0___boxed(lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
uint8_t v___y_282__boxed_583_; lean_object* v_res_584_; 
v___y_282__boxed_583_ = lean_unbox(v___y_581_);
v_res_584_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(v___y_282__boxed_583_, v___y_582_);
lean_dec_ref(v___y_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(lean_object* v_ws_587_, lean_object* v_mod_588_, lean_object* v_facet_589_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = l_Lean_Name_isAnonymous(v_facet_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = l_Lake_Module_keyword;
lean_inc(v_facet_589_);
v___x_592_ = l_Lean_Name_append(v___x_591_, v_facet_589_);
v___x_593_ = l_Lake_Workspace_findModuleFacetConfig_x3f(v___x_592_, v_ws_587_);
if (lean_obj_tag(v___x_593_) == 1)
{
lean_object* v_lib_594_; lean_object* v_pkg_595_; lean_object* v_val_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_610_; 
lean_dec(v_facet_589_);
v_lib_594_ = lean_ctor_get(v_mod_588_, 0);
v_pkg_595_ = lean_ctor_get(v_lib_594_, 0);
v_val_596_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_610_ == 0)
{
v___x_598_ = v___x_593_;
v_isShared_599_ = v_isSharedCheck_610_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_val_596_);
lean_dec(v___x_593_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_610_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_name_600_; lean_object* v_keyName_601_; uint8_t v_buildable_602_; lean_object* v_format_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v_name_600_ = lean_ctor_get(v_mod_588_, 1);
v_keyName_601_ = lean_ctor_get(v_pkg_595_, 2);
v_buildable_602_ = lean_ctor_get_uint8(v_val_596_, sizeof(void*)*4);
v_format_603_ = lean_ctor_get(v_val_596_, 3);
lean_inc_ref(v_format_603_);
lean_dec(v_val_596_);
lean_inc(v_name_600_);
lean_inc(v_keyName_601_);
v___x_604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_604_, 0, v_keyName_601_);
lean_ctor_set(v___x_604_, 1, v_name_600_);
v___x_605_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_591_);
lean_ctor_set(v___x_605_, 2, v_mod_588_);
lean_ctor_set(v___x_605_, 3, v___x_592_);
v___x_606_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v_format_603_);
lean_ctor_set_uint8(v___x_606_, sizeof(void*)*2, v_buildable_602_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_606_);
v___x_608_ = v___x_598_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v___x_593_);
lean_dec(v___x_592_);
lean_dec_ref(v_mod_588_);
v___x_611_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0));
v___x_612_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v_facet_589_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
else
{
lean_object* v_lib_614_; lean_object* v_pkg_615_; lean_object* v_name_616_; lean_object* v_keyName_617_; lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
lean_dec(v_facet_589_);
v_lib_614_ = lean_ctor_get(v_mod_588_, 0);
v_pkg_615_ = lean_ctor_get(v_lib_614_, 0);
v_name_616_ = lean_ctor_get(v_mod_588_, 1);
v_keyName_617_ = lean_ctor_get(v_pkg_615_, 2);
v___f_618_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1));
v___x_619_ = l_Lake_Module_leanArtsFacet;
lean_inc(v_name_616_);
lean_inc(v_keyName_617_);
v___x_620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_620_, 0, v_keyName_617_);
lean_ctor_set(v___x_620_, 1, v_name_616_);
v___x_621_ = l_Lake_Module_keyword;
v___x_622_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
lean_ctor_set(v___x_622_, 2, v_mod_588_);
lean_ctor_set(v___x_622_, 3, v___x_619_);
v___x_623_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v___f_618_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*2, v___x_590_);
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___boxed(lean_object* v_ws_625_, lean_object* v_mod_626_, lean_object* v_facet_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_625_, v_mod_626_, v_facet_627_);
lean_dec_ref(v_ws_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(lean_object* v_pkg_629_, lean_object* v_name_630_, lean_object* v_facet_631_, lean_object* v_config_632_){
_start:
{
uint8_t v___x_633_; 
v___x_633_ = l_Lean_Name_isAnonymous(v_facet_631_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec_ref(v_config_632_);
lean_dec_ref(v_pkg_629_);
v___x_634_ = lean_alloc_ctor(20, 2, 0);
lean_ctor_set(v___x_634_, 0, v_name_630_);
lean_ctor_set(v___x_634_, 1, v_facet_631_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
else
{
lean_object* v_format_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_645_; 
lean_dec(v_facet_631_);
v_format_636_ = lean_ctor_get(v_config_632_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_config_632_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v_config_632_, 0);
lean_dec(v_unused_646_);
v___x_638_ = v_config_632_;
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_format_636_);
lean_dec(v_config_632_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v_name_630_);
lean_ctor_set(v___x_638_, 0, v_pkg_629_);
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_pkg_629_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_name_630_);
v___x_641_ = v_reuseFailAlloc_644_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v_format_636_);
lean_ctor_set_uint8(v___x_642_, sizeof(void*)*2, v___x_633_);
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(lean_object* v_ws_650_, lean_object* v_pkg_651_, lean_object* v_target_652_, lean_object* v_decl_653_, lean_object* v_facet_654_){
_start:
{
lean_object* v_name_655_; lean_object* v_kind_656_; lean_object* v_config_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_713_; 
v_name_655_ = lean_ctor_get(v_decl_653_, 1);
v_kind_656_ = lean_ctor_get(v_decl_653_, 2);
v_config_657_ = lean_ctor_get(v_decl_653_, 3);
v_isSharedCheck_713_ = !lean_is_exclusive(v_decl_653_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; 
v_unused_714_ = lean_ctor_get(v_decl_653_, 0);
lean_dec(v_unused_714_);
v___x_659_ = v_decl_653_;
v_isShared_660_ = v_isSharedCheck_713_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_config_657_);
lean_inc(v_kind_656_);
lean_inc(v_name_655_);
lean_dec(v_decl_653_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_713_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
uint8_t v___x_661_; 
v___x_661_ = l_Lean_Name_isAnonymous(v_kind_656_);
if (v___x_661_ == 0)
{
uint8_t v___x_662_; lean_object* v___y_664_; uint8_t v___x_691_; 
lean_dec(v_target_652_);
v___x_662_ = 1;
v___x_691_ = l_Lean_Name_isAnonymous(v_facet_654_);
if (v___x_691_ == 0)
{
v___y_664_ = v_facet_654_;
goto v___jp_663_;
}
else
{
lean_object* v___x_692_; 
lean_dec(v_facet_654_);
v___x_692_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1));
v___y_664_ = v___x_692_;
goto v___jp_663_;
}
v___jp_663_:
{
lean_object* v_facetConfigs_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_facetConfigs_665_ = lean_ctor_get(v_ws_650_, 6);
lean_inc(v___y_664_);
lean_inc(v_kind_656_);
v___x_666_ = l_Lean_Name_append(v_kind_656_, v___y_664_);
v___x_667_ = l_Lake_FacetConfigMap_get_x3f(v___x_666_, v_facetConfigs_665_);
if (lean_obj_tag(v___x_667_) == 1)
{
lean_object* v_val_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_687_; 
lean_dec(v___y_664_);
v_val_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_687_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_687_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_val_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_687_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_keyName_672_; uint8_t v_buildable_673_; lean_object* v_format_674_; lean_object* v_tgt_675_; lean_object* v___x_676_; lean_object* v_info_678_; 
v_keyName_672_ = lean_ctor_get(v_pkg_651_, 2);
lean_inc(v_keyName_672_);
v_buildable_673_ = lean_ctor_get_uint8(v_val_668_, sizeof(void*)*4);
v_format_674_ = lean_ctor_get(v_val_668_, 3);
lean_inc_ref(v_format_674_);
lean_dec(v_val_668_);
lean_inc(v_name_655_);
v_tgt_675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_tgt_675_, 0, v_pkg_651_);
lean_ctor_set(v_tgt_675_, 1, v_name_655_);
lean_ctor_set(v_tgt_675_, 2, v_config_657_);
v___x_676_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_676_, 0, v_keyName_672_);
lean_ctor_set(v___x_676_, 1, v_name_655_);
if (v_isShared_660_ == 0)
{
lean_ctor_set_tag(v___x_659_, 1);
lean_ctor_set(v___x_659_, 3, v___x_666_);
lean_ctor_set(v___x_659_, 2, v_tgt_675_);
lean_ctor_set(v___x_659_, 1, v_kind_656_);
lean_ctor_set(v___x_659_, 0, v___x_676_);
v_info_678_ = v___x_659_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_kind_656_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_tgt_675_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v___x_666_);
v_info_678_ = v_reuseFailAlloc_686_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_679_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_679_, 0, v_info_678_);
lean_ctor_set(v___x_679_, 1, v_format_674_);
lean_ctor_set_uint8(v___x_679_, sizeof(void*)*2, v_buildable_673_);
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_mk_empty_array_with_capacity(v___x_680_);
v___x_682_ = lean_array_push(v___x_681_, v___x_679_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_682_);
v___x_684_ = v___x_670_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec(v___x_667_);
lean_dec(v___x_666_);
lean_del_object(v___x_659_);
lean_dec(v_config_657_);
lean_dec(v_name_655_);
lean_dec_ref(v_pkg_651_);
v___x_688_ = l_Lean_Name_toString(v_kind_656_, v___x_662_);
v___x_689_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___y_664_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
}
else
{
lean_object* v___x_693_; 
lean_del_object(v___x_659_);
lean_dec(v_kind_656_);
lean_dec(v_name_655_);
v___x_693_ = l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(v_pkg_651_, v_target_652_, v_facet_654_, v_config_657_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_712_; 
v_a_702_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_712_ == 0)
{
v___x_704_ = v___x_693_;
v_isShared_705_ = v_isSharedCheck_712_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_693_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_712_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___x_708_ = lean_array_push(v___x_707_, v_a_702_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_708_);
v___x_710_ = v___x_704_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___boxed(lean_object* v_ws_715_, lean_object* v_pkg_716_, lean_object* v_target_717_, lean_object* v_decl_718_, lean_object* v_facet_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_715_, v_pkg_716_, v_target_717_, v_decl_718_, v_facet_719_);
lean_dec_ref(v_ws_715_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(lean_object* v_ws_721_, lean_object* v_pkg_722_, lean_object* v_target_723_, lean_object* v_facet_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lake_Package_findTargetDecl_x3f(v_target_723_, v_pkg_722_);
if (lean_obj_tag(v___x_725_) == 1)
{
lean_object* v_val_726_; lean_object* v___x_727_; 
v_val_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_721_, v_pkg_722_, v_target_723_, v_val_726_, v_facet_724_);
return v___x_727_;
}
else
{
lean_object* v___x_728_; 
lean_dec(v___x_725_);
lean_inc_ref(v_pkg_722_);
lean_inc(v_target_723_);
v___x_728_ = l_Lake_Package_findTargetModule_x3f(v_target_723_, v_pkg_722_);
if (lean_obj_tag(v___x_728_) == 1)
{
lean_object* v_val_729_; lean_object* v___x_730_; 
lean_dec(v_target_723_);
lean_dec_ref(v_pkg_722_);
v_val_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_val_729_);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_721_, v_val_729_, v_facet_724_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_749_; 
v_a_739_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_749_ == 0)
{
v___x_741_ = v___x_730_;
v_isShared_742_ = v_isSharedCheck_749_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_730_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_749_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = lean_mk_empty_array_with_capacity(v___x_743_);
v___x_745_ = lean_array_push(v___x_744_, v_a_739_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_745_);
v___x_747_ = v___x_741_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v_baseName_750_; uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v___x_728_);
lean_dec(v_facet_724_);
v_baseName_750_ = lean_ctor_get(v_pkg_722_, 1);
lean_inc(v_baseName_750_);
lean_dec_ref(v_pkg_722_);
v___x_751_ = 0;
v___x_752_ = l_Lean_Name_toString(v_target_723_, v___x_751_);
v___x_753_ = lean_alloc_ctor(17, 2, 0);
lean_ctor_set(v___x_753_, 0, v_baseName_750_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage___boxed(lean_object* v_ws_755_, lean_object* v_pkg_756_, lean_object* v_target_757_, lean_object* v_facet_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_755_, v_pkg_756_, v_target_757_, v_facet_758_);
lean_dec_ref(v_ws_755_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(lean_object* v_ws_760_, lean_object* v_pkg_761_, lean_object* v_as_762_, size_t v_i_763_, size_t v_stop_764_, lean_object* v_b_765_){
_start:
{
lean_object* v_a_767_; uint8_t v___x_771_; 
v___x_771_ = lean_usize_dec_eq(v_i_763_, v_stop_764_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = lean_array_uget_borrowed(v_as_762_, v_i_763_);
v___x_773_ = lean_box(0);
lean_inc(v___x_772_);
lean_inc_ref(v_pkg_761_);
v___x_774_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_760_, v_pkg_761_, v___x_772_, v___x_773_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_dec_ref(v_b_765_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_dec_ref(v_pkg_761_);
return v___x_774_;
}
else
{
lean_object* v_a_775_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
v_a_767_ = v_a_775_;
goto v___jp_766_;
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_777_; 
v_a_776_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_774_, 1);
v___x_777_ = l_Array_append___redArg(v_b_765_, v_a_776_);
lean_dec(v_a_776_);
v_a_767_ = v___x_777_;
goto v___jp_766_;
}
}
else
{
lean_object* v___x_778_; 
lean_dec_ref(v_pkg_761_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v_b_765_);
return v___x_778_;
}
v___jp_766_:
{
size_t v___x_768_; size_t v___x_769_; 
v___x_768_ = ((size_t)1ULL);
v___x_769_ = lean_usize_add(v_i_763_, v___x_768_);
v_i_763_ = v___x_769_;
v_b_765_ = v_a_767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0___boxed(lean_object* v_ws_779_, lean_object* v_pkg_780_, lean_object* v_as_781_, lean_object* v_i_782_, lean_object* v_stop_783_, lean_object* v_b_784_){
_start:
{
size_t v_i_boxed_785_; size_t v_stop_boxed_786_; lean_object* v_res_787_; 
v_i_boxed_785_ = lean_unbox_usize(v_i_782_);
lean_dec(v_i_782_);
v_stop_boxed_786_ = lean_unbox_usize(v_stop_783_);
lean_dec(v_stop_783_);
v_res_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_779_, v_pkg_780_, v_as_781_, v_i_boxed_785_, v_stop_boxed_786_, v_b_784_);
lean_dec_ref(v_as_781_);
lean_dec_ref(v_ws_779_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(lean_object* v_ws_792_, lean_object* v_pkg_793_){
_start:
{
lean_object* v_defaultTargets_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v_defaultTargets_794_ = lean_ctor_get(v_pkg_793_, 17);
lean_inc_ref(v_defaultTargets_794_);
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0));
v___x_797_ = lean_array_get_size(v_defaultTargets_794_);
v___x_798_ = lean_nat_dec_lt(v___x_795_, v___x_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
lean_dec_ref(v_defaultTargets_794_);
lean_dec_ref(v_pkg_793_);
v___x_799_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1));
return v___x_799_;
}
else
{
size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; 
v___x_800_ = ((size_t)0ULL);
v___x_801_ = lean_usize_of_nat(v___x_797_);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_792_, v_pkg_793_, v_defaultTargets_794_, v___x_800_, v___x_801_, v___x_796_);
lean_dec_ref(v_defaultTargets_794_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___boxed(lean_object* v_ws_803_, lean_object* v_pkg_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_803_, v_pkg_804_);
lean_dec_ref(v_ws_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(lean_object* v_ws_807_, lean_object* v_pkg_808_, lean_object* v_facet_809_){
_start:
{
uint8_t v___x_810_; 
v___x_810_ = l_Lean_Name_isAnonymous(v_facet_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = l_Lake_Package_keyword;
lean_inc(v_facet_809_);
v___x_812_ = l_Lean_Name_append(v___x_811_, v_facet_809_);
v___x_813_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v___x_812_, v_ws_807_);
if (lean_obj_tag(v___x_813_) == 1)
{
lean_object* v_val_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_facet_809_);
v_val_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_830_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_830_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_val_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_830_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_keyName_818_; uint8_t v_buildable_819_; lean_object* v_format_820_; lean_object* v___x_822_; 
v_keyName_818_ = lean_ctor_get(v_pkg_808_, 2);
v_buildable_819_ = lean_ctor_get_uint8(v_val_814_, sizeof(void*)*4);
v_format_820_ = lean_ctor_get(v_val_814_, 3);
lean_inc_ref(v_format_820_);
lean_dec(v_val_814_);
lean_inc(v_keyName_818_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v_keyName_818_);
v___x_822_ = v___x_816_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_keyName_818_);
v___x_822_ = v_reuseFailAlloc_829_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_823_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_811_);
lean_ctor_set(v___x_823_, 2, v_pkg_808_);
lean_ctor_set(v___x_823_, 3, v___x_812_);
v___x_824_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v_format_820_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*2, v_buildable_819_);
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = lean_mk_empty_array_with_capacity(v___x_825_);
v___x_827_ = lean_array_push(v___x_826_, v___x_824_);
v___x_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec(v___x_813_);
lean_dec(v___x_812_);
lean_dec_ref(v_pkg_808_);
v___x_831_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0));
v___x_832_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v_facet_809_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
else
{
lean_object* v___x_834_; 
lean_dec(v_facet_809_);
v___x_834_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_807_, v_pkg_808_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___boxed(lean_object* v_ws_835_, lean_object* v_pkg_836_, lean_object* v_facet_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_835_, v_pkg_836_, v_facet_837_);
lean_dec_ref(v_ws_835_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(lean_object* v_ws_839_, lean_object* v_target_840_, lean_object* v_facet_841_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lake_Workspace_findTargetDecl_x3f(v_target_840_, v_ws_839_);
if (lean_obj_tag(v___x_867_) == 1)
{
lean_object* v_val_868_; lean_object* v_fst_869_; lean_object* v_snd_870_; lean_object* v___x_871_; 
v_val_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_val_868_);
lean_dec_ref_known(v___x_867_, 1);
v_fst_869_ = lean_ctor_get(v_val_868_, 0);
lean_inc(v_fst_869_);
v_snd_870_ = lean_ctor_get(v_val_868_, 1);
lean_inc(v_snd_870_);
lean_dec(v_val_868_);
v___x_871_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_839_, v_fst_869_, v_target_840_, v_snd_870_, v_facet_841_);
return v___x_871_;
}
else
{
lean_object* v_packages_872_; lean_object* v___x_873_; size_t v_sz_874_; size_t v___x_875_; lean_object* v___x_876_; lean_object* v_fst_877_; 
lean_dec(v___x_867_);
v_packages_872_ = lean_ctor_get(v_ws_839_, 4);
v___x_873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0));
v_sz_874_ = lean_array_size(v_packages_872_);
v___x_875_ = ((size_t)0ULL);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v_target_840_, v_packages_872_, v_sz_874_, v___x_875_, v___x_873_);
v_fst_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_fst_877_);
lean_dec_ref(v___x_876_);
if (lean_obj_tag(v_fst_877_) == 0)
{
goto v___jp_842_;
}
else
{
lean_object* v_val_878_; 
v_val_878_ = lean_ctor_get(v_fst_877_, 0);
lean_inc(v_val_878_);
lean_dec_ref_known(v_fst_877_, 1);
if (lean_obj_tag(v_val_878_) == 1)
{
lean_object* v_val_879_; lean_object* v___x_880_; 
lean_dec(v_target_840_);
v_val_879_ = lean_ctor_get(v_val_878_, 0);
lean_inc(v_val_879_);
lean_dec_ref_known(v_val_878_, 1);
v___x_880_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_839_, v_val_879_, v_facet_841_);
return v___x_880_;
}
else
{
lean_dec(v_val_878_);
goto v___jp_842_;
}
}
}
v___jp_842_:
{
lean_object* v___x_843_; 
lean_inc(v_target_840_);
v___x_843_ = l_Lake_Workspace_findTargetModule_x3f(v_target_840_, v_ws_839_);
if (lean_obj_tag(v___x_843_) == 1)
{
lean_object* v_val_844_; lean_object* v___x_845_; 
lean_dec(v_target_840_);
v_val_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_val_844_);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_839_, v_val_844_, v_facet_841_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_864_; 
v_a_854_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_864_ == 0)
{
v___x_856_ = v___x_845_;
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_845_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_858_ = lean_unsigned_to_nat(1u);
v___x_859_ = lean_mk_empty_array_with_capacity(v___x_858_);
v___x_860_ = lean_array_push(v___x_859_, v_a_854_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_860_);
v___x_862_ = v___x_856_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec(v___x_843_);
lean_dec(v_facet_841_);
v___x_865_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v___x_865_, 0, v_target_840_);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace___boxed(lean_object* v_ws_881_, lean_object* v_target_882_, lean_object* v_facet_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(v_ws_881_, v_target_882_, v_facet_883_);
lean_dec_ref(v_ws_881_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(lean_object* v_s_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0));
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___boxed(lean_object* v_s_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v_s_889_);
lean_dec_ref(v_s_889_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(lean_object* v_spec_891_, lean_object* v___x_892_, lean_object* v___x_893_, lean_object* v_a_894_, lean_object* v_b_895_){
_start:
{
lean_object* v_it_897_; lean_object* v_startInclusive_898_; lean_object* v_endExclusive_899_; 
if (lean_obj_tag(v_a_894_) == 0)
{
lean_object* v_currPos_903_; lean_object* v_searcher_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_927_; 
v_currPos_903_ = lean_ctor_get(v_a_894_, 0);
v_searcher_904_ = lean_ctor_get(v_a_894_, 1);
v_isSharedCheck_927_ = !lean_is_exclusive(v_a_894_);
if (v_isSharedCheck_927_ == 0)
{
v___x_906_ = v_a_894_;
v_isShared_907_ = v_isSharedCheck_927_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_searcher_904_);
lean_inc(v_currPos_903_);
lean_dec(v_a_894_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_927_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
uint8_t v_decide_908_; 
v_decide_908_ = lean_nat_dec_eq(v_searcher_904_, v___x_893_);
if (v_decide_908_ == 0)
{
uint32_t v___x_909_; uint32_t v___x_910_; uint8_t v___x_911_; 
v___x_909_ = 47;
v___x_910_ = lean_string_utf8_get_fast(v_spec_891_, v_searcher_904_);
v___x_911_ = lean_uint32_dec_eq(v___x_910_, v___x_909_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = lean_string_utf8_next_fast(v_spec_891_, v_searcher_904_);
lean_dec(v_searcher_904_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v___x_912_);
v___x_914_ = v___x_906_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_currPos_903_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v___x_912_);
v___x_914_ = v_reuseFailAlloc_916_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
v_a_894_ = v___x_914_;
goto _start;
}
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v_slice_920_; lean_object* v_nextIt_922_; 
v___x_917_ = lean_string_utf8_next_fast(v_spec_891_, v_searcher_904_);
v___x_918_ = lean_nat_sub(v___x_917_, v_searcher_904_);
v___x_919_ = lean_nat_add(v_searcher_904_, v___x_918_);
lean_dec(v___x_918_);
v_slice_920_ = l_String_Slice_subslice_x21(v___x_892_, v_currPos_903_, v_searcher_904_);
lean_inc(v___x_919_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v___x_919_);
lean_ctor_set(v___x_906_, 0, v___x_919_);
v_nextIt_922_ = v___x_906_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_919_);
v_nextIt_922_ = v_reuseFailAlloc_925_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v_startInclusive_923_; lean_object* v_endExclusive_924_; 
v_startInclusive_923_ = lean_ctor_get(v_slice_920_, 0);
lean_inc(v_startInclusive_923_);
v_endExclusive_924_ = lean_ctor_get(v_slice_920_, 1);
lean_inc(v_endExclusive_924_);
lean_dec_ref(v_slice_920_);
v_it_897_ = v_nextIt_922_;
v_startInclusive_898_ = v_startInclusive_923_;
v_endExclusive_899_ = v_endExclusive_924_;
goto v___jp_896_;
}
}
}
else
{
lean_object* v___x_926_; 
lean_del_object(v___x_906_);
lean_dec(v_searcher_904_);
v___x_926_ = lean_box(1);
lean_inc(v___x_893_);
v_it_897_ = v___x_926_;
v_startInclusive_898_ = v_currPos_903_;
v_endExclusive_899_ = v___x_893_;
goto v___jp_896_;
}
}
}
else
{
lean_dec(v___x_893_);
lean_dec_ref(v_spec_891_);
return v_b_895_;
}
v___jp_896_:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_inc_ref(v_spec_891_);
v___x_900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_900_, 0, v_spec_891_);
lean_ctor_set(v___x_900_, 1, v_startInclusive_898_);
lean_ctor_set(v___x_900_, 2, v_endExclusive_899_);
v___x_901_ = lean_array_push(v_b_895_, v___x_900_);
v_a_894_ = v_it_897_;
v_b_895_ = v___x_901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg___boxed(lean_object* v_spec_928_, lean_object* v___x_929_, lean_object* v___x_930_, lean_object* v_a_931_, lean_object* v_b_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_928_, v___x_929_, v___x_930_, v_a_931_, v_b_932_);
lean_dec_ref(v___x_929_);
return v_res_933_;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_938_ = lean_string_utf8_byte_size(v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(lean_object* v_ws_939_, lean_object* v_spec_940_, lean_object* v_facet_941_, uint8_t v_isMaybePath_942_, uint8_t v_explicit_943_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_string_utf8_byte_size(v_spec_940_);
lean_inc_ref_n(v_spec_940_, 2);
v___x_952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_952_, 0, v_spec_940_);
lean_ctor_set(v___x_952_, 1, v___x_950_);
lean_ctor_set(v___x_952_, 2, v___x_951_);
v___x_953_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v___x_952_);
v___x_954_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0));
v___x_955_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_940_, v___x_952_, v___x_951_, v___x_953_, v___x_954_);
lean_dec_ref_known(v___x_952_, 3);
v___x_956_ = lean_array_to_list(v___x_955_);
if (lean_obj_tag(v___x_956_) == 1)
{
lean_object* v_tail_957_; 
v_tail_957_ = lean_ctor_get(v___x_956_, 1);
lean_inc(v_tail_957_);
if (lean_obj_tag(v_tail_957_) == 0)
{
lean_object* v_head_958_; lean_object* v_str_959_; lean_object* v_startInclusive_960_; lean_object* v_endExclusive_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
lean_dec_ref(v_spec_940_);
v_head_958_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_head_958_);
lean_dec_ref_known(v___x_956_, 2);
v_str_959_ = lean_ctor_get(v_head_958_, 0);
lean_inc_ref(v_str_959_);
v_startInclusive_960_ = lean_ctor_get(v_head_958_, 1);
lean_inc(v_startInclusive_960_);
v_endExclusive_961_ = lean_ctor_get(v_head_958_, 2);
lean_inc(v_endExclusive_961_);
lean_dec(v_head_958_);
v___x_962_ = lean_nat_sub(v_endExclusive_961_, v_startInclusive_960_);
v___x_963_ = lean_nat_dec_eq(v___x_962_, v___x_950_);
lean_dec(v___x_962_);
if (v___x_963_ == 0)
{
if (v_explicit_943_ == 0)
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = lean_string_utf8_extract_fast(v_str_959_, v_startInclusive_960_, v_endExclusive_961_);
lean_dec(v_endExclusive_961_);
lean_dec(v_startInclusive_960_);
lean_dec_ref(v_str_959_);
v___x_965_ = l_Lake_stringToLegalOrSimpleName(v___x_964_);
v___x_966_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(v_ws_939_, v___x_965_, v_facet_941_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_string_utf8_extract_fast(v_str_959_, v_startInclusive_960_, v_endExclusive_961_);
lean_dec(v_endExclusive_961_);
lean_dec(v_startInclusive_960_);
lean_dec_ref(v_str_959_);
v___x_968_ = l_Lake_parsePackageSpec(v_ws_939_, v___x_967_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec(v_facet_941_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_978_; 
v_a_977_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_968_, 1);
v___x_978_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_939_, v_a_977_, v_facet_941_);
return v___x_978_;
}
}
}
else
{
lean_object* v_packages_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
lean_dec(v_endExclusive_961_);
lean_dec(v_startInclusive_960_);
lean_dec_ref(v_str_959_);
v_packages_979_ = lean_ctor_get(v_ws_939_, 4);
v___x_980_ = lean_array_fget_borrowed(v_packages_979_, v___x_950_);
lean_inc(v___x_980_);
v___x_981_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_939_, v___x_980_, v_facet_941_);
return v___x_981_;
}
}
else
{
lean_object* v_tail_982_; 
v_tail_982_ = lean_ctor_get(v_tail_957_, 1);
if (lean_obj_tag(v_tail_982_) == 0)
{
lean_object* v_head_983_; lean_object* v_head_984_; lean_object* v_str_985_; lean_object* v_startInclusive_986_; lean_object* v_endExclusive_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec_ref(v_spec_940_);
v_head_983_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_head_983_);
lean_dec_ref_known(v___x_956_, 2);
v_head_984_ = lean_ctor_get(v_tail_957_, 0);
lean_inc(v_head_984_);
lean_dec_ref_known(v_tail_957_, 2);
v_str_985_ = lean_ctor_get(v_head_983_, 0);
lean_inc_ref(v_str_985_);
v_startInclusive_986_ = lean_ctor_get(v_head_983_, 1);
lean_inc(v_startInclusive_986_);
v_endExclusive_987_ = lean_ctor_get(v_head_983_, 2);
lean_inc(v_endExclusive_987_);
lean_dec(v_head_983_);
v___x_988_ = lean_string_utf8_extract_fast(v_str_985_, v_startInclusive_986_, v_endExclusive_987_);
lean_dec(v_endExclusive_987_);
lean_dec(v_startInclusive_986_);
lean_dec_ref(v_str_985_);
v___x_989_ = l_Lake_parsePackageSpec(v_ws_939_, v___x_988_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_head_984_);
lean_dec(v_facet_941_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1046_; 
v_a_998_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1000_ = v___x_989_;
v_isShared_1001_ = v_isSharedCheck_1046_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_989_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1046_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v_str_1002_; lean_object* v_startInclusive_1003_; lean_object* v_endExclusive_1004_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v_str_1002_ = lean_ctor_get(v_head_984_, 0);
lean_inc_ref(v_str_1002_);
v_startInclusive_1003_ = lean_ctor_get(v_head_984_, 1);
lean_inc(v_startInclusive_1003_);
v_endExclusive_1004_ = lean_ctor_get(v_head_984_, 2);
lean_inc(v_endExclusive_1004_);
v___x_1009_ = lean_nat_sub(v_endExclusive_1004_, v_startInclusive_1003_);
v___x_1010_ = lean_nat_dec_eq(v___x_1009_, v___x_950_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1011_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_1012_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2, &l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2);
v___x_1013_ = lean_nat_dec_le(v___x_1012_, v___x_1009_);
lean_dec(v___x_1009_);
if (v___x_1013_ == 0)
{
lean_del_object(v___x_1000_);
lean_dec(v_head_984_);
goto v___jp_1005_;
}
else
{
uint8_t v___x_1014_; 
v___x_1014_ = lean_string_memcmp(v_str_1002_, v___x_1011_, v_startInclusive_1003_, v___x_950_, v___x_1012_);
if (v___x_1014_ == 0)
{
lean_del_object(v___x_1000_);
lean_dec(v_head_984_);
goto v___jp_1005_;
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = l_String_Slice_Pos_nextn(v_head_984_, v___x_950_, v___x_1015_);
lean_dec(v_head_984_);
v___x_1017_ = lean_nat_add(v_startInclusive_1003_, v___x_1016_);
lean_dec(v___x_1016_);
lean_dec(v_startInclusive_1003_);
v___x_1018_ = lean_string_utf8_extract_fast(v_str_1002_, v___x_1017_, v_endExclusive_1004_);
lean_dec(v_endExclusive_1004_);
lean_dec(v___x_1017_);
lean_dec_ref(v_str_1002_);
v___x_1019_ = l_String_toName(v___x_1018_);
lean_inc(v___x_1019_);
v___x_1020_ = l_Lake_Package_findTargetModule_x3f(v___x_1019_, v_a_998_);
if (lean_obj_tag(v___x_1020_) == 1)
{
lean_object* v_val_1021_; lean_object* v___x_1022_; 
lean_dec(v___x_1019_);
lean_del_object(v___x_1000_);
v_val_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_val_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_939_, v_val_1021_, v_facet_941_);
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
lean_dec(v_facet_941_);
v___x_1041_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1019_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set_tag(v___x_1000_, 0);
lean_ctor_set(v___x_1000_, 0, v___x_1041_);
v___x_1043_ = v___x_1000_;
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
else
{
lean_object* v___x_1045_; 
lean_dec(v___x_1009_);
lean_dec(v_endExclusive_1004_);
lean_dec(v_startInclusive_1003_);
lean_dec_ref(v_str_1002_);
lean_del_object(v___x_1000_);
lean_dec(v_head_984_);
v___x_1045_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_939_, v_a_998_, v_facet_941_);
return v___x_1045_;
}
v___jp_1005_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = lean_string_utf8_extract_fast(v_str_1002_, v_startInclusive_1003_, v_endExclusive_1004_);
lean_dec(v_endExclusive_1004_);
lean_dec(v_startInclusive_1003_);
lean_dec_ref(v_str_1002_);
v___x_1007_ = l_Lake_stringToLegalOrSimpleName(v___x_1006_);
v___x_1008_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_939_, v_a_998_, v___x_1007_, v_facet_941_);
return v___x_1008_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_957_, 2);
lean_dec_ref_known(v___x_956_, 2);
lean_dec(v_facet_941_);
goto v___jp_944_;
}
}
}
else
{
lean_dec(v___x_956_);
lean_dec(v_facet_941_);
goto v___jp_944_;
}
v___jp_944_:
{
if (v_isMaybePath_942_ == 0)
{
uint32_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = 47;
v___x_946_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_946_, 0, v_spec_940_);
lean_ctor_set_uint32(v___x_946_, sizeof(void*)*1, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_948_, 0, v_spec_940_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___boxed(lean_object* v_ws_1047_, lean_object* v_spec_1048_, lean_object* v_facet_1049_, lean_object* v_isMaybePath_1050_, lean_object* v_explicit_1051_){
_start:
{
uint8_t v_isMaybePath_boxed_1052_; uint8_t v_explicit_boxed_1053_; lean_object* v_res_1054_; 
v_isMaybePath_boxed_1052_ = lean_unbox(v_isMaybePath_1050_);
v_explicit_boxed_1053_ = lean_unbox(v_explicit_1051_);
v_res_1054_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1047_, v_spec_1048_, v_facet_1049_, v_isMaybePath_boxed_1052_, v_explicit_boxed_1053_);
lean_dec_ref(v_ws_1047_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(lean_object* v_spec_1055_, lean_object* v___x_1056_, lean_object* v___x_1057_, lean_object* v_inst_1058_, lean_object* v_R_1059_, lean_object* v_a_1060_, lean_object* v_b_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_1055_, v___x_1056_, v___x_1057_, v_a_1060_, v_b_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___boxed(lean_object* v_spec_1063_, lean_object* v___x_1064_, lean_object* v___x_1065_, lean_object* v_inst_1066_, lean_object* v_R_1067_, lean_object* v_a_1068_, lean_object* v_b_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(v_spec_1063_, v___x_1064_, v___x_1065_, v_inst_1066_, v_R_1067_, v_a_1068_, v_b_1069_);
lean_dec_ref(v___x_1064_);
return v_res_1070_;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1073_ = lean_string_utf8_byte_size(v___x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(lean_object* v_ws_1074_, lean_object* v_spec_1075_, lean_object* v_facet_1076_){
_start:
{
uint8_t v___y_1079_; uint8_t v___y_1080_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1195_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1196_ = lean_string_utf8_byte_size(v_spec_1075_);
v___x_1197_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1, &l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1);
v___x_1198_ = lean_nat_dec_le(v___x_1197_, v___x_1196_);
if (v___x_1198_ == 0)
{
goto v___jp_1159_;
}
else
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = lean_unsigned_to_nat(0u);
v___x_1200_ = lean_string_memcmp(v_spec_1075_, v___x_1195_, v___x_1199_, v___x_1199_, v___x_1197_);
if (v___x_1200_ == 0)
{
goto v___jp_1159_;
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; lean_object* v___x_1206_; 
v___x_1201_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_spec_1075_);
v___x_1202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1202_, 0, v_spec_1075_);
lean_ctor_set(v___x_1202_, 1, v___x_1199_);
lean_ctor_set(v___x_1202_, 2, v___x_1196_);
v___x_1203_ = l_String_Slice_Pos_nextn(v___x_1202_, v___x_1199_, v___x_1201_);
lean_dec_ref_known(v___x_1202_, 3);
v___x_1204_ = lean_string_utf8_extract_fast(v_spec_1075_, v___x_1203_, v___x_1196_);
lean_dec(v___x_1203_);
lean_dec_ref(v_spec_1075_);
v___x_1205_ = 0;
v___x_1206_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1074_, v___x_1204_, v_facet_1076_, v___x_1205_, v___x_1198_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set_tag(v___x_1209_, 1);
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_a_1215_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1206_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1206_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set_tag(v___x_1217_, 0);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
v___jp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
lean_inc_ref(v_spec_1075_);
v___x_1081_ = l_Lake_resolvePath(v_spec_1075_);
v___x_1082_ = lean_string_utf8_byte_size(v___x_1081_);
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_nat_dec_eq(v___x_1082_, v___x_1083_);
if (v___x_1084_ == 0)
{
uint8_t v___x_1085_; 
v___x_1085_ = l_System_FilePath_isDir(v___x_1081_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lake_Workspace_findModuleBySrc_x3f(v___x_1081_, v_ws_1074_);
if (lean_obj_tag(v___x_1086_) == 1)
{
lean_object* v_val_1087_; lean_object* v___x_1088_; 
lean_dec_ref(v_spec_1075_);
v_val_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_val_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_1074_, v_val_1087_, v_facet_1076_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 1);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1107_; 
v_a_1097_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1099_ = v___x_1088_;
v_isShared_1100_ = v_isSharedCheck_1107_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1088_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1107_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1101_ = lean_unsigned_to_nat(1u);
v___x_1102_ = lean_mk_empty_array_with_capacity(v___x_1101_);
v___x_1103_ = lean_array_push(v___x_1102_, v_a_1097_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set_tag(v___x_1099_, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1103_);
v___x_1105_ = v___x_1099_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v___x_1108_; 
lean_dec(v___x_1086_);
v___x_1108_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1074_, v_spec_1075_, v_facet_1076_, v___y_1079_, v___x_1085_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set_tag(v___x_1111_, 1);
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
v_a_1117_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1108_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1108_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set_tag(v___x_1119_, 0);
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
else
{
lean_object* v___x_1125_; 
lean_dec_ref(v___x_1081_);
v___x_1125_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1074_, v_spec_1075_, v_facet_1076_, v___y_1080_, v___y_1080_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 1);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
v_a_1134_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1125_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1125_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 0);
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
else
{
lean_object* v___x_1142_; 
lean_dec_ref(v___x_1081_);
v___x_1142_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1074_, v_spec_1075_, v_facet_1076_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 1);
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
v_a_1151_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1142_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1142_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set_tag(v___x_1153_, 0);
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
v___jp_1159_:
{
uint8_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1160_ = 1;
v___x_1161_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_1162_ = lean_string_utf8_byte_size(v_spec_1075_);
v___x_1163_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2, &l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2);
v___x_1164_ = lean_nat_dec_le(v___x_1163_, v___x_1162_);
if (v___x_1164_ == 0)
{
v___y_1079_ = v___x_1160_;
v___y_1080_ = v___x_1164_;
goto v___jp_1078_;
}
else
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = lean_string_memcmp(v_spec_1075_, v___x_1161_, v___x_1165_, v___x_1165_, v___x_1163_);
if (v___x_1166_ == 0)
{
v___y_1079_ = v___x_1160_;
v___y_1080_ = v___x_1166_;
goto v___jp_1078_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v_mod_1171_; lean_object* v___x_1172_; 
v___x_1167_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_spec_1075_);
v___x_1168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1168_, 0, v_spec_1075_);
lean_ctor_set(v___x_1168_, 1, v___x_1165_);
lean_ctor_set(v___x_1168_, 2, v___x_1162_);
v___x_1169_ = l_String_Slice_Pos_nextn(v___x_1168_, v___x_1165_, v___x_1167_);
lean_dec_ref_known(v___x_1168_, 3);
v___x_1170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1170_, 0, v_spec_1075_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
lean_ctor_set(v___x_1170_, 2, v___x_1162_);
v_mod_1171_ = l_String_Slice_toName(v___x_1170_);
lean_dec_ref_known(v___x_1170_, 3);
lean_inc(v_mod_1171_);
v___x_1172_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_1171_, v_ws_1074_);
if (lean_obj_tag(v___x_1172_) == 1)
{
lean_object* v_val_1173_; lean_object* v___x_1174_; 
lean_dec(v_mod_1171_);
v_val_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_val_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1174_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_1074_, v_val_1173_, v_facet_1076_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 1);
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1192_; 
v_a_1183_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1185_ = v___x_1174_;
v_isShared_1186_ = v_isSharedCheck_1192_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1174_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1192_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1187_ = lean_mk_empty_array_with_capacity(v___x_1167_);
v___x_1188_ = lean_array_push(v___x_1187_, v_a_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set_tag(v___x_1185_, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1188_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec(v___x_1172_);
lean_dec(v_facet_1076_);
v___x_1193_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_mod_1171_);
v___x_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___boxed(lean_object* v_ws_1223_, lean_object* v_spec_1224_, lean_object* v_facet_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1223_, v_spec_1224_, v_facet_1225_);
lean_dec_ref(v_ws_1223_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object* v_ws_1228_, lean_object* v_spec_1229_){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = lean_string_utf8_byte_size(v_spec_1229_);
lean_inc_ref_n(v_spec_1229_, 2);
v___x_1239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1239_, 0, v_spec_1229_);
lean_ctor_set(v___x_1239_, 1, v___x_1237_);
lean_ctor_set(v___x_1239_, 2, v___x_1238_);
v___x_1240_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v___x_1239_);
v___x_1241_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0));
v___x_1242_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_1229_, v___x_1239_, v___x_1238_, v___x_1240_, v___x_1241_);
lean_dec_ref_known(v___x_1239_, 3);
v___x_1243_ = lean_array_to_list(v___x_1242_);
if (lean_obj_tag(v___x_1243_) == 1)
{
lean_object* v_tail_1244_; 
v_tail_1244_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_tail_1244_);
if (lean_obj_tag(v_tail_1244_) == 0)
{
lean_object* v_head_1245_; lean_object* v_str_1246_; lean_object* v_startInclusive_1247_; lean_object* v_endExclusive_1248_; lean_object* v___x_1249_; lean_object* v_targetName_1250_; lean_object* v___x_1251_; 
v_head_1245_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_head_1245_);
lean_dec_ref_known(v___x_1243_, 2);
v_str_1246_ = lean_ctor_get(v_head_1245_, 0);
lean_inc_ref(v_str_1246_);
v_startInclusive_1247_ = lean_ctor_get(v_head_1245_, 1);
lean_inc(v_startInclusive_1247_);
v_endExclusive_1248_ = lean_ctor_get(v_head_1245_, 2);
lean_inc(v_endExclusive_1248_);
lean_dec(v_head_1245_);
v___x_1249_ = lean_string_utf8_extract_fast(v_str_1246_, v_startInclusive_1247_, v_endExclusive_1248_);
lean_dec(v_endExclusive_1248_);
lean_dec(v_startInclusive_1247_);
lean_dec_ref(v_str_1246_);
v_targetName_1250_ = l_Lake_stringToLegalOrSimpleName(v___x_1249_);
v___x_1251_ = l_Lake_Workspace_findLeanExe_x3f(v_targetName_1250_, v_ws_1228_);
lean_dec(v_targetName_1250_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_1252_, 0, v_spec_1229_);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
else
{
lean_object* v_val_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v_spec_1229_);
v_val_1254_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1251_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_val_1254_);
lean_dec(v___x_1251_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_val_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v_head_1262_; lean_object* v_head_1263_; lean_object* v_tail_1264_; lean_object* v_str_1266_; lean_object* v_startInclusive_1267_; lean_object* v_endExclusive_1268_; 
v_head_1262_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_head_1262_);
lean_dec_ref_known(v___x_1243_, 2);
v_head_1263_ = lean_ctor_get(v_tail_1244_, 0);
lean_inc(v_head_1263_);
v_tail_1264_ = lean_ctor_get(v_tail_1244_, 1);
lean_inc(v_tail_1264_);
lean_dec_ref_known(v_tail_1244_, 2);
if (lean_obj_tag(v_tail_1264_) == 0)
{
lean_object* v_str_1306_; lean_object* v_startInclusive_1307_; lean_object* v_endExclusive_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_str_1306_ = lean_ctor_get(v_head_1262_, 0);
lean_inc_ref(v_str_1306_);
v_startInclusive_1307_ = lean_ctor_get(v_head_1262_, 1);
lean_inc(v_startInclusive_1307_);
v_endExclusive_1308_ = lean_ctor_get(v_head_1262_, 2);
lean_inc(v_endExclusive_1308_);
v___x_1309_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1310_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1, &l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1);
v___x_1311_ = lean_nat_sub(v_endExclusive_1308_, v_startInclusive_1307_);
v___x_1312_ = lean_nat_dec_le(v___x_1310_, v___x_1311_);
lean_dec(v___x_1311_);
if (v___x_1312_ == 0)
{
lean_dec(v_head_1262_);
v_str_1266_ = v_str_1306_;
v_startInclusive_1267_ = v_startInclusive_1307_;
v_endExclusive_1268_ = v_endExclusive_1308_;
goto v___jp_1265_;
}
else
{
uint8_t v___x_1313_; 
v___x_1313_ = lean_string_memcmp(v_str_1306_, v___x_1309_, v_startInclusive_1307_, v___x_1237_, v___x_1310_);
if (v___x_1313_ == 0)
{
lean_dec(v_head_1262_);
v_str_1266_ = v_str_1306_;
v_startInclusive_1267_ = v_startInclusive_1307_;
v_endExclusive_1268_ = v_endExclusive_1308_;
goto v___jp_1265_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = lean_unsigned_to_nat(1u);
v___x_1315_ = l_String_Slice_Pos_nextn(v_head_1262_, v___x_1237_, v___x_1314_);
lean_dec(v_head_1262_);
v___x_1316_ = lean_nat_add(v_startInclusive_1307_, v___x_1315_);
lean_dec(v___x_1315_);
lean_dec(v_startInclusive_1307_);
v_str_1266_ = v_str_1306_;
v_startInclusive_1267_ = v___x_1316_;
v_endExclusive_1268_ = v_endExclusive_1308_;
goto v___jp_1265_;
}
}
}
else
{
lean_dec(v_tail_1264_);
lean_dec(v_head_1263_);
lean_dec(v_head_1262_);
goto v___jp_1233_;
}
v___jp_1265_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_string_utf8_extract_fast(v_str_1266_, v_startInclusive_1267_, v_endExclusive_1268_);
lean_dec(v_endExclusive_1268_);
lean_dec(v_startInclusive_1267_);
lean_dec_ref(v_str_1266_);
v___x_1270_ = l_Lake_parsePackageSpec(v_ws_1228_, v___x_1269_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec(v_head_1263_);
lean_dec_ref(v_spec_1229_);
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1305_; 
v_a_1279_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1281_ = v___x_1270_;
v_isShared_1282_ = v_isSharedCheck_1305_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1270_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1305_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_str_1283_; lean_object* v_startInclusive_1284_; lean_object* v_endExclusive_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1304_; 
v_str_1283_ = lean_ctor_get(v_head_1263_, 0);
v_startInclusive_1284_ = lean_ctor_get(v_head_1263_, 1);
v_endExclusive_1285_ = lean_ctor_get(v_head_1263_, 2);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_head_1263_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1287_ = v_head_1263_;
v_isShared_1288_ = v_isSharedCheck_1304_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_endExclusive_1285_);
lean_inc(v_startInclusive_1284_);
lean_inc(v_str_1283_);
lean_dec(v_head_1263_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1304_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_string_utf8_extract_fast(v_str_1283_, v_startInclusive_1284_, v_endExclusive_1285_);
lean_dec(v_endExclusive_1285_);
lean_dec(v_startInclusive_1284_);
lean_dec_ref(v_str_1283_);
v___x_1290_ = l_Lake_stringToLegalOrSimpleName(v___x_1289_);
v___x_1291_ = l_Lake_Package_findTargetDecl_x3f(v___x_1290_, v_a_1279_);
lean_dec(v___x_1290_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_del_object(v___x_1287_);
lean_del_object(v___x_1281_);
lean_dec(v_a_1279_);
goto v___jp_1230_;
}
else
{
lean_object* v_val_1292_; lean_object* v_name_1293_; lean_object* v_kind_1294_; lean_object* v_config_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v_val_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_val_1292_);
lean_dec_ref_known(v___x_1291_, 1);
v_name_1293_ = lean_ctor_get(v_val_1292_, 1);
lean_inc(v_name_1293_);
v_kind_1294_ = lean_ctor_get(v_val_1292_, 2);
lean_inc(v_kind_1294_);
v_config_1295_ = lean_ctor_get(v_val_1292_, 3);
lean_inc(v_config_1295_);
lean_dec(v_val_1292_);
v___x_1296_ = l_Lake_LeanExe_keyword;
v___x_1297_ = lean_name_eq(v_kind_1294_, v___x_1296_);
lean_dec(v_kind_1294_);
if (v___x_1297_ == 0)
{
lean_dec(v_config_1295_);
lean_dec(v_name_1293_);
lean_del_object(v___x_1287_);
lean_del_object(v___x_1281_);
lean_dec(v_a_1279_);
goto v___jp_1230_;
}
else
{
lean_object* v___x_1299_; 
lean_dec_ref(v_spec_1229_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 2, v_config_1295_);
lean_ctor_set(v___x_1287_, 1, v_name_1293_);
lean_ctor_set(v___x_1287_, 0, v_a_1279_);
v___x_1299_ = v___x_1287_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1279_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_name_1293_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_config_1295_);
v___x_1299_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1301_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1299_);
v___x_1301_ = v___x_1281_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
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
lean_dec(v___x_1243_);
goto v___jp_1233_;
}
v___jp_1230_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_spec_1229_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
v___jp_1233_:
{
uint32_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = 47;
v___x_1235_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_1235_, 0, v_spec_1229_);
lean_ctor_set_uint32(v___x_1235_, sizeof(void*)*1, v___x_1234_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed(lean_object* v_ws_1317_, lean_object* v_spec_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lake_parseExeTargetSpec(v_ws_1317_, v_spec_1318_);
lean_dec_ref(v_ws_1317_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(lean_object* v_s_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0));
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___boxed(lean_object* v_s_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(v_s_1322_);
lean_dec_ref(v_s_1322_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(lean_object* v_spec_1324_, lean_object* v___x_1325_, lean_object* v___x_1326_, lean_object* v_a_1327_, lean_object* v_b_1328_){
_start:
{
lean_object* v_it_1330_; lean_object* v_startInclusive_1331_; lean_object* v_endExclusive_1332_; 
if (lean_obj_tag(v_a_1327_) == 0)
{
lean_object* v_currPos_1337_; lean_object* v_searcher_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1361_; 
v_currPos_1337_ = lean_ctor_get(v_a_1327_, 0);
v_searcher_1338_ = lean_ctor_get(v_a_1327_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_a_1327_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1340_ = v_a_1327_;
v_isShared_1341_ = v_isSharedCheck_1361_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_searcher_1338_);
lean_inc(v_currPos_1337_);
lean_dec(v_a_1327_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1361_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
uint8_t v_decide_1342_; 
v_decide_1342_ = lean_nat_dec_eq(v_searcher_1338_, v___x_1326_);
if (v_decide_1342_ == 0)
{
uint32_t v___x_1343_; uint32_t v___x_1344_; uint8_t v___x_1345_; 
v___x_1343_ = 58;
v___x_1344_ = lean_string_utf8_get_fast(v_spec_1324_, v_searcher_1338_);
v___x_1345_ = lean_uint32_dec_eq(v___x_1344_, v___x_1343_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_string_utf8_next_fast(v_spec_1324_, v_searcher_1338_);
lean_dec(v_searcher_1338_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 1, v___x_1346_);
v___x_1348_ = v___x_1340_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_currPos_1337_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
v_a_1327_ = v___x_1348_;
goto _start;
}
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v_slice_1354_; lean_object* v_nextIt_1356_; 
v___x_1351_ = lean_string_utf8_next_fast(v_spec_1324_, v_searcher_1338_);
v___x_1352_ = lean_nat_sub(v___x_1351_, v_searcher_1338_);
v___x_1353_ = lean_nat_add(v_searcher_1338_, v___x_1352_);
lean_dec(v___x_1352_);
v_slice_1354_ = l_String_Slice_subslice_x21(v___x_1325_, v_currPos_1337_, v_searcher_1338_);
lean_inc(v___x_1353_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 1, v___x_1353_);
lean_ctor_set(v___x_1340_, 0, v___x_1353_);
v_nextIt_1356_ = v___x_1340_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1353_);
v_nextIt_1356_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v_startInclusive_1357_; lean_object* v_endExclusive_1358_; 
v_startInclusive_1357_ = lean_ctor_get(v_slice_1354_, 0);
lean_inc(v_startInclusive_1357_);
v_endExclusive_1358_ = lean_ctor_get(v_slice_1354_, 1);
lean_inc(v_endExclusive_1358_);
lean_dec_ref(v_slice_1354_);
v_it_1330_ = v_nextIt_1356_;
v_startInclusive_1331_ = v_startInclusive_1357_;
v_endExclusive_1332_ = v_endExclusive_1358_;
goto v___jp_1329_;
}
}
}
else
{
lean_object* v___x_1360_; 
lean_del_object(v___x_1340_);
lean_dec(v_searcher_1338_);
v___x_1360_ = lean_box(1);
lean_inc(v___x_1326_);
v_it_1330_ = v___x_1360_;
v_startInclusive_1331_ = v_currPos_1337_;
v_endExclusive_1332_ = v___x_1326_;
goto v___jp_1329_;
}
}
}
else
{
lean_dec(v___x_1326_);
lean_dec_ref(v_spec_1324_);
return v_b_1328_;
}
v___jp_1329_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_inc_ref(v_spec_1324_);
v___x_1333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1333_, 0, v_spec_1324_);
lean_ctor_set(v___x_1333_, 1, v_startInclusive_1331_);
lean_ctor_set(v___x_1333_, 2, v_endExclusive_1332_);
v___x_1334_ = l_String_Slice_toString(v___x_1333_);
lean_dec_ref_known(v___x_1333_, 3);
v___x_1335_ = lean_array_push(v_b_1328_, v___x_1334_);
v_a_1327_ = v_it_1330_;
v_b_1328_ = v___x_1335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg___boxed(lean_object* v_spec_1362_, lean_object* v___x_1363_, lean_object* v___x_1364_, lean_object* v_a_1365_, lean_object* v_b_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1362_, v___x_1363_, v___x_1364_, v_a_1365_, v_b_1366_);
lean_dec_ref(v___x_1363_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec(lean_object* v_ws_1370_, lean_object* v_spec_1371_){
_start:
{
uint32_t v___x_1373_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1373_ = 58;
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = lean_string_utf8_byte_size(v_spec_1371_);
lean_inc_ref_n(v_spec_1371_, 2);
v___x_1379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1379_, 0, v_spec_1371_);
lean_ctor_set(v___x_1379_, 1, v___x_1377_);
lean_ctor_set(v___x_1379_, 2, v___x_1378_);
v___x_1380_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(v___x_1379_);
v___x_1381_ = ((lean_object*)(l_Lake_parseTargetSpec___closed__0));
v___x_1382_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1371_, v___x_1379_, v___x_1378_, v___x_1380_, v___x_1381_);
lean_dec_ref_known(v___x_1379_, 3);
v___x_1383_ = lean_array_to_list(v___x_1382_);
if (lean_obj_tag(v___x_1383_) == 1)
{
lean_object* v_tail_1384_; 
v_tail_1384_ = lean_ctor_get(v___x_1383_, 1);
lean_inc(v_tail_1384_);
if (lean_obj_tag(v_tail_1384_) == 0)
{
lean_object* v_head_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec_ref(v_spec_1371_);
v_head_1385_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_head_1385_);
lean_dec_ref_known(v___x_1383_, 2);
v___x_1386_ = lean_box(0);
v___x_1387_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1370_, v_head_1385_, v___x_1386_);
return v___x_1387_;
}
else
{
lean_object* v_tail_1388_; 
v_tail_1388_ = lean_ctor_get(v_tail_1384_, 1);
if (lean_obj_tag(v_tail_1388_) == 0)
{
lean_object* v_head_1389_; lean_object* v_head_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec_ref(v_spec_1371_);
v_head_1389_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_head_1389_);
lean_dec_ref_known(v___x_1383_, 2);
v_head_1390_ = lean_ctor_get(v_tail_1384_, 0);
lean_inc(v_head_1390_);
lean_dec_ref_known(v_tail_1384_, 2);
v___x_1391_ = l_String_toName(v_head_1390_);
v___x_1392_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1370_, v_head_1389_, v___x_1391_);
return v___x_1392_;
}
else
{
lean_dec_ref_known(v_tail_1384_, 2);
lean_dec_ref_known(v___x_1383_, 2);
goto v___jp_1374_;
}
}
}
else
{
lean_dec(v___x_1383_);
goto v___jp_1374_;
}
v___jp_1374_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_1375_, 0, v_spec_1371_);
lean_ctor_set_uint32(v___x_1375_, sizeof(void*)*1, v___x_1373_);
v___x_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec___boxed(lean_object* v_ws_1393_, lean_object* v_spec_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lake_parseTargetSpec(v_ws_1393_, v_spec_1394_);
lean_dec_ref(v_ws_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(lean_object* v_spec_1397_, lean_object* v___x_1398_, lean_object* v___x_1399_, lean_object* v_inst_1400_, lean_object* v_R_1401_, lean_object* v_a_1402_, lean_object* v_b_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1397_, v___x_1398_, v___x_1399_, v_a_1402_, v_b_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___boxed(lean_object* v_spec_1405_, lean_object* v___x_1406_, lean_object* v___x_1407_, lean_object* v_inst_1408_, lean_object* v_R_1409_, lean_object* v_a_1410_, lean_object* v_b_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(v_spec_1405_, v___x_1406_, v___x_1407_, v_inst_1408_, v_R_1409_, v_a_1410_, v_b_1411_);
lean_dec_ref(v___x_1406_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(lean_object* v_ws_1413_, lean_object* v_as_x27_1414_, lean_object* v_b_1415_){
_start:
{
if (lean_obj_tag(v_as_x27_1414_) == 0)
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v_b_1415_);
return v___x_1417_;
}
else
{
lean_object* v_head_1418_; lean_object* v_tail_1419_; lean_object* v___x_1420_; 
v_head_1418_ = lean_ctor_get(v_as_x27_1414_, 0);
v_tail_1419_ = lean_ctor_get(v_as_x27_1414_, 1);
lean_inc(v_head_1418_);
v___x_1420_ = l_Lake_parseTargetSpec(v_ws_1413_, v_head_1418_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = l_Array_append___redArg(v_b_1415_, v_a_1421_);
lean_dec(v_a_1421_);
v_as_x27_1414_ = v_tail_1419_;
v_b_1415_ = v___x_1422_;
goto _start;
}
else
{
lean_dec_ref(v_b_1415_);
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg___boxed(lean_object* v_ws_1424_, lean_object* v_as_x27_1425_, lean_object* v_b_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1424_, v_as_x27_1425_, v_b_1426_);
lean_dec(v_as_x27_1425_);
lean_dec_ref(v_ws_1424_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs(lean_object* v_ws_1431_, lean_object* v_specs_1432_){
_start:
{
lean_object* v___x_1434_; lean_object* v_results_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v_results_1435_ = ((lean_object*)(l_Lake_parseTargetSpecs___closed__0));
v___x_1436_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1431_, v_specs_1432_, v_results_1435_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1437_);
v___x_1438_ = lean_array_get_size(v_a_1437_);
lean_dec(v_a_1437_);
v___x_1439_ = lean_nat_dec_eq(v___x_1438_, v___x_1434_);
if (v___x_1439_ == 0)
{
return v___x_1436_;
}
else
{
lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1454_; 
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v___x_1436_, 0);
lean_dec(v_unused_1455_);
v___x_1441_ = v___x_1436_;
v_isShared_1442_ = v_isSharedCheck_1454_;
goto v_resetjp_1440_;
}
else
{
lean_dec(v___x_1436_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1454_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v_packages_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_packages_1443_ = lean_ctor_get(v_ws_1431_, 4);
v___x_1444_ = lean_array_fget_borrowed(v_packages_1443_, v___x_1434_);
lean_inc(v___x_1444_);
v___x_1445_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_1431_, v___x_1444_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1448_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
if (v_isShared_1442_ == 0)
{
lean_ctor_set_tag(v___x_1441_, 1);
lean_ctor_set(v___x_1441_, 0, v_a_1446_);
v___x_1448_ = v___x_1441_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; 
v_a_1450_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1445_, 1);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v_a_1450_);
v___x_1452_ = v___x_1441_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
else
{
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___boxed(lean_object* v_ws_1456_, lean_object* v_specs_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lake_parseTargetSpecs(v_ws_1456_, v_specs_1457_);
lean_dec(v_specs_1457_);
lean_dec_ref(v_ws_1456_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(lean_object* v_ws_1460_, lean_object* v_as_1461_, lean_object* v_as_x27_1462_, lean_object* v_b_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1460_, v_as_x27_1462_, v_b_1463_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___boxed(lean_object* v_ws_1467_, lean_object* v_as_1468_, lean_object* v_as_x27_1469_, lean_object* v_b_1470_, lean_object* v_a_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(v_ws_1467_, v_as_1468_, v_as_x27_1469_, v_b_1470_, v_a_1471_);
lean_dec(v_as_x27_1469_);
lean_dec(v_as_1468_);
lean_dec_ref(v_ws_1467_);
return v_res_1473_;
}
}
lean_object* runtime_initialize_Lake_CLI_Error(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Build(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
