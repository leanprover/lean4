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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
v_registeredJobs_57_ = lean_ctor_get(v_a_38_, 3);
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
v_registeredJobs_202_ = lean_ctor_get(v_a_170_, 3);
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
uint8_t v___y_370__boxed_583_; lean_object* v_res_584_; 
v___y_370__boxed_583_ = lean_unbox(v___y_581_);
v_res_584_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(v___y_370__boxed_583_, v___y_582_);
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
lean_dec_ref(v___x_725_);
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
lean_dec_ref(v___x_728_);
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
lean_dec_ref(v___x_774_);
v_a_767_ = v_a_775_;
goto v___jp_766_;
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_777_; 
v_a_776_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v___x_774_);
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
v_defaultTargets_794_ = lean_ctor_get(v_pkg_793_, 16);
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
uint8_t v___x_800_; 
v___x_800_ = lean_nat_dec_le(v___x_797_, v___x_797_);
if (v___x_800_ == 0)
{
if (v___x_798_ == 0)
{
lean_object* v___x_801_; 
lean_dec_ref(v_defaultTargets_794_);
lean_dec_ref(v_pkg_793_);
v___x_801_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1));
return v___x_801_;
}
else
{
size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
v___x_802_ = ((size_t)0ULL);
v___x_803_ = lean_usize_of_nat(v___x_797_);
v___x_804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_792_, v_pkg_793_, v_defaultTargets_794_, v___x_802_, v___x_803_, v___x_796_);
lean_dec_ref(v_defaultTargets_794_);
return v___x_804_;
}
}
else
{
size_t v___x_805_; size_t v___x_806_; lean_object* v___x_807_; 
v___x_805_ = ((size_t)0ULL);
v___x_806_ = lean_usize_of_nat(v___x_797_);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_792_, v_pkg_793_, v_defaultTargets_794_, v___x_805_, v___x_806_, v___x_796_);
lean_dec_ref(v_defaultTargets_794_);
return v___x_807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___boxed(lean_object* v_ws_808_, lean_object* v_pkg_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_808_, v_pkg_809_);
lean_dec_ref(v_ws_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(lean_object* v_ws_812_, lean_object* v_pkg_813_, lean_object* v_facet_814_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = l_Lean_Name_isAnonymous(v_facet_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = l_Lake_Package_keyword;
lean_inc(v_facet_814_);
v___x_817_ = l_Lean_Name_append(v___x_816_, v_facet_814_);
v___x_818_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v___x_817_, v_ws_812_);
if (lean_obj_tag(v___x_818_) == 1)
{
lean_object* v_val_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_835_; 
lean_dec(v_facet_814_);
v_val_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_835_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_835_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_val_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_835_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_keyName_823_; uint8_t v_buildable_824_; lean_object* v_format_825_; lean_object* v___x_827_; 
v_keyName_823_ = lean_ctor_get(v_pkg_813_, 2);
v_buildable_824_ = lean_ctor_get_uint8(v_val_819_, sizeof(void*)*4);
v_format_825_ = lean_ctor_get(v_val_819_, 3);
lean_inc_ref(v_format_825_);
lean_dec(v_val_819_);
lean_inc(v_keyName_823_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v_keyName_823_);
v___x_827_ = v___x_821_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_keyName_823_);
v___x_827_ = v_reuseFailAlloc_834_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_828_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_816_);
lean_ctor_set(v___x_828_, 2, v_pkg_813_);
lean_ctor_set(v___x_828_, 3, v___x_817_);
v___x_829_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v_format_825_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*2, v_buildable_824_);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_mk_empty_array_with_capacity(v___x_830_);
v___x_832_ = lean_array_push(v___x_831_, v___x_829_);
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v___x_818_);
lean_dec(v___x_817_);
lean_dec_ref(v_pkg_813_);
v___x_836_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0));
v___x_837_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v_facet_814_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
else
{
lean_object* v___x_839_; 
lean_dec(v_facet_814_);
v___x_839_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_812_, v_pkg_813_);
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___boxed(lean_object* v_ws_840_, lean_object* v_pkg_841_, lean_object* v_facet_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_840_, v_pkg_841_, v_facet_842_);
lean_dec_ref(v_ws_840_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(lean_object* v_ws_844_, lean_object* v_target_845_, lean_object* v_facet_846_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lake_Workspace_findTargetDecl_x3f(v_target_845_, v_ws_844_);
if (lean_obj_tag(v___x_872_) == 1)
{
lean_object* v_val_873_; lean_object* v_fst_874_; lean_object* v_snd_875_; lean_object* v___x_876_; 
v_val_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_val_873_);
lean_dec_ref(v___x_872_);
v_fst_874_ = lean_ctor_get(v_val_873_, 0);
lean_inc(v_fst_874_);
v_snd_875_ = lean_ctor_get(v_val_873_, 1);
lean_inc(v_snd_875_);
lean_dec(v_val_873_);
v___x_876_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_844_, v_fst_874_, v_target_845_, v_snd_875_, v_facet_846_);
return v___x_876_;
}
else
{
lean_object* v_packages_877_; lean_object* v___x_878_; size_t v_sz_879_; size_t v___x_880_; lean_object* v___x_881_; lean_object* v_fst_882_; 
lean_dec(v___x_872_);
v_packages_877_ = lean_ctor_get(v_ws_844_, 4);
v___x_878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0));
v_sz_879_ = lean_array_size(v_packages_877_);
v___x_880_ = ((size_t)0ULL);
v___x_881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v_target_845_, v_packages_877_, v_sz_879_, v___x_880_, v___x_878_);
v_fst_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_fst_882_);
lean_dec_ref(v___x_881_);
if (lean_obj_tag(v_fst_882_) == 0)
{
goto v___jp_847_;
}
else
{
lean_object* v_val_883_; 
v_val_883_ = lean_ctor_get(v_fst_882_, 0);
lean_inc(v_val_883_);
lean_dec_ref(v_fst_882_);
if (lean_obj_tag(v_val_883_) == 1)
{
lean_object* v_val_884_; lean_object* v___x_885_; 
lean_dec(v_target_845_);
v_val_884_ = lean_ctor_get(v_val_883_, 0);
lean_inc(v_val_884_);
lean_dec_ref(v_val_883_);
v___x_885_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_844_, v_val_884_, v_facet_846_);
return v___x_885_;
}
else
{
lean_dec(v_val_883_);
goto v___jp_847_;
}
}
}
v___jp_847_:
{
lean_object* v___x_848_; 
lean_inc(v_target_845_);
v___x_848_ = l_Lake_Workspace_findTargetModule_x3f(v_target_845_, v_ws_844_);
if (lean_obj_tag(v___x_848_) == 1)
{
lean_object* v_val_849_; lean_object* v___x_850_; 
lean_dec(v_target_845_);
v_val_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_val_849_);
lean_dec_ref(v___x_848_);
v___x_850_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_844_, v_val_849_, v_facet_846_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_869_; 
v_a_859_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_869_ == 0)
{
v___x_861_ = v___x_850_;
v_isShared_862_ = v_isSharedCheck_869_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_850_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_869_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_863_ = lean_unsigned_to_nat(1u);
v___x_864_ = lean_mk_empty_array_with_capacity(v___x_863_);
v___x_865_ = lean_array_push(v___x_864_, v_a_859_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_865_);
v___x_867_ = v___x_861_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec(v___x_848_);
lean_dec(v_facet_846_);
v___x_870_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v___x_870_, 0, v_target_845_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace___boxed(lean_object* v_ws_886_, lean_object* v_target_887_, lean_object* v_facet_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(v_ws_886_, v_target_887_, v_facet_888_);
lean_dec_ref(v_ws_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(lean_object* v_s_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0));
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___boxed(lean_object* v_s_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v_s_894_);
lean_dec_ref(v_s_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(lean_object* v_spec_896_, lean_object* v___x_897_, lean_object* v___x_898_, lean_object* v_a_899_, lean_object* v_b_900_){
_start:
{
lean_object* v_it_902_; lean_object* v_startInclusive_903_; lean_object* v_endExclusive_904_; 
if (lean_obj_tag(v_a_899_) == 0)
{
lean_object* v_currPos_908_; lean_object* v_searcher_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_935_; 
v_currPos_908_ = lean_ctor_get(v_a_899_, 0);
v_searcher_909_ = lean_ctor_get(v_a_899_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v_a_899_);
if (v_isSharedCheck_935_ == 0)
{
v___x_911_ = v_a_899_;
v_isShared_912_ = v_isSharedCheck_935_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_searcher_909_);
lean_inc(v_currPos_908_);
lean_dec(v_a_899_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_935_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_startInclusive_913_; lean_object* v_endExclusive_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_startInclusive_913_ = lean_ctor_get(v___x_897_, 1);
v_endExclusive_914_ = lean_ctor_get(v___x_897_, 2);
v___x_915_ = lean_nat_sub(v_endExclusive_914_, v_startInclusive_913_);
v___x_916_ = lean_nat_dec_eq(v_searcher_909_, v___x_915_);
lean_dec(v___x_915_);
if (v___x_916_ == 0)
{
uint32_t v___x_917_; uint32_t v___x_918_; uint8_t v___x_919_; 
v___x_917_ = 47;
v___x_918_ = lean_string_utf8_get_fast(v_spec_896_, v_searcher_909_);
v___x_919_ = lean_uint32_dec_eq(v___x_918_, v___x_917_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = lean_string_utf8_next_fast(v_spec_896_, v_searcher_909_);
lean_dec(v_searcher_909_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 1, v___x_920_);
v___x_922_ = v___x_911_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_currPos_908_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v___x_920_);
v___x_922_ = v_reuseFailAlloc_924_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
v_a_899_ = v___x_922_;
goto _start;
}
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_slice_928_; lean_object* v_nextIt_930_; 
v___x_925_ = lean_string_utf8_next_fast(v_spec_896_, v_searcher_909_);
v___x_926_ = lean_nat_sub(v___x_925_, v_searcher_909_);
v___x_927_ = lean_nat_add(v_searcher_909_, v___x_926_);
lean_dec(v___x_926_);
v_slice_928_ = l_String_Slice_subslice_x21(v___x_897_, v_currPos_908_, v_searcher_909_);
lean_inc(v___x_927_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 1, v___x_927_);
lean_ctor_set(v___x_911_, 0, v___x_927_);
v_nextIt_930_ = v___x_911_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_927_);
v_nextIt_930_ = v_reuseFailAlloc_933_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v_startInclusive_931_; lean_object* v_endExclusive_932_; 
v_startInclusive_931_ = lean_ctor_get(v_slice_928_, 0);
lean_inc(v_startInclusive_931_);
v_endExclusive_932_ = lean_ctor_get(v_slice_928_, 1);
lean_inc(v_endExclusive_932_);
lean_dec_ref(v_slice_928_);
v_it_902_ = v_nextIt_930_;
v_startInclusive_903_ = v_startInclusive_931_;
v_endExclusive_904_ = v_endExclusive_932_;
goto v___jp_901_;
}
}
}
else
{
lean_object* v___x_934_; 
lean_del_object(v___x_911_);
lean_dec(v_searcher_909_);
v___x_934_ = lean_box(1);
lean_inc(v___x_898_);
v_it_902_ = v___x_934_;
v_startInclusive_903_ = v_currPos_908_;
v_endExclusive_904_ = v___x_898_;
goto v___jp_901_;
}
}
}
else
{
lean_dec(v___x_898_);
lean_dec_ref(v_spec_896_);
return v_b_900_;
}
v___jp_901_:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
lean_inc_ref(v_spec_896_);
v___x_905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_905_, 0, v_spec_896_);
lean_ctor_set(v___x_905_, 1, v_startInclusive_903_);
lean_ctor_set(v___x_905_, 2, v_endExclusive_904_);
v___x_906_ = lean_array_push(v_b_900_, v___x_905_);
v_a_899_ = v_it_902_;
v_b_900_ = v___x_906_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg___boxed(lean_object* v_spec_936_, lean_object* v___x_937_, lean_object* v___x_938_, lean_object* v_a_939_, lean_object* v_b_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_936_, v___x_937_, v___x_938_, v_a_939_, v_b_940_);
lean_dec_ref(v___x_937_);
return v_res_941_;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_946_ = lean_string_utf8_byte_size(v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(lean_object* v_ws_947_, lean_object* v_spec_948_, lean_object* v_facet_949_, uint8_t v_isMaybePath_950_, uint8_t v_explicit_951_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = lean_string_utf8_byte_size(v_spec_948_);
lean_inc_ref_n(v_spec_948_, 2);
v___x_960_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_960_, 0, v_spec_948_);
lean_ctor_set(v___x_960_, 1, v___x_958_);
lean_ctor_set(v___x_960_, 2, v___x_959_);
v___x_961_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v___x_960_);
v___x_962_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0));
v___x_963_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_948_, v___x_960_, v___x_959_, v___x_961_, v___x_962_);
lean_dec_ref(v___x_960_);
v___x_964_ = lean_array_to_list(v___x_963_);
if (lean_obj_tag(v___x_964_) == 1)
{
lean_object* v_tail_965_; 
v_tail_965_ = lean_ctor_get(v___x_964_, 1);
lean_inc(v_tail_965_);
if (lean_obj_tag(v_tail_965_) == 0)
{
lean_object* v_head_966_; lean_object* v_str_967_; lean_object* v_startInclusive_968_; lean_object* v_endExclusive_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
lean_dec_ref(v_spec_948_);
v_head_966_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_head_966_);
lean_dec_ref(v___x_964_);
v_str_967_ = lean_ctor_get(v_head_966_, 0);
lean_inc_ref(v_str_967_);
v_startInclusive_968_ = lean_ctor_get(v_head_966_, 1);
lean_inc(v_startInclusive_968_);
v_endExclusive_969_ = lean_ctor_get(v_head_966_, 2);
lean_inc(v_endExclusive_969_);
lean_dec(v_head_966_);
v___x_970_ = lean_nat_sub(v_endExclusive_969_, v_startInclusive_968_);
v___x_971_ = lean_nat_dec_eq(v___x_970_, v___x_958_);
lean_dec(v___x_970_);
if (v___x_971_ == 0)
{
if (v_explicit_951_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_string_utf8_extract(v_str_967_, v_startInclusive_968_, v_endExclusive_969_);
lean_dec(v_endExclusive_969_);
lean_dec(v_startInclusive_968_);
lean_dec_ref(v_str_967_);
v___x_973_ = l_Lake_stringToLegalOrSimpleName(v___x_972_);
v___x_974_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(v_ws_947_, v___x_973_, v_facet_949_);
return v___x_974_;
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_string_utf8_extract(v_str_967_, v_startInclusive_968_, v_endExclusive_969_);
lean_dec(v_endExclusive_969_);
lean_dec(v_startInclusive_968_);
lean_dec_ref(v_str_967_);
v___x_976_ = l_Lake_parsePackageSpec(v_ws_947_, v___x_975_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_facet_949_);
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_986_; 
v_a_985_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v___x_976_);
v___x_986_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_947_, v_a_985_, v_facet_949_);
return v___x_986_;
}
}
}
else
{
lean_object* v_packages_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec(v_endExclusive_969_);
lean_dec(v_startInclusive_968_);
lean_dec_ref(v_str_967_);
v_packages_987_ = lean_ctor_get(v_ws_947_, 4);
v___x_988_ = lean_array_fget_borrowed(v_packages_987_, v___x_958_);
lean_inc(v___x_988_);
v___x_989_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_947_, v___x_988_, v_facet_949_);
return v___x_989_;
}
}
else
{
lean_object* v_tail_990_; 
v_tail_990_ = lean_ctor_get(v_tail_965_, 1);
if (lean_obj_tag(v_tail_990_) == 0)
{
lean_object* v_head_991_; lean_object* v_head_992_; lean_object* v_str_993_; lean_object* v_startInclusive_994_; lean_object* v_endExclusive_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec_ref(v_spec_948_);
v_head_991_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_head_991_);
lean_dec_ref(v___x_964_);
v_head_992_ = lean_ctor_get(v_tail_965_, 0);
lean_inc(v_head_992_);
lean_dec_ref(v_tail_965_);
v_str_993_ = lean_ctor_get(v_head_991_, 0);
lean_inc_ref(v_str_993_);
v_startInclusive_994_ = lean_ctor_get(v_head_991_, 1);
lean_inc(v_startInclusive_994_);
v_endExclusive_995_ = lean_ctor_get(v_head_991_, 2);
lean_inc(v_endExclusive_995_);
lean_dec(v_head_991_);
v___x_996_ = lean_string_utf8_extract(v_str_993_, v_startInclusive_994_, v_endExclusive_995_);
lean_dec(v_endExclusive_995_);
lean_dec(v_startInclusive_994_);
lean_dec_ref(v_str_993_);
v___x_997_ = l_Lake_parsePackageSpec(v_ws_947_, v___x_996_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v_head_992_);
lean_dec(v_facet_949_);
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1055_; 
v_a_1006_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1008_ = v___x_997_;
v_isShared_1009_ = v_isSharedCheck_1055_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_997_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1055_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v_str_1010_; lean_object* v_startInclusive_1011_; lean_object* v_endExclusive_1012_; uint8_t v___y_1014_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v_str_1010_ = lean_ctor_get(v_head_992_, 0);
lean_inc_ref(v_str_1010_);
v_startInclusive_1011_ = lean_ctor_get(v_head_992_, 1);
lean_inc(v_startInclusive_1011_);
v_endExclusive_1012_ = lean_ctor_get(v_head_992_, 2);
lean_inc(v_endExclusive_1012_);
v___x_1048_ = lean_nat_sub(v_endExclusive_1012_, v_startInclusive_1011_);
v___x_1049_ = lean_nat_dec_eq(v___x_1048_, v___x_958_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1050_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_1051_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2, &l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2);
v___x_1052_ = lean_nat_dec_le(v___x_1051_, v___x_1048_);
lean_dec(v___x_1048_);
if (v___x_1052_ == 0)
{
v___y_1014_ = v___x_1049_;
goto v___jp_1013_;
}
else
{
uint8_t v___x_1053_; 
v___x_1053_ = lean_string_memcmp(v_str_1010_, v___x_1050_, v_startInclusive_1011_, v___x_958_, v___x_1051_);
v___y_1014_ = v___x_1053_;
goto v___jp_1013_;
}
}
else
{
lean_object* v___x_1054_; 
lean_dec(v___x_1048_);
lean_dec(v_endExclusive_1012_);
lean_dec(v_startInclusive_1011_);
lean_dec_ref(v_str_1010_);
lean_del_object(v___x_1008_);
lean_dec(v_head_992_);
v___x_1054_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_947_, v_a_1006_, v_facet_949_);
return v___x_1054_;
}
v___jp_1013_:
{
if (v___y_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_del_object(v___x_1008_);
lean_dec(v_head_992_);
v___x_1015_ = lean_string_utf8_extract(v_str_1010_, v_startInclusive_1011_, v_endExclusive_1012_);
lean_dec(v_endExclusive_1012_);
lean_dec(v_startInclusive_1011_);
lean_dec_ref(v_str_1010_);
v___x_1016_ = l_Lake_stringToLegalOrSimpleName(v___x_1015_);
v___x_1017_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_947_, v_a_1006_, v___x_1016_, v_facet_949_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1018_ = lean_unsigned_to_nat(1u);
v___x_1019_ = l_String_Slice_Pos_nextn(v_head_992_, v___x_958_, v___x_1018_);
lean_dec(v_head_992_);
v___x_1020_ = lean_nat_add(v_startInclusive_1011_, v___x_1019_);
lean_dec(v___x_1019_);
lean_dec(v_startInclusive_1011_);
v___x_1021_ = lean_string_utf8_extract(v_str_1010_, v___x_1020_, v_endExclusive_1012_);
lean_dec(v_endExclusive_1012_);
lean_dec(v___x_1020_);
lean_dec_ref(v_str_1010_);
v___x_1022_ = l_String_toName(v___x_1021_);
lean_inc(v___x_1022_);
v___x_1023_ = l_Lake_Package_findTargetModule_x3f(v___x_1022_, v_a_1006_);
if (lean_obj_tag(v___x_1023_) == 1)
{
lean_object* v_val_1024_; lean_object* v___x_1025_; 
lean_dec(v___x_1022_);
lean_del_object(v___x_1008_);
v_val_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_val_1024_);
lean_dec_ref(v___x_1023_);
v___x_1025_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_947_, v_val_1024_, v_facet_949_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1043_; 
v_a_1034_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1036_ = v___x_1025_;
v_isShared_1037_ = v_isSharedCheck_1043_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1025_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1043_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1038_ = lean_mk_empty_array_with_capacity(v___x_1018_);
v___x_1039_ = lean_array_push(v___x_1038_, v_a_1034_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1039_);
v___x_1041_ = v___x_1036_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
lean_dec(v___x_1023_);
lean_dec(v_facet_949_);
v___x_1044_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1022_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set_tag(v___x_1008_, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1044_);
v___x_1046_ = v___x_1008_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_tail_965_);
lean_dec_ref(v___x_964_);
lean_dec(v_facet_949_);
goto v___jp_952_;
}
}
}
else
{
lean_dec(v___x_964_);
lean_dec(v_facet_949_);
goto v___jp_952_;
}
v___jp_952_:
{
if (v_isMaybePath_950_ == 0)
{
uint32_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = 47;
v___x_954_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_954_, 0, v_spec_948_);
lean_ctor_set_uint32(v___x_954_, sizeof(void*)*1, v___x_953_);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_956_, 0, v_spec_948_);
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___boxed(lean_object* v_ws_1056_, lean_object* v_spec_1057_, lean_object* v_facet_1058_, lean_object* v_isMaybePath_1059_, lean_object* v_explicit_1060_){
_start:
{
uint8_t v_isMaybePath_boxed_1061_; uint8_t v_explicit_boxed_1062_; lean_object* v_res_1063_; 
v_isMaybePath_boxed_1061_ = lean_unbox(v_isMaybePath_1059_);
v_explicit_boxed_1062_ = lean_unbox(v_explicit_1060_);
v_res_1063_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1056_, v_spec_1057_, v_facet_1058_, v_isMaybePath_boxed_1061_, v_explicit_boxed_1062_);
lean_dec_ref(v_ws_1056_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(lean_object* v_spec_1064_, lean_object* v___x_1065_, lean_object* v___x_1066_, lean_object* v_inst_1067_, lean_object* v_R_1068_, lean_object* v_a_1069_, lean_object* v_b_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_1064_, v___x_1065_, v___x_1066_, v_a_1069_, v_b_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___boxed(lean_object* v_spec_1072_, lean_object* v___x_1073_, lean_object* v___x_1074_, lean_object* v_inst_1075_, lean_object* v_R_1076_, lean_object* v_a_1077_, lean_object* v_b_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(v_spec_1072_, v___x_1073_, v___x_1074_, v_inst_1075_, v_R_1076_, v_a_1077_, v_b_1078_);
lean_dec_ref(v___x_1073_);
return v_res_1079_;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1082_ = lean_string_utf8_byte_size(v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(lean_object* v_ws_1083_, lean_object* v_spec_1084_, lean_object* v_facet_1085_){
_start:
{
uint8_t v___y_1088_; uint8_t v___y_1089_; uint8_t v___y_1169_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1205_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1206_ = lean_string_utf8_byte_size(v_spec_1084_);
v___x_1207_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1, &l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1);
v___x_1208_ = lean_nat_dec_le(v___x_1207_, v___x_1206_);
if (v___x_1208_ == 0)
{
v___y_1169_ = v___x_1208_;
goto v___jp_1168_;
}
else
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = lean_string_memcmp(v_spec_1084_, v___x_1205_, v___x_1209_, v___x_1209_, v___x_1207_);
if (v___x_1210_ == 0)
{
v___y_1169_ = v___x_1210_;
goto v___jp_1168_;
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; lean_object* v___x_1216_; 
v___x_1211_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_spec_1084_);
v___x_1212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1212_, 0, v_spec_1084_);
lean_ctor_set(v___x_1212_, 1, v___x_1209_);
lean_ctor_set(v___x_1212_, 2, v___x_1206_);
v___x_1213_ = l_String_Slice_Pos_nextn(v___x_1212_, v___x_1209_, v___x_1211_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = lean_string_utf8_extract(v_spec_1084_, v___x_1213_, v___x_1206_);
lean_dec(v___x_1213_);
lean_dec_ref(v_spec_1084_);
v___x_1215_ = 0;
v___x_1216_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1083_, v___x_1214_, v_facet_1085_, v___x_1215_, v___x_1210_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set_tag(v___x_1219_, 1);
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
v_a_1225_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1216_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1216_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set_tag(v___x_1227_, 0);
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
v___jp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
lean_inc_ref(v_spec_1084_);
v___x_1090_ = l_Lake_resolvePath(v_spec_1084_);
v___x_1091_ = lean_string_utf8_byte_size(v___x_1090_);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_nat_dec_eq(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
uint8_t v___x_1094_; 
v___x_1094_ = l_System_FilePath_isDir(v___x_1090_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lake_Workspace_findModuleBySrc_x3f(v___x_1090_, v_ws_1083_);
if (lean_obj_tag(v___x_1095_) == 1)
{
lean_object* v_val_1096_; lean_object* v___x_1097_; 
lean_dec_ref(v_spec_1084_);
v_val_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_val_1096_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_1083_, v_val_1096_, v_facet_1085_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set_tag(v___x_1100_, 1);
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1116_; 
v_a_1106_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1108_ = v___x_1097_;
v_isShared_1109_ = v_isSharedCheck_1116_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1097_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1116_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1110_ = lean_unsigned_to_nat(1u);
v___x_1111_ = lean_mk_empty_array_with_capacity(v___x_1110_);
v___x_1112_ = lean_array_push(v___x_1111_, v_a_1106_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set_tag(v___x_1108_, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1112_);
v___x_1114_ = v___x_1108_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_object* v___x_1117_; 
lean_dec(v___x_1095_);
v___x_1117_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1083_, v_spec_1084_, v_facet_1085_, v___y_1088_, v___x_1094_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 1);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
v_a_1126_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1117_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1117_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 0);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
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
}
}
else
{
lean_object* v___x_1134_; 
lean_dec_ref(v___x_1090_);
v___x_1134_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1083_, v_spec_1084_, v_facet_1085_, v___y_1089_, v___y_1089_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 1);
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
v_a_1143_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1134_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1134_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 0);
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
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
}
}
else
{
lean_object* v___x_1151_; 
lean_dec_ref(v___x_1090_);
v___x_1151_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1083_, v_spec_1084_, v_facet_1085_, v___y_1088_, v___y_1089_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 1);
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
v_a_1160_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1151_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1151_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set_tag(v___x_1162_, 0);
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
v___jp_1168_:
{
uint8_t v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1170_ = 1;
v___x_1171_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_1172_ = lean_string_utf8_byte_size(v_spec_1084_);
v___x_1173_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2, &l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2);
v___x_1174_ = lean_nat_dec_le(v___x_1173_, v___x_1172_);
if (v___x_1174_ == 0)
{
v___y_1088_ = v___x_1170_;
v___y_1089_ = v___y_1169_;
goto v___jp_1087_;
}
else
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = lean_string_memcmp(v_spec_1084_, v___x_1171_, v___x_1175_, v___x_1175_, v___x_1173_);
if (v___x_1176_ == 0)
{
v___y_1088_ = v___x_1170_;
v___y_1089_ = v___x_1176_;
goto v___jp_1087_;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v_mod_1181_; lean_object* v___x_1182_; 
v___x_1177_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_spec_1084_);
v___x_1178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1178_, 0, v_spec_1084_);
lean_ctor_set(v___x_1178_, 1, v___x_1175_);
lean_ctor_set(v___x_1178_, 2, v___x_1172_);
v___x_1179_ = l_String_Slice_Pos_nextn(v___x_1178_, v___x_1175_, v___x_1177_);
lean_dec_ref(v___x_1178_);
v___x_1180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1180_, 0, v_spec_1084_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
lean_ctor_set(v___x_1180_, 2, v___x_1172_);
v_mod_1181_ = l_String_Slice_toName(v___x_1180_);
lean_dec_ref(v___x_1180_);
lean_inc(v_mod_1181_);
v___x_1182_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_1181_, v_ws_1083_);
if (lean_obj_tag(v___x_1182_) == 1)
{
lean_object* v_val_1183_; lean_object* v___x_1184_; 
lean_dec(v_mod_1181_);
v_val_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_val_1183_);
lean_dec_ref(v___x_1182_);
v___x_1184_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_1083_, v_val_1183_, v_facet_1085_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set_tag(v___x_1187_, 1);
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1202_; 
v_a_1193_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1195_ = v___x_1184_;
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1184_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1197_ = lean_mk_empty_array_with_capacity(v___x_1177_);
v___x_1198_ = lean_array_push(v___x_1197_, v_a_1193_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set_tag(v___x_1195_, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1198_);
v___x_1200_ = v___x_1195_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec(v___x_1182_);
lean_dec(v_facet_1085_);
v___x_1203_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1203_, 0, v_mod_1181_);
v___x_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___boxed(lean_object* v_ws_1233_, lean_object* v_spec_1234_, lean_object* v_facet_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1233_, v_spec_1234_, v_facet_1235_);
lean_dec_ref(v_ws_1233_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object* v_ws_1238_, lean_object* v_spec_1239_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = lean_string_utf8_byte_size(v_spec_1239_);
lean_inc_ref_n(v_spec_1239_, 2);
v___x_1249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1249_, 0, v_spec_1239_);
lean_ctor_set(v___x_1249_, 1, v___x_1247_);
lean_ctor_set(v___x_1249_, 2, v___x_1248_);
v___x_1250_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v___x_1249_);
v___x_1251_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0));
v___x_1252_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_1239_, v___x_1249_, v___x_1248_, v___x_1250_, v___x_1251_);
lean_dec_ref(v___x_1249_);
v___x_1253_ = lean_array_to_list(v___x_1252_);
if (lean_obj_tag(v___x_1253_) == 1)
{
lean_object* v_tail_1254_; 
v_tail_1254_ = lean_ctor_get(v___x_1253_, 1);
lean_inc(v_tail_1254_);
if (lean_obj_tag(v_tail_1254_) == 0)
{
lean_object* v_head_1255_; lean_object* v_str_1256_; lean_object* v_startInclusive_1257_; lean_object* v_endExclusive_1258_; lean_object* v___x_1259_; lean_object* v_targetName_1260_; lean_object* v___x_1261_; 
v_head_1255_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_head_1255_);
lean_dec_ref(v___x_1253_);
v_str_1256_ = lean_ctor_get(v_head_1255_, 0);
lean_inc_ref(v_str_1256_);
v_startInclusive_1257_ = lean_ctor_get(v_head_1255_, 1);
lean_inc(v_startInclusive_1257_);
v_endExclusive_1258_ = lean_ctor_get(v_head_1255_, 2);
lean_inc(v_endExclusive_1258_);
lean_dec(v_head_1255_);
v___x_1259_ = lean_string_utf8_extract(v_str_1256_, v_startInclusive_1257_, v_endExclusive_1258_);
lean_dec(v_endExclusive_1258_);
lean_dec(v_startInclusive_1257_);
lean_dec_ref(v_str_1256_);
v_targetName_1260_ = l_Lake_stringToLegalOrSimpleName(v___x_1259_);
v___x_1261_ = l_Lake_Workspace_findLeanExe_x3f(v_targetName_1260_, v_ws_1238_);
lean_dec(v_targetName_1260_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_spec_1239_);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
else
{
lean_object* v_val_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v_spec_1239_);
v_val_1264_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1261_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_val_1264_);
lean_dec(v___x_1261_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_val_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_object* v_head_1272_; lean_object* v_head_1273_; lean_object* v_tail_1274_; lean_object* v_str_1276_; lean_object* v_startInclusive_1277_; lean_object* v_endExclusive_1278_; 
v_head_1272_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_head_1272_);
lean_dec_ref(v___x_1253_);
v_head_1273_ = lean_ctor_get(v_tail_1254_, 0);
lean_inc(v_head_1273_);
v_tail_1274_ = lean_ctor_get(v_tail_1254_, 1);
lean_inc(v_tail_1274_);
lean_dec_ref(v_tail_1254_);
if (lean_obj_tag(v_tail_1274_) == 0)
{
lean_object* v_str_1316_; lean_object* v_startInclusive_1317_; lean_object* v_endExclusive_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v_str_1316_ = lean_ctor_get(v_head_1272_, 0);
lean_inc_ref(v_str_1316_);
v_startInclusive_1317_ = lean_ctor_get(v_head_1272_, 1);
lean_inc(v_startInclusive_1317_);
v_endExclusive_1318_ = lean_ctor_get(v_head_1272_, 2);
lean_inc(v_endExclusive_1318_);
v___x_1319_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1320_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1, &l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1);
v___x_1321_ = lean_nat_sub(v_endExclusive_1318_, v_startInclusive_1317_);
v___x_1322_ = lean_nat_dec_le(v___x_1320_, v___x_1321_);
lean_dec(v___x_1321_);
if (v___x_1322_ == 0)
{
lean_dec(v_head_1272_);
v_str_1276_ = v_str_1316_;
v_startInclusive_1277_ = v_startInclusive_1317_;
v_endExclusive_1278_ = v_endExclusive_1318_;
goto v___jp_1275_;
}
else
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_string_memcmp(v_str_1316_, v___x_1319_, v_startInclusive_1317_, v___x_1247_, v___x_1320_);
if (v___x_1323_ == 0)
{
lean_dec(v_head_1272_);
v_str_1276_ = v_str_1316_;
v_startInclusive_1277_ = v_startInclusive_1317_;
v_endExclusive_1278_ = v_endExclusive_1318_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = lean_unsigned_to_nat(1u);
v___x_1325_ = l_String_Slice_Pos_nextn(v_head_1272_, v___x_1247_, v___x_1324_);
lean_dec(v_head_1272_);
v___x_1326_ = lean_nat_add(v_startInclusive_1317_, v___x_1325_);
lean_dec(v___x_1325_);
lean_dec(v_startInclusive_1317_);
v_str_1276_ = v_str_1316_;
v_startInclusive_1277_ = v___x_1326_;
v_endExclusive_1278_ = v_endExclusive_1318_;
goto v___jp_1275_;
}
}
}
else
{
lean_dec(v_tail_1274_);
lean_dec(v_head_1273_);
lean_dec(v_head_1272_);
goto v___jp_1243_;
}
v___jp_1275_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_string_utf8_extract(v_str_1276_, v_startInclusive_1277_, v_endExclusive_1278_);
lean_dec(v_endExclusive_1278_);
lean_dec(v_startInclusive_1277_);
lean_dec_ref(v_str_1276_);
v___x_1280_ = l_Lake_parsePackageSpec(v_ws_1238_, v___x_1279_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v_head_1273_);
lean_dec_ref(v_spec_1239_);
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1315_; 
v_a_1289_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1291_ = v___x_1280_;
v_isShared_1292_ = v_isSharedCheck_1315_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1280_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1315_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_str_1293_; lean_object* v_startInclusive_1294_; lean_object* v_endExclusive_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1314_; 
v_str_1293_ = lean_ctor_get(v_head_1273_, 0);
v_startInclusive_1294_ = lean_ctor_get(v_head_1273_, 1);
v_endExclusive_1295_ = lean_ctor_get(v_head_1273_, 2);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_head_1273_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1297_ = v_head_1273_;
v_isShared_1298_ = v_isSharedCheck_1314_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_endExclusive_1295_);
lean_inc(v_startInclusive_1294_);
lean_inc(v_str_1293_);
lean_dec(v_head_1273_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1314_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_string_utf8_extract(v_str_1293_, v_startInclusive_1294_, v_endExclusive_1295_);
lean_dec(v_endExclusive_1295_);
lean_dec(v_startInclusive_1294_);
lean_dec_ref(v_str_1293_);
v___x_1300_ = l_Lake_stringToLegalOrSimpleName(v___x_1299_);
v___x_1301_ = l_Lake_Package_findTargetDecl_x3f(v___x_1300_, v_a_1289_);
lean_dec(v___x_1300_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_del_object(v___x_1297_);
lean_del_object(v___x_1291_);
lean_dec(v_a_1289_);
goto v___jp_1240_;
}
else
{
lean_object* v_val_1302_; lean_object* v_name_1303_; lean_object* v_kind_1304_; lean_object* v_config_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_val_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_val_1302_);
lean_dec_ref(v___x_1301_);
v_name_1303_ = lean_ctor_get(v_val_1302_, 1);
lean_inc(v_name_1303_);
v_kind_1304_ = lean_ctor_get(v_val_1302_, 2);
lean_inc(v_kind_1304_);
v_config_1305_ = lean_ctor_get(v_val_1302_, 3);
lean_inc(v_config_1305_);
lean_dec(v_val_1302_);
v___x_1306_ = l_Lake_LeanExe_keyword;
v___x_1307_ = lean_name_eq(v_kind_1304_, v___x_1306_);
lean_dec(v_kind_1304_);
if (v___x_1307_ == 0)
{
lean_dec(v_config_1305_);
lean_dec(v_name_1303_);
lean_del_object(v___x_1297_);
lean_del_object(v___x_1291_);
lean_dec(v_a_1289_);
goto v___jp_1240_;
}
else
{
lean_object* v___x_1309_; 
lean_dec_ref(v_spec_1239_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 2, v_config_1305_);
lean_ctor_set(v___x_1297_, 1, v_name_1303_);
lean_ctor_set(v___x_1297_, 0, v_a_1289_);
v___x_1309_ = v___x_1297_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1289_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_name_1303_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_config_1305_);
v___x_1309_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1311_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1309_);
v___x_1311_ = v___x_1291_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
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
lean_dec(v___x_1253_);
goto v___jp_1243_;
}
v___jp_1240_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_spec_1239_);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
v___jp_1243_:
{
uint32_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = 47;
v___x_1245_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_1245_, 0, v_spec_1239_);
lean_ctor_set_uint32(v___x_1245_, sizeof(void*)*1, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed(lean_object* v_ws_1327_, lean_object* v_spec_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lake_parseExeTargetSpec(v_ws_1327_, v_spec_1328_);
lean_dec_ref(v_ws_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(lean_object* v_s_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0));
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___boxed(lean_object* v_s_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(v_s_1332_);
lean_dec_ref(v_s_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(lean_object* v_spec_1334_, lean_object* v___x_1335_, lean_object* v___x_1336_, lean_object* v_a_1337_, lean_object* v_b_1338_){
_start:
{
lean_object* v_it_1340_; lean_object* v_startInclusive_1341_; lean_object* v_endExclusive_1342_; 
if (lean_obj_tag(v_a_1337_) == 0)
{
lean_object* v_currPos_1347_; lean_object* v_searcher_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1374_; 
v_currPos_1347_ = lean_ctor_get(v_a_1337_, 0);
v_searcher_1348_ = lean_ctor_get(v_a_1337_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_a_1337_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1350_ = v_a_1337_;
v_isShared_1351_ = v_isSharedCheck_1374_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_searcher_1348_);
lean_inc(v_currPos_1347_);
lean_dec(v_a_1337_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1374_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v_startInclusive_1352_; lean_object* v_endExclusive_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v_startInclusive_1352_ = lean_ctor_get(v___x_1335_, 1);
v_endExclusive_1353_ = lean_ctor_get(v___x_1335_, 2);
v___x_1354_ = lean_nat_sub(v_endExclusive_1353_, v_startInclusive_1352_);
v___x_1355_ = lean_nat_dec_eq(v_searcher_1348_, v___x_1354_);
lean_dec(v___x_1354_);
if (v___x_1355_ == 0)
{
uint32_t v___x_1356_; uint32_t v___x_1357_; uint8_t v___x_1358_; 
v___x_1356_ = 58;
v___x_1357_ = lean_string_utf8_get_fast(v_spec_1334_, v_searcher_1348_);
v___x_1358_ = lean_uint32_dec_eq(v___x_1357_, v___x_1356_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1359_ = lean_string_utf8_next_fast(v_spec_1334_, v_searcher_1348_);
lean_dec(v_searcher_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1359_);
v___x_1361_ = v___x_1350_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_currPos_1347_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
v_a_1337_ = v___x_1361_;
goto _start;
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v_slice_1367_; lean_object* v_nextIt_1369_; 
v___x_1364_ = lean_string_utf8_next_fast(v_spec_1334_, v_searcher_1348_);
v___x_1365_ = lean_nat_sub(v___x_1364_, v_searcher_1348_);
v___x_1366_ = lean_nat_add(v_searcher_1348_, v___x_1365_);
lean_dec(v___x_1365_);
v_slice_1367_ = l_String_Slice_subslice_x21(v___x_1335_, v_currPos_1347_, v_searcher_1348_);
lean_inc(v___x_1366_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1366_);
lean_ctor_set(v___x_1350_, 0, v___x_1366_);
v_nextIt_1369_ = v___x_1350_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v___x_1366_);
v_nextIt_1369_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v_startInclusive_1370_; lean_object* v_endExclusive_1371_; 
v_startInclusive_1370_ = lean_ctor_get(v_slice_1367_, 0);
lean_inc(v_startInclusive_1370_);
v_endExclusive_1371_ = lean_ctor_get(v_slice_1367_, 1);
lean_inc(v_endExclusive_1371_);
lean_dec_ref(v_slice_1367_);
v_it_1340_ = v_nextIt_1369_;
v_startInclusive_1341_ = v_startInclusive_1370_;
v_endExclusive_1342_ = v_endExclusive_1371_;
goto v___jp_1339_;
}
}
}
else
{
lean_object* v___x_1373_; 
lean_del_object(v___x_1350_);
lean_dec(v_searcher_1348_);
v___x_1373_ = lean_box(1);
lean_inc(v___x_1336_);
v_it_1340_ = v___x_1373_;
v_startInclusive_1341_ = v_currPos_1347_;
v_endExclusive_1342_ = v___x_1336_;
goto v___jp_1339_;
}
}
}
else
{
lean_dec(v___x_1336_);
lean_dec_ref(v_spec_1334_);
return v_b_1338_;
}
v___jp_1339_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_inc_ref(v_spec_1334_);
v___x_1343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1343_, 0, v_spec_1334_);
lean_ctor_set(v___x_1343_, 1, v_startInclusive_1341_);
lean_ctor_set(v___x_1343_, 2, v_endExclusive_1342_);
v___x_1344_ = l_String_Slice_toString(v___x_1343_);
lean_dec_ref(v___x_1343_);
v___x_1345_ = lean_array_push(v_b_1338_, v___x_1344_);
v_a_1337_ = v_it_1340_;
v_b_1338_ = v___x_1345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg___boxed(lean_object* v_spec_1375_, lean_object* v___x_1376_, lean_object* v___x_1377_, lean_object* v_a_1378_, lean_object* v_b_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1375_, v___x_1376_, v___x_1377_, v_a_1378_, v_b_1379_);
lean_dec_ref(v___x_1376_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec(lean_object* v_ws_1383_, lean_object* v_spec_1384_){
_start:
{
uint32_t v___x_1386_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1386_ = 58;
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = lean_string_utf8_byte_size(v_spec_1384_);
lean_inc_ref_n(v_spec_1384_, 2);
v___x_1392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1392_, 0, v_spec_1384_);
lean_ctor_set(v___x_1392_, 1, v___x_1390_);
lean_ctor_set(v___x_1392_, 2, v___x_1391_);
v___x_1393_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(v___x_1392_);
v___x_1394_ = ((lean_object*)(l_Lake_parseTargetSpec___closed__0));
v___x_1395_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1384_, v___x_1392_, v___x_1391_, v___x_1393_, v___x_1394_);
lean_dec_ref(v___x_1392_);
v___x_1396_ = lean_array_to_list(v___x_1395_);
if (lean_obj_tag(v___x_1396_) == 1)
{
lean_object* v_tail_1397_; 
v_tail_1397_ = lean_ctor_get(v___x_1396_, 1);
lean_inc(v_tail_1397_);
if (lean_obj_tag(v_tail_1397_) == 0)
{
lean_object* v_head_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec_ref(v_spec_1384_);
v_head_1398_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_head_1398_);
lean_dec_ref(v___x_1396_);
v___x_1399_ = lean_box(0);
v___x_1400_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1383_, v_head_1398_, v___x_1399_);
return v___x_1400_;
}
else
{
lean_object* v_tail_1401_; 
v_tail_1401_ = lean_ctor_get(v_tail_1397_, 1);
if (lean_obj_tag(v_tail_1401_) == 0)
{
lean_object* v_head_1402_; lean_object* v_head_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec_ref(v_spec_1384_);
v_head_1402_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_head_1402_);
lean_dec_ref(v___x_1396_);
v_head_1403_ = lean_ctor_get(v_tail_1397_, 0);
lean_inc(v_head_1403_);
lean_dec_ref(v_tail_1397_);
v___x_1404_ = l_String_toName(v_head_1403_);
v___x_1405_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1383_, v_head_1402_, v___x_1404_);
return v___x_1405_;
}
else
{
lean_dec_ref(v_tail_1397_);
lean_dec_ref(v___x_1396_);
goto v___jp_1387_;
}
}
}
else
{
lean_dec(v___x_1396_);
goto v___jp_1387_;
}
v___jp_1387_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_1388_, 0, v_spec_1384_);
lean_ctor_set_uint32(v___x_1388_, sizeof(void*)*1, v___x_1386_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec___boxed(lean_object* v_ws_1406_, lean_object* v_spec_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lake_parseTargetSpec(v_ws_1406_, v_spec_1407_);
lean_dec_ref(v_ws_1406_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(lean_object* v_spec_1410_, lean_object* v___x_1411_, lean_object* v___x_1412_, lean_object* v_inst_1413_, lean_object* v_R_1414_, lean_object* v_a_1415_, lean_object* v_b_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1410_, v___x_1411_, v___x_1412_, v_a_1415_, v_b_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___boxed(lean_object* v_spec_1418_, lean_object* v___x_1419_, lean_object* v___x_1420_, lean_object* v_inst_1421_, lean_object* v_R_1422_, lean_object* v_a_1423_, lean_object* v_b_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(v_spec_1418_, v___x_1419_, v___x_1420_, v_inst_1421_, v_R_1422_, v_a_1423_, v_b_1424_);
lean_dec_ref(v___x_1419_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(lean_object* v_ws_1426_, lean_object* v_as_x27_1427_, lean_object* v_b_1428_){
_start:
{
if (lean_obj_tag(v_as_x27_1427_) == 0)
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_b_1428_);
return v___x_1430_;
}
else
{
lean_object* v_head_1431_; lean_object* v_tail_1432_; lean_object* v___x_1433_; 
v_head_1431_ = lean_ctor_get(v_as_x27_1427_, 0);
v_tail_1432_ = lean_ctor_get(v_as_x27_1427_, 1);
lean_inc(v_head_1431_);
v___x_1433_ = l_Lake_parseTargetSpec(v_ws_1426_, v_head_1431_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref(v___x_1433_);
v___x_1435_ = l_Array_append___redArg(v_b_1428_, v_a_1434_);
lean_dec(v_a_1434_);
v_as_x27_1427_ = v_tail_1432_;
v_b_1428_ = v___x_1435_;
goto _start;
}
else
{
lean_dec_ref(v_b_1428_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg___boxed(lean_object* v_ws_1437_, lean_object* v_as_x27_1438_, lean_object* v_b_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1437_, v_as_x27_1438_, v_b_1439_);
lean_dec(v_as_x27_1438_);
lean_dec_ref(v_ws_1437_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs(lean_object* v_ws_1444_, lean_object* v_specs_1445_){
_start:
{
lean_object* v___x_1447_; lean_object* v_results_1448_; lean_object* v___x_1449_; 
v___x_1447_ = lean_unsigned_to_nat(0u);
v_results_1448_ = ((lean_object*)(l_Lake_parseTargetSpecs___closed__0));
v___x_1449_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1444_, v_specs_1445_, v_results_1448_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
v___x_1451_ = lean_array_get_size(v_a_1450_);
lean_dec(v_a_1450_);
v___x_1452_ = lean_nat_dec_eq(v___x_1451_, v___x_1447_);
if (v___x_1452_ == 0)
{
return v___x_1449_;
}
else
{
lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1467_; 
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v___x_1449_, 0);
lean_dec(v_unused_1468_);
v___x_1454_ = v___x_1449_;
v_isShared_1455_ = v_isSharedCheck_1467_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v___x_1449_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1467_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v_packages_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v_packages_1456_ = lean_ctor_get(v_ws_1444_, 4);
v___x_1457_ = lean_array_fget_borrowed(v_packages_1456_, v___x_1447_);
lean_inc(v___x_1457_);
v___x_1458_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_1444_, v___x_1457_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref(v___x_1458_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set_tag(v___x_1454_, 1);
lean_ctor_set(v___x_1454_, 0, v_a_1459_);
v___x_1461_ = v___x_1454_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; 
v_a_1463_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v___x_1458_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v_a_1463_);
v___x_1465_ = v___x_1454_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
else
{
return v___x_1449_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___boxed(lean_object* v_ws_1469_, lean_object* v_specs_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lake_parseTargetSpecs(v_ws_1469_, v_specs_1470_);
lean_dec(v_specs_1470_);
lean_dec_ref(v_ws_1469_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(lean_object* v_ws_1473_, lean_object* v_as_1474_, lean_object* v_as_x27_1475_, lean_object* v_b_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1473_, v_as_x27_1475_, v_b_1476_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___boxed(lean_object* v_ws_1480_, lean_object* v_as_1481_, lean_object* v_as_x27_1482_, lean_object* v_b_1483_, lean_object* v_a_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(v_ws_1480_, v_as_1481_, v_as_x27_1482_, v_b_1483_, v_a_1484_);
lean_dec(v_as_x27_1482_);
lean_dec(v_as_1481_);
lean_dec_ref(v_ws_1480_);
return v_res_1486_;
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
