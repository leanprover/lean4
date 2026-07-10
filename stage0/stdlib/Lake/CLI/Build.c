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
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = l_Lean_Name_isAnonymous(v_facet_631_);
v___x_634_ = lean_bool_not(v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v_format_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_645_; 
lean_dec(v_facet_631_);
v_format_635_ = lean_ctor_get(v_config_632_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_config_632_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v_config_632_, 0);
lean_dec(v_unused_646_);
v___x_637_ = v_config_632_;
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_format_635_);
lean_dec(v_config_632_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
uint8_t v___x_639_; lean_object* v___x_641_; 
v___x_639_ = 1;
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_name_630_);
lean_ctor_set(v___x_637_, 0, v_pkg_629_);
v___x_641_ = v___x_637_;
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
lean_ctor_set(v___x_642_, 1, v_format_635_);
lean_ctor_set_uint8(v___x_642_, sizeof(void*)*2, v___x_639_);
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec_ref(v_config_632_);
lean_dec_ref(v_pkg_629_);
v___x_647_ = lean_alloc_ctor(20, 2, 0);
lean_ctor_set(v___x_647_, 0, v_name_630_);
lean_ctor_set(v___x_647_, 1, v_facet_631_);
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(lean_object* v_ws_652_, lean_object* v_pkg_653_, lean_object* v_target_654_, lean_object* v_decl_655_, lean_object* v_facet_656_){
_start:
{
lean_object* v_name_657_; lean_object* v_kind_658_; lean_object* v_config_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_715_; 
v_name_657_ = lean_ctor_get(v_decl_655_, 1);
v_kind_658_ = lean_ctor_get(v_decl_655_, 2);
v_config_659_ = lean_ctor_get(v_decl_655_, 3);
v_isSharedCheck_715_ = !lean_is_exclusive(v_decl_655_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v_decl_655_, 0);
lean_dec(v_unused_716_);
v___x_661_ = v_decl_655_;
v_isShared_662_ = v_isSharedCheck_715_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_config_659_);
lean_inc(v_kind_658_);
lean_inc(v_name_657_);
lean_dec(v_decl_655_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_715_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
uint8_t v___x_663_; 
v___x_663_ = l_Lean_Name_isAnonymous(v_kind_658_);
if (v___x_663_ == 0)
{
uint8_t v___x_664_; lean_object* v___y_666_; uint8_t v___x_693_; 
lean_dec(v_target_654_);
v___x_664_ = 1;
v___x_693_ = l_Lean_Name_isAnonymous(v_facet_656_);
if (v___x_693_ == 0)
{
v___y_666_ = v_facet_656_;
goto v___jp_665_;
}
else
{
lean_object* v___x_694_; 
lean_dec(v_facet_656_);
v___x_694_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1));
v___y_666_ = v___x_694_;
goto v___jp_665_;
}
v___jp_665_:
{
lean_object* v_facetConfigs_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_facetConfigs_667_ = lean_ctor_get(v_ws_652_, 6);
lean_inc(v___y_666_);
lean_inc(v_kind_658_);
v___x_668_ = l_Lean_Name_append(v_kind_658_, v___y_666_);
v___x_669_ = l_Lake_FacetConfigMap_get_x3f(v___x_668_, v_facetConfigs_667_);
if (lean_obj_tag(v___x_669_) == 1)
{
lean_object* v_val_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_689_; 
lean_dec(v___y_666_);
v_val_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_689_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_689_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_val_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_689_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_keyName_674_; uint8_t v_buildable_675_; lean_object* v_format_676_; lean_object* v_tgt_677_; lean_object* v___x_678_; lean_object* v_info_680_; 
v_keyName_674_ = lean_ctor_get(v_pkg_653_, 2);
lean_inc(v_keyName_674_);
v_buildable_675_ = lean_ctor_get_uint8(v_val_670_, sizeof(void*)*4);
v_format_676_ = lean_ctor_get(v_val_670_, 3);
lean_inc_ref(v_format_676_);
lean_dec(v_val_670_);
lean_inc(v_name_657_);
v_tgt_677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_tgt_677_, 0, v_pkg_653_);
lean_ctor_set(v_tgt_677_, 1, v_name_657_);
lean_ctor_set(v_tgt_677_, 2, v_config_659_);
v___x_678_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_678_, 0, v_keyName_674_);
lean_ctor_set(v___x_678_, 1, v_name_657_);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 1);
lean_ctor_set(v___x_661_, 3, v___x_668_);
lean_ctor_set(v___x_661_, 2, v_tgt_677_);
lean_ctor_set(v___x_661_, 1, v_kind_658_);
lean_ctor_set(v___x_661_, 0, v___x_678_);
v_info_680_ = v___x_661_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_kind_658_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_tgt_677_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v___x_668_);
v_info_680_ = v_reuseFailAlloc_688_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_681_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_681_, 0, v_info_680_);
lean_ctor_set(v___x_681_, 1, v_format_676_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*2, v_buildable_675_);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_mk_empty_array_with_capacity(v___x_682_);
v___x_684_ = lean_array_push(v___x_683_, v___x_681_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_684_);
v___x_686_ = v___x_672_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v___x_669_);
lean_dec(v___x_668_);
lean_del_object(v___x_661_);
lean_dec(v_config_659_);
lean_dec(v_name_657_);
lean_dec_ref(v_pkg_653_);
v___x_690_ = l_Lean_Name_toString(v_kind_658_, v___x_664_);
v___x_691_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___y_666_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
}
else
{
lean_object* v___x_695_; 
lean_del_object(v___x_661_);
lean_dec(v_kind_658_);
lean_dec(v_name_657_);
v___x_695_ = l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(v_pkg_653_, v_target_654_, v_facet_656_, v_config_659_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_714_; 
v_a_704_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_714_ == 0)
{
v___x_706_ = v___x_695_;
v_isShared_707_ = v_isSharedCheck_714_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_695_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_714_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_mk_empty_array_with_capacity(v___x_708_);
v___x_710_ = lean_array_push(v___x_709_, v_a_704_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_710_);
v___x_712_ = v___x_706_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___boxed(lean_object* v_ws_717_, lean_object* v_pkg_718_, lean_object* v_target_719_, lean_object* v_decl_720_, lean_object* v_facet_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_717_, v_pkg_718_, v_target_719_, v_decl_720_, v_facet_721_);
lean_dec_ref(v_ws_717_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(lean_object* v_ws_723_, lean_object* v_pkg_724_, lean_object* v_target_725_, lean_object* v_facet_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lake_Package_findTargetDecl_x3f(v_target_725_, v_pkg_724_);
if (lean_obj_tag(v___x_727_) == 1)
{
lean_object* v_val_728_; lean_object* v___x_729_; 
v_val_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v___x_727_, 1);
v___x_729_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_723_, v_pkg_724_, v_target_725_, v_val_728_, v_facet_726_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; 
lean_dec(v___x_727_);
lean_inc_ref(v_pkg_724_);
lean_inc(v_target_725_);
v___x_730_ = l_Lake_Package_findTargetModule_x3f(v_target_725_, v_pkg_724_);
if (lean_obj_tag(v___x_730_) == 1)
{
lean_object* v_val_731_; lean_object* v___x_732_; 
lean_dec(v_target_725_);
lean_dec_ref(v_pkg_724_);
v_val_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_val_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_723_, v_val_731_, v_facet_726_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_751_; 
v_a_741_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_751_ == 0)
{
v___x_743_ = v___x_732_;
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_732_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_mk_empty_array_with_capacity(v___x_745_);
v___x_747_ = lean_array_push(v___x_746_, v_a_741_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_747_);
v___x_749_ = v___x_743_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v_baseName_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec(v___x_730_);
lean_dec(v_facet_726_);
v_baseName_752_ = lean_ctor_get(v_pkg_724_, 1);
lean_inc(v_baseName_752_);
lean_dec_ref(v_pkg_724_);
v___x_753_ = 0;
v___x_754_ = l_Lean_Name_toString(v_target_725_, v___x_753_);
v___x_755_ = lean_alloc_ctor(17, 2, 0);
lean_ctor_set(v___x_755_, 0, v_baseName_752_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage___boxed(lean_object* v_ws_757_, lean_object* v_pkg_758_, lean_object* v_target_759_, lean_object* v_facet_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_757_, v_pkg_758_, v_target_759_, v_facet_760_);
lean_dec_ref(v_ws_757_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(lean_object* v_ws_762_, lean_object* v_pkg_763_, lean_object* v_as_764_, size_t v_i_765_, size_t v_stop_766_, lean_object* v_b_767_){
_start:
{
lean_object* v_a_769_; uint8_t v___x_773_; 
v___x_773_ = lean_usize_dec_eq(v_i_765_, v_stop_766_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_array_uget_borrowed(v_as_764_, v_i_765_);
v___x_775_ = lean_box(0);
lean_inc(v___x_774_);
lean_inc_ref(v_pkg_763_);
v___x_776_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_762_, v_pkg_763_, v___x_774_, v___x_775_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_dec_ref(v_b_767_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_dec_ref(v_pkg_763_);
return v___x_776_;
}
else
{
lean_object* v_a_777_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_776_, 1);
v_a_769_ = v_a_777_;
goto v___jp_768_;
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_779_; 
v_a_778_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_776_, 1);
v___x_779_ = l_Array_append___redArg(v_b_767_, v_a_778_);
lean_dec(v_a_778_);
v_a_769_ = v___x_779_;
goto v___jp_768_;
}
}
else
{
lean_object* v___x_780_; 
lean_dec_ref(v_pkg_763_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v_b_767_);
return v___x_780_;
}
v___jp_768_:
{
size_t v___x_770_; size_t v___x_771_; 
v___x_770_ = ((size_t)1ULL);
v___x_771_ = lean_usize_add(v_i_765_, v___x_770_);
v_i_765_ = v___x_771_;
v_b_767_ = v_a_769_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0___boxed(lean_object* v_ws_781_, lean_object* v_pkg_782_, lean_object* v_as_783_, lean_object* v_i_784_, lean_object* v_stop_785_, lean_object* v_b_786_){
_start:
{
size_t v_i_boxed_787_; size_t v_stop_boxed_788_; lean_object* v_res_789_; 
v_i_boxed_787_ = lean_unbox_usize(v_i_784_);
lean_dec(v_i_784_);
v_stop_boxed_788_ = lean_unbox_usize(v_stop_785_);
lean_dec(v_stop_785_);
v_res_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_781_, v_pkg_782_, v_as_783_, v_i_boxed_787_, v_stop_boxed_788_, v_b_786_);
lean_dec_ref(v_as_783_);
lean_dec_ref(v_ws_781_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(lean_object* v_ws_794_, lean_object* v_pkg_795_){
_start:
{
lean_object* v_defaultTargets_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_defaultTargets_796_ = lean_ctor_get(v_pkg_795_, 17);
lean_inc_ref(v_defaultTargets_796_);
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0));
v___x_799_ = lean_array_get_size(v_defaultTargets_796_);
v___x_800_ = lean_nat_dec_lt(v___x_797_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
lean_dec_ref(v_defaultTargets_796_);
lean_dec_ref(v_pkg_795_);
v___x_801_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1));
return v___x_801_;
}
else
{
uint8_t v___x_802_; 
v___x_802_ = lean_nat_dec_le(v___x_799_, v___x_799_);
if (v___x_802_ == 0)
{
if (v___x_800_ == 0)
{
lean_object* v___x_803_; 
lean_dec_ref(v_defaultTargets_796_);
lean_dec_ref(v_pkg_795_);
v___x_803_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1));
return v___x_803_;
}
else
{
size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_804_ = ((size_t)0ULL);
v___x_805_ = lean_usize_of_nat(v___x_799_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_794_, v_pkg_795_, v_defaultTargets_796_, v___x_804_, v___x_805_, v___x_798_);
lean_dec_ref(v_defaultTargets_796_);
return v___x_806_;
}
}
else
{
size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_807_ = ((size_t)0ULL);
v___x_808_ = lean_usize_of_nat(v___x_799_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_794_, v_pkg_795_, v_defaultTargets_796_, v___x_807_, v___x_808_, v___x_798_);
lean_dec_ref(v_defaultTargets_796_);
return v___x_809_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___boxed(lean_object* v_ws_810_, lean_object* v_pkg_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_810_, v_pkg_811_);
lean_dec_ref(v_ws_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(lean_object* v_ws_814_, lean_object* v_pkg_815_, lean_object* v_facet_816_){
_start:
{
uint8_t v___x_817_; 
v___x_817_ = l_Lean_Name_isAnonymous(v_facet_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = l_Lake_Package_keyword;
lean_inc(v_facet_816_);
v___x_819_ = l_Lean_Name_append(v___x_818_, v_facet_816_);
v___x_820_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v___x_819_, v_ws_814_);
if (lean_obj_tag(v___x_820_) == 1)
{
lean_object* v_val_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_837_; 
lean_dec(v_facet_816_);
v_val_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_837_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_837_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_val_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_837_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_keyName_825_; uint8_t v_buildable_826_; lean_object* v_format_827_; lean_object* v___x_829_; 
v_keyName_825_ = lean_ctor_get(v_pkg_815_, 2);
v_buildable_826_ = lean_ctor_get_uint8(v_val_821_, sizeof(void*)*4);
v_format_827_ = lean_ctor_get(v_val_821_, 3);
lean_inc_ref(v_format_827_);
lean_dec(v_val_821_);
lean_inc(v_keyName_825_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v_keyName_825_);
v___x_829_ = v___x_823_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_keyName_825_);
v___x_829_ = v_reuseFailAlloc_836_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_830_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v___x_818_);
lean_ctor_set(v___x_830_, 2, v_pkg_815_);
lean_ctor_set(v___x_830_, 3, v___x_819_);
v___x_831_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v_format_827_);
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*2, v_buildable_826_);
v___x_832_ = lean_unsigned_to_nat(1u);
v___x_833_ = lean_mk_empty_array_with_capacity(v___x_832_);
v___x_834_ = lean_array_push(v___x_833_, v___x_831_);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec(v___x_820_);
lean_dec(v___x_819_);
lean_dec_ref(v_pkg_815_);
v___x_838_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0));
v___x_839_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v_facet_816_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
else
{
lean_object* v___x_841_; 
lean_dec(v_facet_816_);
v___x_841_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_814_, v_pkg_815_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___boxed(lean_object* v_ws_842_, lean_object* v_pkg_843_, lean_object* v_facet_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_842_, v_pkg_843_, v_facet_844_);
lean_dec_ref(v_ws_842_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(lean_object* v_ws_846_, lean_object* v_target_847_, lean_object* v_facet_848_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lake_Workspace_findTargetDecl_x3f(v_target_847_, v_ws_846_);
if (lean_obj_tag(v___x_874_) == 1)
{
lean_object* v_val_875_; lean_object* v_fst_876_; lean_object* v_snd_877_; lean_object* v___x_878_; 
v_val_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_val_875_);
lean_dec_ref_known(v___x_874_, 1);
v_fst_876_ = lean_ctor_get(v_val_875_, 0);
lean_inc(v_fst_876_);
v_snd_877_ = lean_ctor_get(v_val_875_, 1);
lean_inc(v_snd_877_);
lean_dec(v_val_875_);
v___x_878_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_846_, v_fst_876_, v_target_847_, v_snd_877_, v_facet_848_);
return v___x_878_;
}
else
{
lean_object* v_packages_879_; lean_object* v___x_880_; size_t v_sz_881_; size_t v___x_882_; lean_object* v___x_883_; lean_object* v_fst_884_; 
lean_dec(v___x_874_);
v_packages_879_ = lean_ctor_get(v_ws_846_, 4);
v___x_880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0));
v_sz_881_ = lean_array_size(v_packages_879_);
v___x_882_ = ((size_t)0ULL);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v_target_847_, v_packages_879_, v_sz_881_, v___x_882_, v___x_880_);
v_fst_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_fst_884_);
lean_dec_ref(v___x_883_);
if (lean_obj_tag(v_fst_884_) == 0)
{
goto v___jp_849_;
}
else
{
lean_object* v_val_885_; 
v_val_885_ = lean_ctor_get(v_fst_884_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v_fst_884_, 1);
if (lean_obj_tag(v_val_885_) == 1)
{
lean_object* v_val_886_; lean_object* v___x_887_; 
lean_dec(v_target_847_);
v_val_886_ = lean_ctor_get(v_val_885_, 0);
lean_inc(v_val_886_);
lean_dec_ref_known(v_val_885_, 1);
v___x_887_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_846_, v_val_886_, v_facet_848_);
return v___x_887_;
}
else
{
lean_dec(v_val_885_);
goto v___jp_849_;
}
}
}
v___jp_849_:
{
lean_object* v___x_850_; 
lean_inc(v_target_847_);
v___x_850_ = l_Lake_Workspace_findTargetModule_x3f(v_target_847_, v_ws_846_);
if (lean_obj_tag(v___x_850_) == 1)
{
lean_object* v_val_851_; lean_object* v___x_852_; 
lean_dec(v_target_847_);
v_val_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_val_851_);
lean_dec_ref_known(v___x_850_, 1);
v___x_852_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_846_, v_val_851_, v_facet_848_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_871_; 
v_a_861_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_871_ == 0)
{
v___x_863_ = v___x_852_;
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_852_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = lean_mk_empty_array_with_capacity(v___x_865_);
v___x_867_ = lean_array_push(v___x_866_, v_a_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_867_);
v___x_869_ = v___x_863_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec(v___x_850_);
lean_dec(v_facet_848_);
v___x_872_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v___x_872_, 0, v_target_847_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace___boxed(lean_object* v_ws_888_, lean_object* v_target_889_, lean_object* v_facet_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(v_ws_888_, v_target_889_, v_facet_890_);
lean_dec_ref(v_ws_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(lean_object* v_s_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0));
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___boxed(lean_object* v_s_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v_s_896_);
lean_dec_ref(v_s_896_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(lean_object* v_spec_898_, lean_object* v___x_899_, lean_object* v___x_900_, lean_object* v_a_901_, lean_object* v_b_902_){
_start:
{
lean_object* v_it_904_; lean_object* v_startInclusive_905_; lean_object* v_endExclusive_906_; 
if (lean_obj_tag(v_a_901_) == 0)
{
lean_object* v_currPos_910_; lean_object* v_searcher_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_937_; 
v_currPos_910_ = lean_ctor_get(v_a_901_, 0);
v_searcher_911_ = lean_ctor_get(v_a_901_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_a_901_);
if (v_isSharedCheck_937_ == 0)
{
v___x_913_ = v_a_901_;
v_isShared_914_ = v_isSharedCheck_937_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_searcher_911_);
lean_inc(v_currPos_910_);
lean_dec(v_a_901_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_937_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_startInclusive_915_; lean_object* v_endExclusive_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_startInclusive_915_ = lean_ctor_get(v___x_899_, 1);
v_endExclusive_916_ = lean_ctor_get(v___x_899_, 2);
v___x_917_ = lean_nat_sub(v_endExclusive_916_, v_startInclusive_915_);
v___x_918_ = lean_nat_dec_eq(v_searcher_911_, v___x_917_);
lean_dec(v___x_917_);
if (v___x_918_ == 0)
{
uint32_t v___x_919_; uint32_t v___x_920_; uint8_t v___x_921_; 
v___x_919_ = 47;
v___x_920_ = lean_string_utf8_get_fast(v_spec_898_, v_searcher_911_);
v___x_921_ = lean_uint32_dec_eq(v___x_920_, v___x_919_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_922_ = lean_string_utf8_next_fast(v_spec_898_, v_searcher_911_);
lean_dec(v_searcher_911_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 1, v___x_922_);
v___x_924_ = v___x_913_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_currPos_910_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v___x_922_);
v___x_924_ = v_reuseFailAlloc_926_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
v_a_901_ = v___x_924_;
goto _start;
}
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_slice_930_; lean_object* v_nextIt_932_; 
v___x_927_ = lean_string_utf8_next_fast(v_spec_898_, v_searcher_911_);
v___x_928_ = lean_nat_sub(v___x_927_, v_searcher_911_);
v___x_929_ = lean_nat_add(v_searcher_911_, v___x_928_);
lean_dec(v___x_928_);
v_slice_930_ = l_String_Slice_subslice_x21(v___x_899_, v_currPos_910_, v_searcher_911_);
lean_inc(v___x_929_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 1, v___x_929_);
lean_ctor_set(v___x_913_, 0, v___x_929_);
v_nextIt_932_ = v___x_913_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v___x_929_);
v_nextIt_932_ = v_reuseFailAlloc_935_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v_startInclusive_933_; lean_object* v_endExclusive_934_; 
v_startInclusive_933_ = lean_ctor_get(v_slice_930_, 0);
lean_inc(v_startInclusive_933_);
v_endExclusive_934_ = lean_ctor_get(v_slice_930_, 1);
lean_inc(v_endExclusive_934_);
lean_dec_ref(v_slice_930_);
v_it_904_ = v_nextIt_932_;
v_startInclusive_905_ = v_startInclusive_933_;
v_endExclusive_906_ = v_endExclusive_934_;
goto v___jp_903_;
}
}
}
else
{
lean_object* v___x_936_; 
lean_del_object(v___x_913_);
lean_dec(v_searcher_911_);
v___x_936_ = lean_box(1);
lean_inc(v___x_900_);
v_it_904_ = v___x_936_;
v_startInclusive_905_ = v_currPos_910_;
v_endExclusive_906_ = v___x_900_;
goto v___jp_903_;
}
}
}
else
{
lean_dec(v___x_900_);
lean_dec_ref(v_spec_898_);
return v_b_902_;
}
v___jp_903_:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
lean_inc_ref(v_spec_898_);
v___x_907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_907_, 0, v_spec_898_);
lean_ctor_set(v___x_907_, 1, v_startInclusive_905_);
lean_ctor_set(v___x_907_, 2, v_endExclusive_906_);
v___x_908_ = lean_array_push(v_b_902_, v___x_907_);
v_a_901_ = v_it_904_;
v_b_902_ = v___x_908_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg___boxed(lean_object* v_spec_938_, lean_object* v___x_939_, lean_object* v___x_940_, lean_object* v_a_941_, lean_object* v_b_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_938_, v___x_939_, v___x_940_, v_a_941_, v_b_942_);
lean_dec_ref(v___x_939_);
return v_res_943_;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_948_ = lean_string_utf8_byte_size(v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(lean_object* v_ws_949_, lean_object* v_spec_950_, lean_object* v_facet_951_, uint8_t v_isMaybePath_952_, uint8_t v_explicit_953_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = lean_string_utf8_byte_size(v_spec_950_);
lean_inc_ref_n(v_spec_950_, 2);
v___x_962_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_962_, 0, v_spec_950_);
lean_ctor_set(v___x_962_, 1, v___x_960_);
lean_ctor_set(v___x_962_, 2, v___x_961_);
v___x_963_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v___x_962_);
v___x_964_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0));
v___x_965_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_950_, v___x_962_, v___x_961_, v___x_963_, v___x_964_);
lean_dec_ref_known(v___x_962_, 3);
v___x_966_ = lean_array_to_list(v___x_965_);
if (lean_obj_tag(v___x_966_) == 1)
{
lean_object* v_tail_967_; 
v_tail_967_ = lean_ctor_get(v___x_966_, 1);
lean_inc(v_tail_967_);
if (lean_obj_tag(v_tail_967_) == 0)
{
lean_object* v_head_968_; lean_object* v_str_969_; lean_object* v_startInclusive_970_; lean_object* v_endExclusive_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
lean_dec_ref(v_spec_950_);
v_head_968_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_head_968_);
lean_dec_ref_known(v___x_966_, 2);
v_str_969_ = lean_ctor_get(v_head_968_, 0);
lean_inc_ref(v_str_969_);
v_startInclusive_970_ = lean_ctor_get(v_head_968_, 1);
lean_inc(v_startInclusive_970_);
v_endExclusive_971_ = lean_ctor_get(v_head_968_, 2);
lean_inc(v_endExclusive_971_);
lean_dec(v_head_968_);
v___x_972_ = lean_nat_sub(v_endExclusive_971_, v_startInclusive_970_);
v___x_973_ = lean_nat_dec_eq(v___x_972_, v___x_960_);
lean_dec(v___x_972_);
if (v___x_973_ == 0)
{
if (v_explicit_953_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_string_utf8_extract(v_str_969_, v_startInclusive_970_, v_endExclusive_971_);
lean_dec(v_endExclusive_971_);
lean_dec(v_startInclusive_970_);
lean_dec_ref(v_str_969_);
v___x_975_ = l_Lake_stringToLegalOrSimpleName(v___x_974_);
v___x_976_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(v_ws_949_, v___x_975_, v_facet_951_);
return v___x_976_;
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_string_utf8_extract(v_str_969_, v_startInclusive_970_, v_endExclusive_971_);
lean_dec(v_endExclusive_971_);
lean_dec(v_startInclusive_970_);
lean_dec_ref(v_str_969_);
v___x_978_ = l_Lake_parsePackageSpec(v_ws_949_, v___x_977_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec(v_facet_951_);
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_988_; 
v_a_987_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_978_, 1);
v___x_988_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_949_, v_a_987_, v_facet_951_);
return v___x_988_;
}
}
}
else
{
lean_object* v_packages_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec(v_endExclusive_971_);
lean_dec(v_startInclusive_970_);
lean_dec_ref(v_str_969_);
v_packages_989_ = lean_ctor_get(v_ws_949_, 4);
v___x_990_ = lean_array_fget_borrowed(v_packages_989_, v___x_960_);
lean_inc(v___x_990_);
v___x_991_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_949_, v___x_990_, v_facet_951_);
return v___x_991_;
}
}
else
{
lean_object* v_tail_992_; 
v_tail_992_ = lean_ctor_get(v_tail_967_, 1);
if (lean_obj_tag(v_tail_992_) == 0)
{
lean_object* v_head_993_; lean_object* v_head_994_; lean_object* v_str_995_; lean_object* v_startInclusive_996_; lean_object* v_endExclusive_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec_ref(v_spec_950_);
v_head_993_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_head_993_);
lean_dec_ref_known(v___x_966_, 2);
v_head_994_ = lean_ctor_get(v_tail_967_, 0);
lean_inc(v_head_994_);
lean_dec_ref_known(v_tail_967_, 2);
v_str_995_ = lean_ctor_get(v_head_993_, 0);
lean_inc_ref(v_str_995_);
v_startInclusive_996_ = lean_ctor_get(v_head_993_, 1);
lean_inc(v_startInclusive_996_);
v_endExclusive_997_ = lean_ctor_get(v_head_993_, 2);
lean_inc(v_endExclusive_997_);
lean_dec(v_head_993_);
v___x_998_ = lean_string_utf8_extract(v_str_995_, v_startInclusive_996_, v_endExclusive_997_);
lean_dec(v_endExclusive_997_);
lean_dec(v_startInclusive_996_);
lean_dec_ref(v_str_995_);
v___x_999_ = l_Lake_parsePackageSpec(v_ws_949_, v___x_998_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v_head_994_);
lean_dec(v_facet_951_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1057_; 
v_a_1008_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1010_ = v___x_999_;
v_isShared_1011_ = v_isSharedCheck_1057_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_999_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1057_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v_str_1012_; lean_object* v_startInclusive_1013_; lean_object* v_endExclusive_1014_; uint8_t v___y_1016_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v_str_1012_ = lean_ctor_get(v_head_994_, 0);
lean_inc_ref(v_str_1012_);
v_startInclusive_1013_ = lean_ctor_get(v_head_994_, 1);
lean_inc(v_startInclusive_1013_);
v_endExclusive_1014_ = lean_ctor_get(v_head_994_, 2);
lean_inc(v_endExclusive_1014_);
v___x_1050_ = lean_nat_sub(v_endExclusive_1014_, v_startInclusive_1013_);
v___x_1051_ = lean_nat_dec_eq(v___x_1050_, v___x_960_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1052_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_1053_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2, &l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2);
v___x_1054_ = lean_nat_dec_le(v___x_1053_, v___x_1050_);
lean_dec(v___x_1050_);
if (v___x_1054_ == 0)
{
v___y_1016_ = v___x_1051_;
goto v___jp_1015_;
}
else
{
uint8_t v___x_1055_; 
v___x_1055_ = lean_string_memcmp(v_str_1012_, v___x_1052_, v_startInclusive_1013_, v___x_960_, v___x_1053_);
v___y_1016_ = v___x_1055_;
goto v___jp_1015_;
}
}
else
{
lean_object* v___x_1056_; 
lean_dec(v___x_1050_);
lean_dec(v_endExclusive_1014_);
lean_dec(v_startInclusive_1013_);
lean_dec_ref(v_str_1012_);
lean_del_object(v___x_1010_);
lean_dec(v_head_994_);
v___x_1056_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_949_, v_a_1008_, v_facet_951_);
return v___x_1056_;
}
v___jp_1015_:
{
if (v___y_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_del_object(v___x_1010_);
lean_dec(v_head_994_);
v___x_1017_ = lean_string_utf8_extract(v_str_1012_, v_startInclusive_1013_, v_endExclusive_1014_);
lean_dec(v_endExclusive_1014_);
lean_dec(v_startInclusive_1013_);
lean_dec_ref(v_str_1012_);
v___x_1018_ = l_Lake_stringToLegalOrSimpleName(v___x_1017_);
v___x_1019_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_949_, v_a_1008_, v___x_1018_, v_facet_951_);
return v___x_1019_;
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = l_String_Slice_Pos_nextn(v_head_994_, v___x_960_, v___x_1020_);
lean_dec(v_head_994_);
v___x_1022_ = lean_nat_add(v_startInclusive_1013_, v___x_1021_);
lean_dec(v___x_1021_);
lean_dec(v_startInclusive_1013_);
v___x_1023_ = lean_string_utf8_extract(v_str_1012_, v___x_1022_, v_endExclusive_1014_);
lean_dec(v_endExclusive_1014_);
lean_dec(v___x_1022_);
lean_dec_ref(v_str_1012_);
v___x_1024_ = l_String_toName(v___x_1023_);
lean_inc(v___x_1024_);
v___x_1025_ = l_Lake_Package_findTargetModule_x3f(v___x_1024_, v_a_1008_);
if (lean_obj_tag(v___x_1025_) == 1)
{
lean_object* v_val_1026_; lean_object* v___x_1027_; 
lean_dec(v___x_1024_);
lean_del_object(v___x_1010_);
v_val_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_val_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_949_, v_val_1026_, v_facet_951_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1045_; 
v_a_1036_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1038_ = v___x_1027_;
v_isShared_1039_ = v_isSharedCheck_1045_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1027_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1045_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1040_ = lean_mk_empty_array_with_capacity(v___x_1020_);
v___x_1041_ = lean_array_push(v___x_1040_, v_a_1036_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1041_);
v___x_1043_ = v___x_1038_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
lean_dec(v___x_1025_);
lean_dec(v_facet_951_);
v___x_1046_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1024_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set_tag(v___x_1010_, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1046_);
v___x_1048_ = v___x_1010_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_tail_967_, 2);
lean_dec_ref_known(v___x_966_, 2);
lean_dec(v_facet_951_);
goto v___jp_954_;
}
}
}
else
{
lean_dec(v___x_966_);
lean_dec(v_facet_951_);
goto v___jp_954_;
}
v___jp_954_:
{
if (v_isMaybePath_952_ == 0)
{
uint32_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = 47;
v___x_956_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_956_, 0, v_spec_950_);
lean_ctor_set_uint32(v___x_956_, sizeof(void*)*1, v___x_955_);
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
return v___x_957_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_958_, 0, v_spec_950_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___boxed(lean_object* v_ws_1058_, lean_object* v_spec_1059_, lean_object* v_facet_1060_, lean_object* v_isMaybePath_1061_, lean_object* v_explicit_1062_){
_start:
{
uint8_t v_isMaybePath_boxed_1063_; uint8_t v_explicit_boxed_1064_; lean_object* v_res_1065_; 
v_isMaybePath_boxed_1063_ = lean_unbox(v_isMaybePath_1061_);
v_explicit_boxed_1064_ = lean_unbox(v_explicit_1062_);
v_res_1065_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1058_, v_spec_1059_, v_facet_1060_, v_isMaybePath_boxed_1063_, v_explicit_boxed_1064_);
lean_dec_ref(v_ws_1058_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(lean_object* v_spec_1066_, lean_object* v___x_1067_, lean_object* v___x_1068_, lean_object* v_inst_1069_, lean_object* v_R_1070_, lean_object* v_a_1071_, lean_object* v_b_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_1066_, v___x_1067_, v___x_1068_, v_a_1071_, v_b_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___boxed(lean_object* v_spec_1074_, lean_object* v___x_1075_, lean_object* v___x_1076_, lean_object* v_inst_1077_, lean_object* v_R_1078_, lean_object* v_a_1079_, lean_object* v_b_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(v_spec_1074_, v___x_1075_, v___x_1076_, v_inst_1077_, v_R_1078_, v_a_1079_, v_b_1080_);
lean_dec_ref(v___x_1075_);
return v_res_1081_;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1084_ = lean_string_utf8_byte_size(v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(lean_object* v_ws_1085_, lean_object* v_spec_1086_, lean_object* v_facet_1087_){
_start:
{
uint8_t v___y_1090_; uint8_t v___y_1091_; uint8_t v___y_1171_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1207_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1208_ = lean_string_utf8_byte_size(v_spec_1086_);
v___x_1209_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1, &l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1);
v___x_1210_ = lean_nat_dec_le(v___x_1209_, v___x_1208_);
if (v___x_1210_ == 0)
{
v___y_1171_ = v___x_1210_;
goto v___jp_1170_;
}
else
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_unsigned_to_nat(0u);
v___x_1212_ = lean_string_memcmp(v_spec_1086_, v___x_1207_, v___x_1211_, v___x_1211_, v___x_1209_);
if (v___x_1212_ == 0)
{
v___y_1171_ = v___x_1212_;
goto v___jp_1170_;
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; lean_object* v___x_1218_; 
v___x_1213_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_spec_1086_);
v___x_1214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1214_, 0, v_spec_1086_);
lean_ctor_set(v___x_1214_, 1, v___x_1211_);
lean_ctor_set(v___x_1214_, 2, v___x_1208_);
v___x_1215_ = l_String_Slice_Pos_nextn(v___x_1214_, v___x_1211_, v___x_1213_);
lean_dec_ref_known(v___x_1214_, 3);
v___x_1216_ = lean_string_utf8_extract(v_spec_1086_, v___x_1215_, v___x_1208_);
lean_dec(v___x_1215_);
lean_dec_ref(v_spec_1086_);
v___x_1217_ = 0;
v___x_1218_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1085_, v___x_1216_, v_facet_1087_, v___x_1217_, v___x_1212_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 1);
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
v_a_1227_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1218_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1218_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set_tag(v___x_1229_, 0);
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
v___jp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
lean_inc_ref(v_spec_1086_);
v___x_1092_ = l_Lake_resolvePath(v_spec_1086_);
v___x_1093_ = lean_string_utf8_byte_size(v___x_1092_);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = lean_nat_dec_eq(v___x_1093_, v___x_1094_);
if (v___x_1095_ == 0)
{
uint8_t v___x_1096_; 
v___x_1096_ = l_System_FilePath_isDir(v___x_1092_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lake_Workspace_findModuleBySrc_x3f(v___x_1092_, v_ws_1085_);
if (lean_obj_tag(v___x_1097_) == 1)
{
lean_object* v_val_1098_; lean_object* v___x_1099_; 
lean_dec_ref(v_spec_1086_);
v_val_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_val_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1099_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_1085_, v_val_1098_, v_facet_1087_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 1);
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1118_; 
v_a_1108_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1110_ = v___x_1099_;
v_isShared_1111_ = v_isSharedCheck_1118_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1099_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1118_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1112_ = lean_unsigned_to_nat(1u);
v___x_1113_ = lean_mk_empty_array_with_capacity(v___x_1112_);
v___x_1114_ = lean_array_push(v___x_1113_, v_a_1108_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1114_);
v___x_1116_ = v___x_1110_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
lean_object* v___x_1119_; 
lean_dec(v___x_1097_);
v___x_1119_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1085_, v_spec_1086_, v_facet_1087_, v___y_1090_, v___x_1096_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 1);
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_a_1128_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1119_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1119_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 0);
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
else
{
lean_object* v___x_1136_; 
lean_dec_ref(v___x_1092_);
v___x_1136_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1085_, v_spec_1086_, v_facet_1087_, v___y_1091_, v___y_1091_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set_tag(v___x_1139_, 1);
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
v_a_1145_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1136_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1136_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set_tag(v___x_1147_, 0);
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
else
{
lean_object* v___x_1153_; 
lean_dec_ref(v___x_1092_);
v___x_1153_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1085_, v_spec_1086_, v_facet_1087_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 1);
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
v_a_1162_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1153_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1153_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set_tag(v___x_1164_, 0);
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
v___jp_1170_:
{
uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1172_ = 1;
v___x_1173_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_1174_ = lean_string_utf8_byte_size(v_spec_1086_);
v___x_1175_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2, &l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2);
v___x_1176_ = lean_nat_dec_le(v___x_1175_, v___x_1174_);
if (v___x_1176_ == 0)
{
v___y_1090_ = v___x_1172_;
v___y_1091_ = v___y_1171_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = lean_string_memcmp(v_spec_1086_, v___x_1173_, v___x_1177_, v___x_1177_, v___x_1175_);
if (v___x_1178_ == 0)
{
v___y_1090_ = v___x_1172_;
v___y_1091_ = v___x_1178_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v_mod_1183_; lean_object* v___x_1184_; 
v___x_1179_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_spec_1086_);
v___x_1180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1180_, 0, v_spec_1086_);
lean_ctor_set(v___x_1180_, 1, v___x_1177_);
lean_ctor_set(v___x_1180_, 2, v___x_1174_);
v___x_1181_ = l_String_Slice_Pos_nextn(v___x_1180_, v___x_1177_, v___x_1179_);
lean_dec_ref_known(v___x_1180_, 3);
v___x_1182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1182_, 0, v_spec_1086_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
lean_ctor_set(v___x_1182_, 2, v___x_1174_);
v_mod_1183_ = l_String_Slice_toName(v___x_1182_);
lean_dec_ref_known(v___x_1182_, 3);
lean_inc(v_mod_1183_);
v___x_1184_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_1183_, v_ws_1085_);
if (lean_obj_tag(v___x_1184_) == 1)
{
lean_object* v_val_1185_; lean_object* v___x_1186_; 
lean_dec(v_mod_1183_);
v_val_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v___x_1186_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_1085_, v_val_1185_, v_facet_1087_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 1);
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1204_; 
v_a_1195_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1197_ = v___x_1186_;
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1186_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1199_ = lean_mk_empty_array_with_capacity(v___x_1179_);
v___x_1200_ = lean_array_push(v___x_1199_, v_a_1195_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set_tag(v___x_1197_, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1200_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec(v___x_1184_);
lean_dec(v_facet_1087_);
v___x_1205_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_mod_1183_);
v___x_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___boxed(lean_object* v_ws_1235_, lean_object* v_spec_1236_, lean_object* v_facet_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1235_, v_spec_1236_, v_facet_1237_);
lean_dec_ref(v_ws_1235_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object* v_ws_1240_, lean_object* v_spec_1241_){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_string_utf8_byte_size(v_spec_1241_);
lean_inc_ref_n(v_spec_1241_, 2);
v___x_1251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1251_, 0, v_spec_1241_);
lean_ctor_set(v___x_1251_, 1, v___x_1249_);
lean_ctor_set(v___x_1251_, 2, v___x_1250_);
v___x_1252_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v___x_1251_);
v___x_1253_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0));
v___x_1254_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_1241_, v___x_1251_, v___x_1250_, v___x_1252_, v___x_1253_);
lean_dec_ref_known(v___x_1251_, 3);
v___x_1255_ = lean_array_to_list(v___x_1254_);
if (lean_obj_tag(v___x_1255_) == 1)
{
lean_object* v_tail_1256_; 
v_tail_1256_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_tail_1256_);
if (lean_obj_tag(v_tail_1256_) == 0)
{
lean_object* v_head_1257_; lean_object* v_str_1258_; lean_object* v_startInclusive_1259_; lean_object* v_endExclusive_1260_; lean_object* v___x_1261_; lean_object* v_targetName_1262_; lean_object* v___x_1263_; 
v_head_1257_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_head_1257_);
lean_dec_ref_known(v___x_1255_, 2);
v_str_1258_ = lean_ctor_get(v_head_1257_, 0);
lean_inc_ref(v_str_1258_);
v_startInclusive_1259_ = lean_ctor_get(v_head_1257_, 1);
lean_inc(v_startInclusive_1259_);
v_endExclusive_1260_ = lean_ctor_get(v_head_1257_, 2);
lean_inc(v_endExclusive_1260_);
lean_dec(v_head_1257_);
v___x_1261_ = lean_string_utf8_extract(v_str_1258_, v_startInclusive_1259_, v_endExclusive_1260_);
lean_dec(v_endExclusive_1260_);
lean_dec(v_startInclusive_1259_);
lean_dec_ref(v_str_1258_);
v_targetName_1262_ = l_Lake_stringToLegalOrSimpleName(v___x_1261_);
v___x_1263_ = l_Lake_Workspace_findLeanExe_x3f(v_targetName_1262_, v_ws_1240_);
lean_dec(v_targetName_1262_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_spec_1241_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
else
{
lean_object* v_val_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_spec_1241_);
v_val_1266_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1263_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_val_1266_);
lean_dec(v___x_1263_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_val_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_head_1274_; lean_object* v_head_1275_; lean_object* v_tail_1276_; lean_object* v_str_1278_; lean_object* v_startInclusive_1279_; lean_object* v_endExclusive_1280_; 
v_head_1274_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_head_1274_);
lean_dec_ref_known(v___x_1255_, 2);
v_head_1275_ = lean_ctor_get(v_tail_1256_, 0);
lean_inc(v_head_1275_);
v_tail_1276_ = lean_ctor_get(v_tail_1256_, 1);
lean_inc(v_tail_1276_);
lean_dec_ref_known(v_tail_1256_, 2);
if (lean_obj_tag(v_tail_1276_) == 0)
{
lean_object* v_str_1318_; lean_object* v_startInclusive_1319_; lean_object* v_endExclusive_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v_str_1318_ = lean_ctor_get(v_head_1274_, 0);
lean_inc_ref(v_str_1318_);
v_startInclusive_1319_ = lean_ctor_get(v_head_1274_, 1);
lean_inc(v_startInclusive_1319_);
v_endExclusive_1320_ = lean_ctor_get(v_head_1274_, 2);
lean_inc(v_endExclusive_1320_);
v___x_1321_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1322_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1, &l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1);
v___x_1323_ = lean_nat_sub(v_endExclusive_1320_, v_startInclusive_1319_);
v___x_1324_ = lean_nat_dec_le(v___x_1322_, v___x_1323_);
lean_dec(v___x_1323_);
if (v___x_1324_ == 0)
{
lean_dec(v_head_1274_);
v_str_1278_ = v_str_1318_;
v_startInclusive_1279_ = v_startInclusive_1319_;
v_endExclusive_1280_ = v_endExclusive_1320_;
goto v___jp_1277_;
}
else
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_string_memcmp(v_str_1318_, v___x_1321_, v_startInclusive_1319_, v___x_1249_, v___x_1322_);
if (v___x_1325_ == 0)
{
lean_dec(v_head_1274_);
v_str_1278_ = v_str_1318_;
v_startInclusive_1279_ = v_startInclusive_1319_;
v_endExclusive_1280_ = v_endExclusive_1320_;
goto v___jp_1277_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = lean_unsigned_to_nat(1u);
v___x_1327_ = l_String_Slice_Pos_nextn(v_head_1274_, v___x_1249_, v___x_1326_);
lean_dec(v_head_1274_);
v___x_1328_ = lean_nat_add(v_startInclusive_1319_, v___x_1327_);
lean_dec(v___x_1327_);
lean_dec(v_startInclusive_1319_);
v_str_1278_ = v_str_1318_;
v_startInclusive_1279_ = v___x_1328_;
v_endExclusive_1280_ = v_endExclusive_1320_;
goto v___jp_1277_;
}
}
}
else
{
lean_dec(v_tail_1276_);
lean_dec(v_head_1275_);
lean_dec(v_head_1274_);
goto v___jp_1245_;
}
v___jp_1277_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_string_utf8_extract(v_str_1278_, v_startInclusive_1279_, v_endExclusive_1280_);
lean_dec(v_endExclusive_1280_);
lean_dec(v_startInclusive_1279_);
lean_dec_ref(v_str_1278_);
v___x_1282_ = l_Lake_parsePackageSpec(v_ws_1240_, v___x_1281_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_head_1275_);
lean_dec_ref(v_spec_1241_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1317_; 
v_a_1291_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1293_ = v___x_1282_;
v_isShared_1294_ = v_isSharedCheck_1317_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1282_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1317_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_str_1295_; lean_object* v_startInclusive_1296_; lean_object* v_endExclusive_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1316_; 
v_str_1295_ = lean_ctor_get(v_head_1275_, 0);
v_startInclusive_1296_ = lean_ctor_get(v_head_1275_, 1);
v_endExclusive_1297_ = lean_ctor_get(v_head_1275_, 2);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_head_1275_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1299_ = v_head_1275_;
v_isShared_1300_ = v_isSharedCheck_1316_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_endExclusive_1297_);
lean_inc(v_startInclusive_1296_);
lean_inc(v_str_1295_);
lean_dec(v_head_1275_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1316_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_string_utf8_extract(v_str_1295_, v_startInclusive_1296_, v_endExclusive_1297_);
lean_dec(v_endExclusive_1297_);
lean_dec(v_startInclusive_1296_);
lean_dec_ref(v_str_1295_);
v___x_1302_ = l_Lake_stringToLegalOrSimpleName(v___x_1301_);
v___x_1303_ = l_Lake_Package_findTargetDecl_x3f(v___x_1302_, v_a_1291_);
lean_dec(v___x_1302_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_del_object(v___x_1299_);
lean_del_object(v___x_1293_);
lean_dec(v_a_1291_);
goto v___jp_1242_;
}
else
{
lean_object* v_val_1304_; lean_object* v_name_1305_; lean_object* v_kind_1306_; lean_object* v_config_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_val_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_val_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v_name_1305_ = lean_ctor_get(v_val_1304_, 1);
lean_inc(v_name_1305_);
v_kind_1306_ = lean_ctor_get(v_val_1304_, 2);
lean_inc(v_kind_1306_);
v_config_1307_ = lean_ctor_get(v_val_1304_, 3);
lean_inc(v_config_1307_);
lean_dec(v_val_1304_);
v___x_1308_ = l_Lake_LeanExe_keyword;
v___x_1309_ = lean_name_eq(v_kind_1306_, v___x_1308_);
lean_dec(v_kind_1306_);
if (v___x_1309_ == 0)
{
lean_dec(v_config_1307_);
lean_dec(v_name_1305_);
lean_del_object(v___x_1299_);
lean_del_object(v___x_1293_);
lean_dec(v_a_1291_);
goto v___jp_1242_;
}
else
{
lean_object* v___x_1311_; 
lean_dec_ref(v_spec_1241_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 2, v_config_1307_);
lean_ctor_set(v___x_1299_, 1, v_name_1305_);
lean_ctor_set(v___x_1299_, 0, v_a_1291_);
v___x_1311_ = v___x_1299_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1291_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_name_1305_);
lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_config_1307_);
v___x_1311_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1313_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1311_);
v___x_1313_ = v___x_1293_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
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
lean_dec(v___x_1255_);
goto v___jp_1245_;
}
v___jp_1242_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_spec_1241_);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
v___jp_1245_:
{
uint32_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = 47;
v___x_1247_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_1247_, 0, v_spec_1241_);
lean_ctor_set_uint32(v___x_1247_, sizeof(void*)*1, v___x_1246_);
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed(lean_object* v_ws_1329_, lean_object* v_spec_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lake_parseExeTargetSpec(v_ws_1329_, v_spec_1330_);
lean_dec_ref(v_ws_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(lean_object* v_s_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0));
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___boxed(lean_object* v_s_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(v_s_1334_);
lean_dec_ref(v_s_1334_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(lean_object* v_spec_1336_, lean_object* v___x_1337_, lean_object* v___x_1338_, lean_object* v_a_1339_, lean_object* v_b_1340_){
_start:
{
lean_object* v_it_1342_; lean_object* v_startInclusive_1343_; lean_object* v_endExclusive_1344_; 
if (lean_obj_tag(v_a_1339_) == 0)
{
lean_object* v_currPos_1349_; lean_object* v_searcher_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1376_; 
v_currPos_1349_ = lean_ctor_get(v_a_1339_, 0);
v_searcher_1350_ = lean_ctor_get(v_a_1339_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_a_1339_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1352_ = v_a_1339_;
v_isShared_1353_ = v_isSharedCheck_1376_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_searcher_1350_);
lean_inc(v_currPos_1349_);
lean_dec(v_a_1339_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1376_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v_startInclusive_1354_; lean_object* v_endExclusive_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_startInclusive_1354_ = lean_ctor_get(v___x_1337_, 1);
v_endExclusive_1355_ = lean_ctor_get(v___x_1337_, 2);
v___x_1356_ = lean_nat_sub(v_endExclusive_1355_, v_startInclusive_1354_);
v___x_1357_ = lean_nat_dec_eq(v_searcher_1350_, v___x_1356_);
lean_dec(v___x_1356_);
if (v___x_1357_ == 0)
{
uint32_t v___x_1358_; uint32_t v___x_1359_; uint8_t v___x_1360_; 
v___x_1358_ = 58;
v___x_1359_ = lean_string_utf8_get_fast(v_spec_1336_, v_searcher_1350_);
v___x_1360_ = lean_uint32_dec_eq(v___x_1359_, v___x_1358_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1361_ = lean_string_utf8_next_fast(v_spec_1336_, v_searcher_1350_);
lean_dec(v_searcher_1350_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 1, v___x_1361_);
v___x_1363_ = v___x_1352_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_currPos_1349_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
v_a_1339_ = v___x_1363_;
goto _start;
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v_slice_1369_; lean_object* v_nextIt_1371_; 
v___x_1366_ = lean_string_utf8_next_fast(v_spec_1336_, v_searcher_1350_);
v___x_1367_ = lean_nat_sub(v___x_1366_, v_searcher_1350_);
v___x_1368_ = lean_nat_add(v_searcher_1350_, v___x_1367_);
lean_dec(v___x_1367_);
v_slice_1369_ = l_String_Slice_subslice_x21(v___x_1337_, v_currPos_1349_, v_searcher_1350_);
lean_inc(v___x_1368_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 1, v___x_1368_);
lean_ctor_set(v___x_1352_, 0, v___x_1368_);
v_nextIt_1371_ = v___x_1352_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v___x_1368_);
v_nextIt_1371_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v_startInclusive_1372_; lean_object* v_endExclusive_1373_; 
v_startInclusive_1372_ = lean_ctor_get(v_slice_1369_, 0);
lean_inc(v_startInclusive_1372_);
v_endExclusive_1373_ = lean_ctor_get(v_slice_1369_, 1);
lean_inc(v_endExclusive_1373_);
lean_dec_ref(v_slice_1369_);
v_it_1342_ = v_nextIt_1371_;
v_startInclusive_1343_ = v_startInclusive_1372_;
v_endExclusive_1344_ = v_endExclusive_1373_;
goto v___jp_1341_;
}
}
}
else
{
lean_object* v___x_1375_; 
lean_del_object(v___x_1352_);
lean_dec(v_searcher_1350_);
v___x_1375_ = lean_box(1);
lean_inc(v___x_1338_);
v_it_1342_ = v___x_1375_;
v_startInclusive_1343_ = v_currPos_1349_;
v_endExclusive_1344_ = v___x_1338_;
goto v___jp_1341_;
}
}
}
else
{
lean_dec(v___x_1338_);
lean_dec_ref(v_spec_1336_);
return v_b_1340_;
}
v___jp_1341_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_inc_ref(v_spec_1336_);
v___x_1345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1345_, 0, v_spec_1336_);
lean_ctor_set(v___x_1345_, 1, v_startInclusive_1343_);
lean_ctor_set(v___x_1345_, 2, v_endExclusive_1344_);
v___x_1346_ = l_String_Slice_toString(v___x_1345_);
lean_dec_ref_known(v___x_1345_, 3);
v___x_1347_ = lean_array_push(v_b_1340_, v___x_1346_);
v_a_1339_ = v_it_1342_;
v_b_1340_ = v___x_1347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg___boxed(lean_object* v_spec_1377_, lean_object* v___x_1378_, lean_object* v___x_1379_, lean_object* v_a_1380_, lean_object* v_b_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1377_, v___x_1378_, v___x_1379_, v_a_1380_, v_b_1381_);
lean_dec_ref(v___x_1378_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec(lean_object* v_ws_1385_, lean_object* v_spec_1386_){
_start:
{
uint32_t v___x_1388_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1388_ = 58;
v___x_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = lean_string_utf8_byte_size(v_spec_1386_);
lean_inc_ref_n(v_spec_1386_, 2);
v___x_1394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1394_, 0, v_spec_1386_);
lean_ctor_set(v___x_1394_, 1, v___x_1392_);
lean_ctor_set(v___x_1394_, 2, v___x_1393_);
v___x_1395_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(v___x_1394_);
v___x_1396_ = ((lean_object*)(l_Lake_parseTargetSpec___closed__0));
v___x_1397_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1386_, v___x_1394_, v___x_1393_, v___x_1395_, v___x_1396_);
lean_dec_ref_known(v___x_1394_, 3);
v___x_1398_ = lean_array_to_list(v___x_1397_);
if (lean_obj_tag(v___x_1398_) == 1)
{
lean_object* v_tail_1399_; 
v_tail_1399_ = lean_ctor_get(v___x_1398_, 1);
lean_inc(v_tail_1399_);
if (lean_obj_tag(v_tail_1399_) == 0)
{
lean_object* v_head_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec_ref(v_spec_1386_);
v_head_1400_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_head_1400_);
lean_dec_ref_known(v___x_1398_, 2);
v___x_1401_ = lean_box(0);
v___x_1402_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1385_, v_head_1400_, v___x_1401_);
return v___x_1402_;
}
else
{
lean_object* v_tail_1403_; 
v_tail_1403_ = lean_ctor_get(v_tail_1399_, 1);
if (lean_obj_tag(v_tail_1403_) == 0)
{
lean_object* v_head_1404_; lean_object* v_head_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec_ref(v_spec_1386_);
v_head_1404_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_head_1404_);
lean_dec_ref_known(v___x_1398_, 2);
v_head_1405_ = lean_ctor_get(v_tail_1399_, 0);
lean_inc(v_head_1405_);
lean_dec_ref_known(v_tail_1399_, 2);
v___x_1406_ = l_String_toName(v_head_1405_);
v___x_1407_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1385_, v_head_1404_, v___x_1406_);
return v___x_1407_;
}
else
{
lean_dec_ref_known(v_tail_1399_, 2);
lean_dec_ref_known(v___x_1398_, 2);
goto v___jp_1389_;
}
}
}
else
{
lean_dec(v___x_1398_);
goto v___jp_1389_;
}
v___jp_1389_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_1390_, 0, v_spec_1386_);
lean_ctor_set_uint32(v___x_1390_, sizeof(void*)*1, v___x_1388_);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec___boxed(lean_object* v_ws_1408_, lean_object* v_spec_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lake_parseTargetSpec(v_ws_1408_, v_spec_1409_);
lean_dec_ref(v_ws_1408_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(lean_object* v_spec_1412_, lean_object* v___x_1413_, lean_object* v___x_1414_, lean_object* v_inst_1415_, lean_object* v_R_1416_, lean_object* v_a_1417_, lean_object* v_b_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1412_, v___x_1413_, v___x_1414_, v_a_1417_, v_b_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___boxed(lean_object* v_spec_1420_, lean_object* v___x_1421_, lean_object* v___x_1422_, lean_object* v_inst_1423_, lean_object* v_R_1424_, lean_object* v_a_1425_, lean_object* v_b_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(v_spec_1420_, v___x_1421_, v___x_1422_, v_inst_1423_, v_R_1424_, v_a_1425_, v_b_1426_);
lean_dec_ref(v___x_1421_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(lean_object* v_ws_1428_, lean_object* v_as_x27_1429_, lean_object* v_b_1430_){
_start:
{
if (lean_obj_tag(v_as_x27_1429_) == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_b_1430_);
return v___x_1432_;
}
else
{
lean_object* v_head_1433_; lean_object* v_tail_1434_; lean_object* v___x_1435_; 
v_head_1433_ = lean_ctor_get(v_as_x27_1429_, 0);
v_tail_1434_ = lean_ctor_get(v_as_x27_1429_, 1);
lean_inc(v_head_1433_);
v___x_1435_ = l_Lake_parseTargetSpec(v_ws_1428_, v_head_1433_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = l_Array_append___redArg(v_b_1430_, v_a_1436_);
lean_dec(v_a_1436_);
v_as_x27_1429_ = v_tail_1434_;
v_b_1430_ = v___x_1437_;
goto _start;
}
else
{
lean_dec_ref(v_b_1430_);
return v___x_1435_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg___boxed(lean_object* v_ws_1439_, lean_object* v_as_x27_1440_, lean_object* v_b_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1439_, v_as_x27_1440_, v_b_1441_);
lean_dec(v_as_x27_1440_);
lean_dec_ref(v_ws_1439_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs(lean_object* v_ws_1446_, lean_object* v_specs_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v_results_1450_; lean_object* v___x_1451_; 
v___x_1449_ = lean_unsigned_to_nat(0u);
v_results_1450_ = ((lean_object*)(l_Lake_parseTargetSpecs___closed__0));
v___x_1451_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1446_, v_specs_1447_, v_results_1450_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
v___x_1453_ = lean_array_get_size(v_a_1452_);
lean_dec(v_a_1452_);
v___x_1454_ = lean_nat_dec_eq(v___x_1453_, v___x_1449_);
if (v___x_1454_ == 0)
{
return v___x_1451_;
}
else
{
lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1469_; 
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1451_, 0);
lean_dec(v_unused_1470_);
v___x_1456_ = v___x_1451_;
v_isShared_1457_ = v_isSharedCheck_1469_;
goto v_resetjp_1455_;
}
else
{
lean_dec(v___x_1451_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1469_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v_packages_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_packages_1458_ = lean_ctor_get(v_ws_1446_, 4);
v___x_1459_ = lean_array_fget_borrowed(v_packages_1458_, v___x_1449_);
lean_inc(v___x_1459_);
v___x_1460_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_1446_, v___x_1459_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1463_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
if (v_isShared_1457_ == 0)
{
lean_ctor_set_tag(v___x_1456_, 1);
lean_ctor_set(v___x_1456_, 0, v_a_1461_);
v___x_1463_ = v___x_1456_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; 
v_a_1465_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1465_);
lean_dec_ref_known(v___x_1460_, 1);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v_a_1465_);
v___x_1467_ = v___x_1456_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
else
{
return v___x_1451_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___boxed(lean_object* v_ws_1471_, lean_object* v_specs_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lake_parseTargetSpecs(v_ws_1471_, v_specs_1472_);
lean_dec(v_specs_1472_);
lean_dec_ref(v_ws_1471_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(lean_object* v_ws_1475_, lean_object* v_as_1476_, lean_object* v_as_x27_1477_, lean_object* v_b_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1475_, v_as_x27_1477_, v_b_1478_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___boxed(lean_object* v_ws_1482_, lean_object* v_as_1483_, lean_object* v_as_x27_1484_, lean_object* v_b_1485_, lean_object* v_a_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(v_ws_1482_, v_as_1483_, v_as_x27_1484_, v_b_1485_, v_a_1486_);
lean_dec(v_as_x27_1484_);
lean_dec(v_as_1483_);
lean_dec_ref(v_ws_1482_);
return v_res_1488_;
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
