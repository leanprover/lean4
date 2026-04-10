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
lean_object* v_name_654_; lean_object* v_kind_655_; lean_object* v_config_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_712_; 
v_name_654_ = lean_ctor_get(v_decl_652_, 1);
v_kind_655_ = lean_ctor_get(v_decl_652_, 2);
v_config_656_ = lean_ctor_get(v_decl_652_, 3);
v_isSharedCheck_712_ = !lean_is_exclusive(v_decl_652_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v_decl_652_, 0);
lean_dec(v_unused_713_);
v___x_658_ = v_decl_652_;
v_isShared_659_ = v_isSharedCheck_712_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_config_656_);
lean_inc(v_kind_655_);
lean_inc(v_name_654_);
lean_dec(v_decl_652_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_712_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
uint8_t v___x_660_; 
v___x_660_ = l_Lean_Name_isAnonymous(v_kind_655_);
if (v___x_660_ == 0)
{
uint8_t v___x_661_; lean_object* v___y_663_; uint8_t v___x_690_; 
lean_dec(v_target_651_);
v___x_661_ = 1;
v___x_690_ = l_Lean_Name_isAnonymous(v_facet_653_);
if (v___x_690_ == 0)
{
v___y_663_ = v_facet_653_;
goto v___jp_662_;
}
else
{
lean_object* v___x_691_; 
lean_dec(v_facet_653_);
v___x_691_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1));
v___y_663_ = v___x_691_;
goto v___jp_662_;
}
v___jp_662_:
{
lean_object* v_facetConfigs_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_facetConfigs_664_ = lean_ctor_get(v_ws_649_, 7);
lean_inc(v___y_663_);
lean_inc(v_kind_655_);
v___x_665_ = l_Lean_Name_append(v_kind_655_, v___y_663_);
v___x_666_ = l_Lake_FacetConfigMap_get_x3f(v___x_665_, v_facetConfigs_664_);
if (lean_obj_tag(v___x_666_) == 1)
{
lean_object* v_val_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_686_; 
lean_dec(v___y_663_);
v_val_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_686_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_686_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_val_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_686_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_keyName_671_; uint8_t v_buildable_672_; lean_object* v_format_673_; lean_object* v_tgt_674_; lean_object* v___x_675_; lean_object* v_info_677_; 
v_keyName_671_ = lean_ctor_get(v_pkg_650_, 2);
lean_inc(v_keyName_671_);
v_buildable_672_ = lean_ctor_get_uint8(v_val_667_, sizeof(void*)*4);
v_format_673_ = lean_ctor_get(v_val_667_, 3);
lean_inc_ref(v_format_673_);
lean_dec(v_val_667_);
lean_inc(v_name_654_);
v_tgt_674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_tgt_674_, 0, v_pkg_650_);
lean_ctor_set(v_tgt_674_, 1, v_name_654_);
lean_ctor_set(v_tgt_674_, 2, v_config_656_);
v___x_675_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_675_, 0, v_keyName_671_);
lean_ctor_set(v___x_675_, 1, v_name_654_);
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 1);
lean_ctor_set(v___x_658_, 3, v___x_665_);
lean_ctor_set(v___x_658_, 2, v_tgt_674_);
lean_ctor_set(v___x_658_, 1, v_kind_655_);
lean_ctor_set(v___x_658_, 0, v___x_675_);
v_info_677_ = v___x_658_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_kind_655_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_tgt_674_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v___x_665_);
v_info_677_ = v_reuseFailAlloc_685_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_678_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_678_, 0, v_info_677_);
lean_ctor_set(v___x_678_, 1, v_format_673_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*2, v_buildable_672_);
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_mk_empty_array_with_capacity(v___x_679_);
v___x_681_ = lean_array_push(v___x_680_, v___x_678_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_681_);
v___x_683_ = v___x_669_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_del_object(v___x_658_);
lean_dec(v_config_656_);
lean_dec(v_name_654_);
lean_dec_ref(v_pkg_650_);
v___x_687_ = l_Lean_Name_toString(v_kind_655_, v___x_661_);
v___x_688_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___y_663_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
}
else
{
lean_object* v___x_692_; 
lean_del_object(v___x_658_);
lean_dec(v_kind_655_);
lean_dec(v_name_654_);
v___x_692_ = l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(v_pkg_650_, v_target_651_, v_facet_653_, v_config_656_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_711_; 
v_a_701_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_711_ == 0)
{
v___x_703_ = v___x_692_;
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_692_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_mk_empty_array_with_capacity(v___x_705_);
v___x_707_ = lean_array_push(v___x_706_, v_a_701_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_707_);
v___x_709_ = v___x_703_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___boxed(lean_object* v_ws_714_, lean_object* v_pkg_715_, lean_object* v_target_716_, lean_object* v_decl_717_, lean_object* v_facet_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_714_, v_pkg_715_, v_target_716_, v_decl_717_, v_facet_718_);
lean_dec_ref(v_ws_714_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(lean_object* v_ws_720_, lean_object* v_pkg_721_, lean_object* v_target_722_, lean_object* v_facet_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lake_Package_findTargetDecl_x3f(v_target_722_, v_pkg_721_);
if (lean_obj_tag(v___x_724_) == 1)
{
lean_object* v_val_725_; lean_object* v___x_726_; 
v_val_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_val_725_);
lean_dec_ref(v___x_724_);
v___x_726_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_720_, v_pkg_721_, v_target_722_, v_val_725_, v_facet_723_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; 
lean_dec(v___x_724_);
lean_inc_ref(v_pkg_721_);
lean_inc(v_target_722_);
v___x_727_ = l_Lake_Package_findTargetModule_x3f(v_target_722_, v_pkg_721_);
if (lean_obj_tag(v___x_727_) == 1)
{
lean_object* v_val_728_; lean_object* v___x_729_; 
lean_dec(v_target_722_);
lean_dec_ref(v_pkg_721_);
v_val_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_val_728_);
lean_dec_ref(v___x_727_);
v___x_729_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_720_, v_val_728_, v_facet_723_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_748_; 
v_a_738_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_748_ == 0)
{
v___x_740_ = v___x_729_;
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_729_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = lean_mk_empty_array_with_capacity(v___x_742_);
v___x_744_ = lean_array_push(v___x_743_, v_a_738_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_744_);
v___x_746_ = v___x_740_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v_baseName_749_; uint8_t v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec(v___x_727_);
lean_dec(v_facet_723_);
v_baseName_749_ = lean_ctor_get(v_pkg_721_, 1);
lean_inc(v_baseName_749_);
lean_dec_ref(v_pkg_721_);
v___x_750_ = 0;
v___x_751_ = l_Lean_Name_toString(v_target_722_, v___x_750_);
v___x_752_ = lean_alloc_ctor(17, 2, 0);
lean_ctor_set(v___x_752_, 0, v_baseName_749_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage___boxed(lean_object* v_ws_754_, lean_object* v_pkg_755_, lean_object* v_target_756_, lean_object* v_facet_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_754_, v_pkg_755_, v_target_756_, v_facet_757_);
lean_dec_ref(v_ws_754_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(lean_object* v_ws_759_, lean_object* v_pkg_760_, lean_object* v_as_761_, size_t v_i_762_, size_t v_stop_763_, lean_object* v_b_764_){
_start:
{
lean_object* v_a_766_; uint8_t v___x_770_; 
v___x_770_ = lean_usize_dec_eq(v_i_762_, v_stop_763_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_array_uget_borrowed(v_as_761_, v_i_762_);
v___x_772_ = lean_box(0);
lean_inc(v___x_771_);
lean_inc_ref(v_pkg_760_);
v___x_773_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_759_, v_pkg_760_, v___x_771_, v___x_772_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_dec_ref(v_b_764_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_dec_ref(v_pkg_760_);
return v___x_773_;
}
else
{
lean_object* v_a_774_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref(v___x_773_);
v_a_766_ = v_a_774_;
goto v___jp_765_;
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_776_; 
v_a_775_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_775_);
lean_dec_ref(v___x_773_);
v___x_776_ = l_Array_append___redArg(v_b_764_, v_a_775_);
lean_dec(v_a_775_);
v_a_766_ = v___x_776_;
goto v___jp_765_;
}
}
else
{
lean_object* v___x_777_; 
lean_dec_ref(v_pkg_760_);
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v_b_764_);
return v___x_777_;
}
v___jp_765_:
{
size_t v___x_767_; size_t v___x_768_; 
v___x_767_ = ((size_t)1ULL);
v___x_768_ = lean_usize_add(v_i_762_, v___x_767_);
v_i_762_ = v___x_768_;
v_b_764_ = v_a_766_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0___boxed(lean_object* v_ws_778_, lean_object* v_pkg_779_, lean_object* v_as_780_, lean_object* v_i_781_, lean_object* v_stop_782_, lean_object* v_b_783_){
_start:
{
size_t v_i_boxed_784_; size_t v_stop_boxed_785_; lean_object* v_res_786_; 
v_i_boxed_784_ = lean_unbox_usize(v_i_781_);
lean_dec(v_i_781_);
v_stop_boxed_785_ = lean_unbox_usize(v_stop_782_);
lean_dec(v_stop_782_);
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_778_, v_pkg_779_, v_as_780_, v_i_boxed_784_, v_stop_boxed_785_, v_b_783_);
lean_dec_ref(v_as_780_);
lean_dec_ref(v_ws_778_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(lean_object* v_ws_791_, lean_object* v_pkg_792_){
_start:
{
lean_object* v_defaultTargets_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_defaultTargets_793_ = lean_ctor_get(v_pkg_792_, 15);
lean_inc_ref(v_defaultTargets_793_);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0));
v___x_796_ = lean_array_get_size(v_defaultTargets_793_);
v___x_797_ = lean_nat_dec_lt(v___x_794_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; 
lean_dec_ref(v_defaultTargets_793_);
lean_dec_ref(v_pkg_792_);
v___x_798_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1));
return v___x_798_;
}
else
{
uint8_t v___x_799_; 
v___x_799_ = lean_nat_dec_le(v___x_796_, v___x_796_);
if (v___x_799_ == 0)
{
if (v___x_797_ == 0)
{
lean_object* v___x_800_; 
lean_dec_ref(v_defaultTargets_793_);
lean_dec_ref(v_pkg_792_);
v___x_800_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1));
return v___x_800_;
}
else
{
size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
v___x_801_ = ((size_t)0ULL);
v___x_802_ = lean_usize_of_nat(v___x_796_);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_791_, v_pkg_792_, v_defaultTargets_793_, v___x_801_, v___x_802_, v___x_795_);
lean_dec_ref(v_defaultTargets_793_);
return v___x_803_;
}
}
else
{
size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_804_ = ((size_t)0ULL);
v___x_805_ = lean_usize_of_nat(v___x_796_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_791_, v_pkg_792_, v_defaultTargets_793_, v___x_804_, v___x_805_, v___x_795_);
lean_dec_ref(v_defaultTargets_793_);
return v___x_806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___boxed(lean_object* v_ws_807_, lean_object* v_pkg_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_807_, v_pkg_808_);
lean_dec_ref(v_ws_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(lean_object* v_ws_811_, lean_object* v_pkg_812_, lean_object* v_facet_813_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = l_Lean_Name_isAnonymous(v_facet_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = l_Lake_Package_keyword;
lean_inc(v_facet_813_);
v___x_816_ = l_Lean_Name_append(v___x_815_, v_facet_813_);
v___x_817_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v___x_816_, v_ws_811_);
if (lean_obj_tag(v___x_817_) == 1)
{
lean_object* v_val_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_facet_813_);
v_val_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_834_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_834_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_val_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_834_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v_keyName_822_; uint8_t v_buildable_823_; lean_object* v_format_824_; lean_object* v___x_826_; 
v_keyName_822_ = lean_ctor_get(v_pkg_812_, 2);
v_buildable_823_ = lean_ctor_get_uint8(v_val_818_, sizeof(void*)*4);
v_format_824_ = lean_ctor_get(v_val_818_, 3);
lean_inc_ref(v_format_824_);
lean_dec(v_val_818_);
lean_inc(v_keyName_822_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v_keyName_822_);
v___x_826_ = v___x_820_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_keyName_822_);
v___x_826_ = v_reuseFailAlloc_833_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_827_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v___x_815_);
lean_ctor_set(v___x_827_, 2, v_pkg_812_);
lean_ctor_set(v___x_827_, 3, v___x_816_);
v___x_828_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_format_824_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*2, v_buildable_823_);
v___x_829_ = lean_unsigned_to_nat(1u);
v___x_830_ = lean_mk_empty_array_with_capacity(v___x_829_);
v___x_831_ = lean_array_push(v___x_830_, v___x_828_);
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v___x_817_);
lean_dec(v___x_816_);
lean_dec_ref(v_pkg_812_);
v___x_835_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0));
v___x_836_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v_facet_813_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
}
else
{
lean_object* v___x_838_; 
lean_dec(v_facet_813_);
v___x_838_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_811_, v_pkg_812_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___boxed(lean_object* v_ws_839_, lean_object* v_pkg_840_, lean_object* v_facet_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_839_, v_pkg_840_, v_facet_841_);
lean_dec_ref(v_ws_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(lean_object* v_ws_843_, lean_object* v_target_844_, lean_object* v_facet_845_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lake_Workspace_findTargetDecl_x3f(v_target_844_, v_ws_843_);
if (lean_obj_tag(v___x_871_) == 1)
{
lean_object* v_val_872_; lean_object* v_fst_873_; lean_object* v_snd_874_; lean_object* v___x_875_; 
v_val_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_val_872_);
lean_dec_ref(v___x_871_);
v_fst_873_ = lean_ctor_get(v_val_872_, 0);
lean_inc(v_fst_873_);
v_snd_874_ = lean_ctor_get(v_val_872_, 1);
lean_inc(v_snd_874_);
lean_dec(v_val_872_);
v___x_875_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_843_, v_fst_873_, v_target_844_, v_snd_874_, v_facet_845_);
return v___x_875_;
}
else
{
lean_object* v_packages_876_; lean_object* v___x_877_; size_t v_sz_878_; size_t v___x_879_; lean_object* v___x_880_; lean_object* v_fst_881_; 
lean_dec(v___x_871_);
v_packages_876_ = lean_ctor_get(v_ws_843_, 5);
v___x_877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0));
v_sz_878_ = lean_array_size(v_packages_876_);
v___x_879_ = ((size_t)0ULL);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v_target_844_, v_packages_876_, v_sz_878_, v___x_879_, v___x_877_);
v_fst_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_fst_881_);
lean_dec_ref(v___x_880_);
if (lean_obj_tag(v_fst_881_) == 0)
{
goto v___jp_846_;
}
else
{
lean_object* v_val_882_; 
v_val_882_ = lean_ctor_get(v_fst_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref(v_fst_881_);
if (lean_obj_tag(v_val_882_) == 1)
{
lean_object* v_val_883_; lean_object* v___x_884_; 
lean_dec(v_target_844_);
v_val_883_ = lean_ctor_get(v_val_882_, 0);
lean_inc(v_val_883_);
lean_dec_ref(v_val_882_);
v___x_884_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_843_, v_val_883_, v_facet_845_);
return v___x_884_;
}
else
{
lean_dec(v_val_882_);
goto v___jp_846_;
}
}
}
v___jp_846_:
{
lean_object* v___x_847_; 
lean_inc(v_target_844_);
v___x_847_ = l_Lake_Workspace_findTargetModule_x3f(v_target_844_, v_ws_843_);
if (lean_obj_tag(v___x_847_) == 1)
{
lean_object* v_val_848_; lean_object* v___x_849_; 
lean_dec(v_target_844_);
v_val_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_val_848_);
lean_dec_ref(v___x_847_);
v___x_849_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_843_, v_val_848_, v_facet_845_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_868_; 
v_a_858_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_868_ == 0)
{
v___x_860_ = v___x_849_;
v_isShared_861_ = v_isSharedCheck_868_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_849_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_868_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_862_ = lean_unsigned_to_nat(1u);
v___x_863_ = lean_mk_empty_array_with_capacity(v___x_862_);
v___x_864_ = lean_array_push(v___x_863_, v_a_858_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_864_);
v___x_866_ = v___x_860_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec(v___x_847_);
lean_dec(v_facet_845_);
v___x_869_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v___x_869_, 0, v_target_844_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace___boxed(lean_object* v_ws_885_, lean_object* v_target_886_, lean_object* v_facet_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(v_ws_885_, v_target_886_, v_facet_887_);
lean_dec_ref(v_ws_885_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(lean_object* v_s_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0));
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___boxed(lean_object* v_s_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v_s_893_);
lean_dec_ref(v_s_893_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(lean_object* v_spec_895_, lean_object* v___x_896_, lean_object* v___x_897_, lean_object* v_a_898_, lean_object* v_b_899_){
_start:
{
lean_object* v_it_901_; lean_object* v_startInclusive_902_; lean_object* v_endExclusive_903_; 
if (lean_obj_tag(v_a_898_) == 0)
{
lean_object* v_currPos_907_; lean_object* v_searcher_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_934_; 
v_currPos_907_ = lean_ctor_get(v_a_898_, 0);
v_searcher_908_ = lean_ctor_get(v_a_898_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_898_);
if (v_isSharedCheck_934_ == 0)
{
v___x_910_ = v_a_898_;
v_isShared_911_ = v_isSharedCheck_934_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_searcher_908_);
lean_inc(v_currPos_907_);
lean_dec(v_a_898_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_934_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_startInclusive_912_; lean_object* v_endExclusive_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v_startInclusive_912_ = lean_ctor_get(v___x_896_, 1);
v_endExclusive_913_ = lean_ctor_get(v___x_896_, 2);
v___x_914_ = lean_nat_sub(v_endExclusive_913_, v_startInclusive_912_);
v___x_915_ = lean_nat_dec_eq(v_searcher_908_, v___x_914_);
lean_dec(v___x_914_);
if (v___x_915_ == 0)
{
uint32_t v___x_916_; uint32_t v___x_917_; uint8_t v___x_918_; 
v___x_916_ = 47;
v___x_917_ = lean_string_utf8_get_fast(v_spec_895_, v_searcher_908_);
v___x_918_ = lean_uint32_dec_eq(v___x_917_, v___x_916_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = lean_string_utf8_next_fast(v_spec_895_, v_searcher_908_);
lean_dec(v_searcher_908_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 1, v___x_919_);
v___x_921_ = v___x_910_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_currPos_907_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___x_919_);
v___x_921_ = v_reuseFailAlloc_923_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
v_a_898_ = v___x_921_;
goto _start;
}
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_slice_927_; lean_object* v_nextIt_929_; 
v___x_924_ = lean_string_utf8_next_fast(v_spec_895_, v_searcher_908_);
v___x_925_ = lean_nat_sub(v___x_924_, v_searcher_908_);
v___x_926_ = lean_nat_add(v_searcher_908_, v___x_925_);
lean_dec(v___x_925_);
v_slice_927_ = l_String_Slice_subslice_x21(v___x_896_, v_currPos_907_, v_searcher_908_);
lean_inc(v___x_926_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 1, v___x_926_);
lean_ctor_set(v___x_910_, 0, v___x_926_);
v_nextIt_929_ = v___x_910_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_926_);
v_nextIt_929_ = v_reuseFailAlloc_932_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v_startInclusive_930_; lean_object* v_endExclusive_931_; 
v_startInclusive_930_ = lean_ctor_get(v_slice_927_, 0);
lean_inc(v_startInclusive_930_);
v_endExclusive_931_ = lean_ctor_get(v_slice_927_, 1);
lean_inc(v_endExclusive_931_);
lean_dec_ref(v_slice_927_);
v_it_901_ = v_nextIt_929_;
v_startInclusive_902_ = v_startInclusive_930_;
v_endExclusive_903_ = v_endExclusive_931_;
goto v___jp_900_;
}
}
}
else
{
lean_object* v___x_933_; 
lean_del_object(v___x_910_);
lean_dec(v_searcher_908_);
v___x_933_ = lean_box(1);
lean_inc(v___x_897_);
v_it_901_ = v___x_933_;
v_startInclusive_902_ = v_currPos_907_;
v_endExclusive_903_ = v___x_897_;
goto v___jp_900_;
}
}
}
else
{
lean_dec(v___x_897_);
lean_dec_ref(v_spec_895_);
return v_b_899_;
}
v___jp_900_:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
lean_inc_ref(v_spec_895_);
v___x_904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_904_, 0, v_spec_895_);
lean_ctor_set(v___x_904_, 1, v_startInclusive_902_);
lean_ctor_set(v___x_904_, 2, v_endExclusive_903_);
v___x_905_ = lean_array_push(v_b_899_, v___x_904_);
v_a_898_ = v_it_901_;
v_b_899_ = v___x_905_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg___boxed(lean_object* v_spec_935_, lean_object* v___x_936_, lean_object* v___x_937_, lean_object* v_a_938_, lean_object* v_b_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_935_, v___x_936_, v___x_937_, v_a_938_, v_b_939_);
lean_dec_ref(v___x_936_);
return v_res_940_;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_945_ = lean_string_utf8_byte_size(v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(lean_object* v_ws_946_, lean_object* v_spec_947_, lean_object* v_facet_948_, uint8_t v_isMaybePath_949_, uint8_t v_explicit_950_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = lean_string_utf8_byte_size(v_spec_947_);
lean_inc_ref_n(v_spec_947_, 2);
v___x_959_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_959_, 0, v_spec_947_);
lean_ctor_set(v___x_959_, 1, v___x_957_);
lean_ctor_set(v___x_959_, 2, v___x_958_);
v___x_960_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v___x_959_);
v___x_961_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0));
v___x_962_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_947_, v___x_959_, v___x_958_, v___x_960_, v___x_961_);
lean_dec_ref(v___x_959_);
v___x_963_ = lean_array_to_list(v___x_962_);
if (lean_obj_tag(v___x_963_) == 1)
{
lean_object* v_tail_964_; 
v_tail_964_ = lean_ctor_get(v___x_963_, 1);
lean_inc(v_tail_964_);
if (lean_obj_tag(v_tail_964_) == 0)
{
lean_object* v_head_965_; lean_object* v_str_966_; lean_object* v_startInclusive_967_; lean_object* v_endExclusive_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
lean_dec_ref(v_spec_947_);
v_head_965_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_head_965_);
lean_dec_ref(v___x_963_);
v_str_966_ = lean_ctor_get(v_head_965_, 0);
lean_inc_ref(v_str_966_);
v_startInclusive_967_ = lean_ctor_get(v_head_965_, 1);
lean_inc(v_startInclusive_967_);
v_endExclusive_968_ = lean_ctor_get(v_head_965_, 2);
lean_inc(v_endExclusive_968_);
lean_dec(v_head_965_);
v___x_969_ = lean_nat_sub(v_endExclusive_968_, v_startInclusive_967_);
v___x_970_ = lean_nat_dec_eq(v___x_969_, v___x_957_);
lean_dec(v___x_969_);
if (v___x_970_ == 0)
{
if (v_explicit_950_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = lean_string_utf8_extract(v_str_966_, v_startInclusive_967_, v_endExclusive_968_);
lean_dec(v_endExclusive_968_);
lean_dec(v_startInclusive_967_);
lean_dec_ref(v_str_966_);
v___x_972_ = l_Lake_stringToLegalOrSimpleName(v___x_971_);
v___x_973_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(v_ws_946_, v___x_972_, v_facet_948_);
lean_dec_ref(v_ws_946_);
return v___x_973_;
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_string_utf8_extract(v_str_966_, v_startInclusive_967_, v_endExclusive_968_);
lean_dec(v_endExclusive_968_);
lean_dec(v_startInclusive_967_);
lean_dec_ref(v_str_966_);
v___x_975_ = l_Lake_parsePackageSpec(v_ws_946_, v___x_974_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_facet_948_);
lean_dec_ref(v_ws_946_);
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_985_; 
v_a_984_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_984_);
lean_dec_ref(v___x_975_);
v___x_985_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_946_, v_a_984_, v_facet_948_);
lean_dec_ref(v_ws_946_);
return v___x_985_;
}
}
}
else
{
lean_object* v_root_986_; lean_object* v___x_987_; 
lean_dec(v_endExclusive_968_);
lean_dec(v_startInclusive_967_);
lean_dec_ref(v_str_966_);
v_root_986_ = lean_ctor_get(v_ws_946_, 0);
lean_inc_ref(v_root_986_);
v___x_987_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_946_, v_root_986_, v_facet_948_);
lean_dec_ref(v_ws_946_);
return v___x_987_;
}
}
else
{
lean_object* v_tail_988_; 
v_tail_988_ = lean_ctor_get(v_tail_964_, 1);
if (lean_obj_tag(v_tail_988_) == 0)
{
lean_object* v_head_989_; lean_object* v_head_990_; lean_object* v_str_991_; lean_object* v_startInclusive_992_; lean_object* v_endExclusive_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec_ref(v_spec_947_);
v_head_989_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_head_989_);
lean_dec_ref(v___x_963_);
v_head_990_ = lean_ctor_get(v_tail_964_, 0);
lean_inc(v_head_990_);
lean_dec_ref(v_tail_964_);
v_str_991_ = lean_ctor_get(v_head_989_, 0);
lean_inc_ref(v_str_991_);
v_startInclusive_992_ = lean_ctor_get(v_head_989_, 1);
lean_inc(v_startInclusive_992_);
v_endExclusive_993_ = lean_ctor_get(v_head_989_, 2);
lean_inc(v_endExclusive_993_);
lean_dec(v_head_989_);
v___x_994_ = lean_string_utf8_extract(v_str_991_, v_startInclusive_992_, v_endExclusive_993_);
lean_dec(v_endExclusive_993_);
lean_dec(v_startInclusive_992_);
lean_dec_ref(v_str_991_);
v___x_995_ = l_Lake_parsePackageSpec(v_ws_946_, v___x_994_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_head_990_);
lean_dec(v_facet_948_);
lean_dec_ref(v_ws_946_);
v_a_996_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1053_; 
v_a_1004_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1006_ = v___x_995_;
v_isShared_1007_ = v_isSharedCheck_1053_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_995_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1053_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_str_1008_; lean_object* v_startInclusive_1009_; lean_object* v_endExclusive_1010_; uint8_t v___y_1012_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v_str_1008_ = lean_ctor_get(v_head_990_, 0);
lean_inc_ref(v_str_1008_);
v_startInclusive_1009_ = lean_ctor_get(v_head_990_, 1);
lean_inc(v_startInclusive_1009_);
v_endExclusive_1010_ = lean_ctor_get(v_head_990_, 2);
lean_inc(v_endExclusive_1010_);
v___x_1046_ = lean_nat_sub(v_endExclusive_1010_, v_startInclusive_1009_);
v___x_1047_ = lean_nat_dec_eq(v___x_1046_, v___x_957_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1048_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_1049_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2, &l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2);
v___x_1050_ = lean_nat_dec_le(v___x_1049_, v___x_1046_);
lean_dec(v___x_1046_);
if (v___x_1050_ == 0)
{
v___y_1012_ = v___x_1047_;
goto v___jp_1011_;
}
else
{
uint8_t v___x_1051_; 
v___x_1051_ = lean_string_memcmp(v_str_1008_, v___x_1048_, v_startInclusive_1009_, v___x_957_, v___x_1049_);
v___y_1012_ = v___x_1051_;
goto v___jp_1011_;
}
}
else
{
lean_object* v___x_1052_; 
lean_dec(v___x_1046_);
lean_dec(v_endExclusive_1010_);
lean_dec(v_startInclusive_1009_);
lean_dec_ref(v_str_1008_);
lean_del_object(v___x_1006_);
lean_dec(v_head_990_);
v___x_1052_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_946_, v_a_1004_, v_facet_948_);
lean_dec_ref(v_ws_946_);
return v___x_1052_;
}
v___jp_1011_:
{
if (v___y_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_del_object(v___x_1006_);
lean_dec(v_head_990_);
v___x_1013_ = lean_string_utf8_extract(v_str_1008_, v_startInclusive_1009_, v_endExclusive_1010_);
lean_dec(v_endExclusive_1010_);
lean_dec(v_startInclusive_1009_);
lean_dec_ref(v_str_1008_);
v___x_1014_ = l_Lake_stringToLegalOrSimpleName(v___x_1013_);
v___x_1015_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_946_, v_a_1004_, v___x_1014_, v_facet_948_);
lean_dec_ref(v_ws_946_);
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = l_String_Slice_Pos_nextn(v_head_990_, v___x_957_, v___x_1016_);
lean_dec(v_head_990_);
v___x_1018_ = lean_nat_add(v_startInclusive_1009_, v___x_1017_);
lean_dec(v___x_1017_);
lean_dec(v_startInclusive_1009_);
v___x_1019_ = lean_string_utf8_extract(v_str_1008_, v___x_1018_, v_endExclusive_1010_);
lean_dec(v_endExclusive_1010_);
lean_dec(v___x_1018_);
lean_dec_ref(v_str_1008_);
v___x_1020_ = l_String_toName(v___x_1019_);
lean_inc(v___x_1020_);
v___x_1021_ = l_Lake_Package_findTargetModule_x3f(v___x_1020_, v_a_1004_);
if (lean_obj_tag(v___x_1021_) == 1)
{
lean_object* v_val_1022_; lean_object* v___x_1023_; 
lean_dec(v___x_1020_);
lean_del_object(v___x_1006_);
v_val_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_val_1022_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_946_, v_val_1022_, v_facet_948_);
lean_dec_ref(v_ws_946_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1041_; 
v_a_1032_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1034_ = v___x_1023_;
v_isShared_1035_ = v_isSharedCheck_1041_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1023_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1041_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1036_ = lean_mk_empty_array_with_capacity(v___x_1016_);
v___x_1037_ = lean_array_push(v___x_1036_, v_a_1032_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1037_);
v___x_1039_ = v___x_1034_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_dec(v___x_1021_);
lean_dec(v_facet_948_);
lean_dec_ref(v_ws_946_);
v___x_1042_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1020_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set_tag(v___x_1006_, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1042_);
v___x_1044_ = v___x_1006_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_tail_964_);
lean_dec_ref(v___x_963_);
lean_dec(v_facet_948_);
lean_dec_ref(v_ws_946_);
goto v___jp_951_;
}
}
}
else
{
lean_dec(v___x_963_);
lean_dec(v_facet_948_);
lean_dec_ref(v_ws_946_);
goto v___jp_951_;
}
v___jp_951_:
{
if (v_isMaybePath_949_ == 0)
{
uint32_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = 47;
v___x_953_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_953_, 0, v_spec_947_);
lean_ctor_set_uint32(v___x_953_, sizeof(void*)*1, v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_955_, 0, v_spec_947_);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___boxed(lean_object* v_ws_1054_, lean_object* v_spec_1055_, lean_object* v_facet_1056_, lean_object* v_isMaybePath_1057_, lean_object* v_explicit_1058_){
_start:
{
uint8_t v_isMaybePath_boxed_1059_; uint8_t v_explicit_boxed_1060_; lean_object* v_res_1061_; 
v_isMaybePath_boxed_1059_ = lean_unbox(v_isMaybePath_1057_);
v_explicit_boxed_1060_ = lean_unbox(v_explicit_1058_);
v_res_1061_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1054_, v_spec_1055_, v_facet_1056_, v_isMaybePath_boxed_1059_, v_explicit_boxed_1060_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(lean_object* v_spec_1062_, lean_object* v___x_1063_, lean_object* v___x_1064_, lean_object* v_inst_1065_, lean_object* v_R_1066_, lean_object* v_a_1067_, lean_object* v_b_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_1062_, v___x_1063_, v___x_1064_, v_a_1067_, v_b_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___boxed(lean_object* v_spec_1070_, lean_object* v___x_1071_, lean_object* v___x_1072_, lean_object* v_inst_1073_, lean_object* v_R_1074_, lean_object* v_a_1075_, lean_object* v_b_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(v_spec_1070_, v___x_1071_, v___x_1072_, v_inst_1073_, v_R_1074_, v_a_1075_, v_b_1076_);
lean_dec_ref(v___x_1071_);
return v_res_1077_;
}
}
static lean_object* _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1080_ = lean_string_utf8_byte_size(v___x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(lean_object* v_ws_1081_, lean_object* v_spec_1082_, lean_object* v_facet_1083_){
_start:
{
uint8_t v___y_1086_; uint8_t v___y_1087_; uint8_t v___y_1167_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1203_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1204_ = lean_string_utf8_byte_size(v_spec_1082_);
v___x_1205_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1, &l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1);
v___x_1206_ = lean_nat_dec_le(v___x_1205_, v___x_1204_);
if (v___x_1206_ == 0)
{
v___y_1167_ = v___x_1206_;
goto v___jp_1166_;
}
else
{
lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_string_memcmp(v_spec_1082_, v___x_1203_, v___x_1207_, v___x_1207_, v___x_1205_);
if (v___x_1208_ == 0)
{
v___y_1167_ = v___x_1208_;
goto v___jp_1166_;
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1209_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_spec_1082_);
v___x_1210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1210_, 0, v_spec_1082_);
lean_ctor_set(v___x_1210_, 1, v___x_1207_);
lean_ctor_set(v___x_1210_, 2, v___x_1204_);
v___x_1211_ = l_String_Slice_Pos_nextn(v___x_1210_, v___x_1207_, v___x_1209_);
lean_dec_ref(v___x_1210_);
v___x_1212_ = lean_string_utf8_extract(v_spec_1082_, v___x_1211_, v___x_1204_);
lean_dec(v___x_1211_);
lean_dec_ref(v_spec_1082_);
v___x_1213_ = 0;
v___x_1214_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1081_, v___x_1212_, v_facet_1083_, v___x_1213_, v___x_1208_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set_tag(v___x_1217_, 1);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
v_a_1223_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1214_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1214_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set_tag(v___x_1225_, 0);
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
v___jp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
lean_inc_ref(v_spec_1082_);
v___x_1088_ = l_Lake_resolvePath(v_spec_1082_);
v___x_1089_ = lean_string_utf8_byte_size(v___x_1088_);
v___x_1090_ = lean_unsigned_to_nat(0u);
v___x_1091_ = lean_nat_dec_eq(v___x_1089_, v___x_1090_);
if (v___x_1091_ == 0)
{
uint8_t v___x_1092_; 
v___x_1092_ = l_System_FilePath_isDir(v___x_1088_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lake_Workspace_findModuleBySrc_x3f(v___x_1088_, v_ws_1081_);
if (lean_obj_tag(v___x_1093_) == 1)
{
lean_object* v_val_1094_; lean_object* v___x_1095_; 
lean_dec_ref(v_spec_1082_);
v_val_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_val_1094_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_1081_, v_val_1094_, v_facet_1083_);
lean_dec_ref(v_ws_1081_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1095_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set_tag(v___x_1098_, 1);
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1114_; 
v_a_1104_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1106_ = v___x_1095_;
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1095_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1108_ = lean_unsigned_to_nat(1u);
v___x_1109_ = lean_mk_empty_array_with_capacity(v___x_1108_);
v___x_1110_ = lean_array_push(v___x_1109_, v_a_1104_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set_tag(v___x_1106_, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1110_);
v___x_1112_ = v___x_1106_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_object* v___x_1115_; 
lean_dec(v___x_1093_);
v___x_1115_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1081_, v_spec_1082_, v_facet_1083_, v___y_1086_, v___x_1092_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 1);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
v_a_1124_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1115_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1115_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set_tag(v___x_1126_, 0);
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
else
{
lean_object* v___x_1132_; 
lean_dec_ref(v___x_1088_);
v___x_1132_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1081_, v_spec_1082_, v_facet_1083_, v___y_1087_, v___y_1087_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 1);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_a_1141_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1132_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1132_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 0);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
else
{
lean_object* v___x_1149_; 
lean_dec_ref(v___x_1088_);
v___x_1149_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1081_, v_spec_1082_, v_facet_1083_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 1);
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v_a_1158_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1149_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1149_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set_tag(v___x_1160_, 0);
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
v___jp_1166_:
{
uint8_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1168_ = 1;
v___x_1169_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_1170_ = lean_string_utf8_byte_size(v_spec_1082_);
v___x_1171_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2, &l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2);
v___x_1172_ = lean_nat_dec_le(v___x_1171_, v___x_1170_);
if (v___x_1172_ == 0)
{
v___y_1086_ = v___x_1168_;
v___y_1087_ = v___y_1167_;
goto v___jp_1085_;
}
else
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_string_memcmp(v_spec_1082_, v___x_1169_, v___x_1173_, v___x_1173_, v___x_1171_);
if (v___x_1174_ == 0)
{
v___y_1086_ = v___x_1168_;
v___y_1087_ = v___x_1174_;
goto v___jp_1085_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v_mod_1179_; lean_object* v___x_1180_; 
v___x_1175_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_spec_1082_);
v___x_1176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1176_, 0, v_spec_1082_);
lean_ctor_set(v___x_1176_, 1, v___x_1173_);
lean_ctor_set(v___x_1176_, 2, v___x_1170_);
v___x_1177_ = l_String_Slice_Pos_nextn(v___x_1176_, v___x_1173_, v___x_1175_);
lean_dec_ref(v___x_1176_);
v___x_1178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1178_, 0, v_spec_1082_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
lean_ctor_set(v___x_1178_, 2, v___x_1170_);
v_mod_1179_ = l_String_Slice_toName(v___x_1178_);
lean_dec_ref(v___x_1178_);
lean_inc(v_mod_1179_);
v___x_1180_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_1179_, v_ws_1081_);
if (lean_obj_tag(v___x_1180_) == 1)
{
lean_object* v_val_1181_; lean_object* v___x_1182_; 
lean_dec(v_mod_1179_);
v_val_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_val_1181_);
lean_dec_ref(v___x_1180_);
v___x_1182_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_1081_, v_val_1181_, v_facet_1083_);
lean_dec_ref(v_ws_1081_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set_tag(v___x_1185_, 1);
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1200_; 
v_a_1191_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1193_ = v___x_1182_;
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1182_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1195_ = lean_mk_empty_array_with_capacity(v___x_1175_);
v___x_1196_ = lean_array_push(v___x_1195_, v_a_1191_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set_tag(v___x_1193_, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1196_);
v___x_1198_ = v___x_1193_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec(v___x_1180_);
lean_dec(v_facet_1083_);
lean_dec_ref(v_ws_1081_);
v___x_1201_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1201_, 0, v_mod_1179_);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___boxed(lean_object* v_ws_1231_, lean_object* v_spec_1232_, lean_object* v_facet_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1231_, v_spec_1232_, v_facet_1233_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object* v_ws_1236_, lean_object* v_spec_1237_){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1245_ = lean_unsigned_to_nat(0u);
v___x_1246_ = lean_string_utf8_byte_size(v_spec_1237_);
lean_inc_ref_n(v_spec_1237_, 2);
v___x_1247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1247_, 0, v_spec_1237_);
lean_ctor_set(v___x_1247_, 1, v___x_1245_);
lean_ctor_set(v___x_1247_, 2, v___x_1246_);
v___x_1248_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v___x_1247_);
v___x_1249_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0));
v___x_1250_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_1237_, v___x_1247_, v___x_1246_, v___x_1248_, v___x_1249_);
lean_dec_ref(v___x_1247_);
v___x_1251_ = lean_array_to_list(v___x_1250_);
if (lean_obj_tag(v___x_1251_) == 1)
{
lean_object* v_tail_1252_; 
v_tail_1252_ = lean_ctor_get(v___x_1251_, 1);
lean_inc(v_tail_1252_);
if (lean_obj_tag(v_tail_1252_) == 0)
{
lean_object* v_head_1253_; lean_object* v_str_1254_; lean_object* v_startInclusive_1255_; lean_object* v_endExclusive_1256_; lean_object* v___x_1257_; lean_object* v_targetName_1258_; lean_object* v___x_1259_; 
v_head_1253_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_head_1253_);
lean_dec_ref(v___x_1251_);
v_str_1254_ = lean_ctor_get(v_head_1253_, 0);
lean_inc_ref(v_str_1254_);
v_startInclusive_1255_ = lean_ctor_get(v_head_1253_, 1);
lean_inc(v_startInclusive_1255_);
v_endExclusive_1256_ = lean_ctor_get(v_head_1253_, 2);
lean_inc(v_endExclusive_1256_);
lean_dec(v_head_1253_);
v___x_1257_ = lean_string_utf8_extract(v_str_1254_, v_startInclusive_1255_, v_endExclusive_1256_);
lean_dec(v_endExclusive_1256_);
lean_dec(v_startInclusive_1255_);
lean_dec_ref(v_str_1254_);
v_targetName_1258_ = l_Lake_stringToLegalOrSimpleName(v___x_1257_);
v___x_1259_ = l_Lake_Workspace_findLeanExe_x3f(v_targetName_1258_, v_ws_1236_);
lean_dec(v_targetName_1258_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_1260_, 0, v_spec_1237_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
else
{
lean_object* v_val_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v_spec_1237_);
v_val_1262_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1259_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_val_1262_);
lean_dec(v___x_1259_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_val_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_object* v_head_1270_; lean_object* v_head_1271_; lean_object* v_tail_1272_; lean_object* v_str_1274_; lean_object* v_startInclusive_1275_; lean_object* v_endExclusive_1276_; 
v_head_1270_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_head_1270_);
lean_dec_ref(v___x_1251_);
v_head_1271_ = lean_ctor_get(v_tail_1252_, 0);
lean_inc(v_head_1271_);
v_tail_1272_ = lean_ctor_get(v_tail_1252_, 1);
lean_inc(v_tail_1272_);
lean_dec_ref(v_tail_1252_);
if (lean_obj_tag(v_tail_1272_) == 0)
{
lean_object* v_str_1314_; lean_object* v_startInclusive_1315_; lean_object* v_endExclusive_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v_str_1314_ = lean_ctor_get(v_head_1270_, 0);
lean_inc_ref(v_str_1314_);
v_startInclusive_1315_ = lean_ctor_get(v_head_1270_, 1);
lean_inc(v_startInclusive_1315_);
v_endExclusive_1316_ = lean_ctor_get(v_head_1270_, 2);
lean_inc(v_endExclusive_1316_);
v___x_1317_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1318_ = lean_obj_once(&l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1, &l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once, _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1);
v___x_1319_ = lean_nat_sub(v_endExclusive_1316_, v_startInclusive_1315_);
v___x_1320_ = lean_nat_dec_le(v___x_1318_, v___x_1319_);
lean_dec(v___x_1319_);
if (v___x_1320_ == 0)
{
lean_dec(v_head_1270_);
v_str_1274_ = v_str_1314_;
v_startInclusive_1275_ = v_startInclusive_1315_;
v_endExclusive_1276_ = v_endExclusive_1316_;
goto v___jp_1273_;
}
else
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_string_memcmp(v_str_1314_, v___x_1317_, v_startInclusive_1315_, v___x_1245_, v___x_1318_);
if (v___x_1321_ == 0)
{
lean_dec(v_head_1270_);
v_str_1274_ = v_str_1314_;
v_startInclusive_1275_ = v_startInclusive_1315_;
v_endExclusive_1276_ = v_endExclusive_1316_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = lean_unsigned_to_nat(1u);
v___x_1323_ = l_String_Slice_Pos_nextn(v_head_1270_, v___x_1245_, v___x_1322_);
lean_dec(v_head_1270_);
v___x_1324_ = lean_nat_add(v_startInclusive_1315_, v___x_1323_);
lean_dec(v___x_1323_);
lean_dec(v_startInclusive_1315_);
v_str_1274_ = v_str_1314_;
v_startInclusive_1275_ = v___x_1324_;
v_endExclusive_1276_ = v_endExclusive_1316_;
goto v___jp_1273_;
}
}
}
else
{
lean_dec(v_tail_1272_);
lean_dec(v_head_1271_);
lean_dec(v_head_1270_);
goto v___jp_1241_;
}
v___jp_1273_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_string_utf8_extract(v_str_1274_, v_startInclusive_1275_, v_endExclusive_1276_);
lean_dec(v_endExclusive_1276_);
lean_dec(v_startInclusive_1275_);
lean_dec_ref(v_str_1274_);
v___x_1278_ = l_Lake_parsePackageSpec(v_ws_1236_, v___x_1277_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec(v_head_1271_);
lean_dec_ref(v_spec_1237_);
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1313_; 
v_a_1287_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1289_ = v___x_1278_;
v_isShared_1290_ = v_isSharedCheck_1313_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1278_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1313_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v_str_1291_; lean_object* v_startInclusive_1292_; lean_object* v_endExclusive_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1312_; 
v_str_1291_ = lean_ctor_get(v_head_1271_, 0);
v_startInclusive_1292_ = lean_ctor_get(v_head_1271_, 1);
v_endExclusive_1293_ = lean_ctor_get(v_head_1271_, 2);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_head_1271_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1295_ = v_head_1271_;
v_isShared_1296_ = v_isSharedCheck_1312_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_endExclusive_1293_);
lean_inc(v_startInclusive_1292_);
lean_inc(v_str_1291_);
lean_dec(v_head_1271_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1312_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = lean_string_utf8_extract(v_str_1291_, v_startInclusive_1292_, v_endExclusive_1293_);
lean_dec(v_endExclusive_1293_);
lean_dec(v_startInclusive_1292_);
lean_dec_ref(v_str_1291_);
v___x_1298_ = l_Lake_stringToLegalOrSimpleName(v___x_1297_);
v___x_1299_ = l_Lake_Package_findTargetDecl_x3f(v___x_1298_, v_a_1287_);
lean_dec(v___x_1298_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_del_object(v___x_1295_);
lean_del_object(v___x_1289_);
lean_dec(v_a_1287_);
goto v___jp_1238_;
}
else
{
lean_object* v_val_1300_; lean_object* v_name_1301_; lean_object* v_kind_1302_; lean_object* v_config_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_val_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_val_1300_);
lean_dec_ref(v___x_1299_);
v_name_1301_ = lean_ctor_get(v_val_1300_, 1);
lean_inc(v_name_1301_);
v_kind_1302_ = lean_ctor_get(v_val_1300_, 2);
lean_inc(v_kind_1302_);
v_config_1303_ = lean_ctor_get(v_val_1300_, 3);
lean_inc(v_config_1303_);
lean_dec(v_val_1300_);
v___x_1304_ = l_Lake_LeanExe_keyword;
v___x_1305_ = lean_name_eq(v_kind_1302_, v___x_1304_);
lean_dec(v_kind_1302_);
if (v___x_1305_ == 0)
{
lean_dec(v_config_1303_);
lean_dec(v_name_1301_);
lean_del_object(v___x_1295_);
lean_del_object(v___x_1289_);
lean_dec(v_a_1287_);
goto v___jp_1238_;
}
else
{
lean_object* v___x_1307_; 
lean_dec_ref(v_spec_1237_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 2, v_config_1303_);
lean_ctor_set(v___x_1295_, 1, v_name_1301_);
lean_ctor_set(v___x_1295_, 0, v_a_1287_);
v___x_1307_ = v___x_1295_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1287_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_name_1301_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v_config_1303_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1307_);
v___x_1309_ = v___x_1289_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
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
lean_dec(v___x_1251_);
goto v___jp_1241_;
}
v___jp_1238_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_1239_, 0, v_spec_1237_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
v___jp_1241_:
{
uint32_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = 47;
v___x_1243_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_1243_, 0, v_spec_1237_);
lean_ctor_set_uint32(v___x_1243_, sizeof(void*)*1, v___x_1242_);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed(lean_object* v_ws_1325_, lean_object* v_spec_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lake_parseExeTargetSpec(v_ws_1325_, v_spec_1326_);
lean_dec_ref(v_ws_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(lean_object* v_s_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0));
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___boxed(lean_object* v_s_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(v_s_1330_);
lean_dec_ref(v_s_1330_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(lean_object* v_spec_1332_, lean_object* v___x_1333_, lean_object* v___x_1334_, lean_object* v_a_1335_, lean_object* v_b_1336_){
_start:
{
lean_object* v_it_1338_; lean_object* v_startInclusive_1339_; lean_object* v_endExclusive_1340_; 
if (lean_obj_tag(v_a_1335_) == 0)
{
lean_object* v_currPos_1345_; lean_object* v_searcher_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1372_; 
v_currPos_1345_ = lean_ctor_get(v_a_1335_, 0);
v_searcher_1346_ = lean_ctor_get(v_a_1335_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_a_1335_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1348_ = v_a_1335_;
v_isShared_1349_ = v_isSharedCheck_1372_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_searcher_1346_);
lean_inc(v_currPos_1345_);
lean_dec(v_a_1335_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1372_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_startInclusive_1350_; lean_object* v_endExclusive_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_startInclusive_1350_ = lean_ctor_get(v___x_1333_, 1);
v_endExclusive_1351_ = lean_ctor_get(v___x_1333_, 2);
v___x_1352_ = lean_nat_sub(v_endExclusive_1351_, v_startInclusive_1350_);
v___x_1353_ = lean_nat_dec_eq(v_searcher_1346_, v___x_1352_);
lean_dec(v___x_1352_);
if (v___x_1353_ == 0)
{
uint32_t v___x_1354_; uint32_t v___x_1355_; uint8_t v___x_1356_; 
v___x_1354_ = 58;
v___x_1355_ = lean_string_utf8_get_fast(v_spec_1332_, v_searcher_1346_);
v___x_1356_ = lean_uint32_dec_eq(v___x_1355_, v___x_1354_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_string_utf8_next_fast(v_spec_1332_, v_searcher_1346_);
lean_dec(v_searcher_1346_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v___x_1357_);
v___x_1359_ = v___x_1348_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_currPos_1345_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
v_a_1335_ = v___x_1359_;
goto _start;
}
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_slice_1365_; lean_object* v_nextIt_1367_; 
v___x_1362_ = lean_string_utf8_next_fast(v_spec_1332_, v_searcher_1346_);
v___x_1363_ = lean_nat_sub(v___x_1362_, v_searcher_1346_);
v___x_1364_ = lean_nat_add(v_searcher_1346_, v___x_1363_);
lean_dec(v___x_1363_);
v_slice_1365_ = l_String_Slice_subslice_x21(v___x_1333_, v_currPos_1345_, v_searcher_1346_);
lean_inc(v___x_1364_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v___x_1364_);
lean_ctor_set(v___x_1348_, 0, v___x_1364_);
v_nextIt_1367_ = v___x_1348_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___x_1364_);
v_nextIt_1367_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v_startInclusive_1368_; lean_object* v_endExclusive_1369_; 
v_startInclusive_1368_ = lean_ctor_get(v_slice_1365_, 0);
lean_inc(v_startInclusive_1368_);
v_endExclusive_1369_ = lean_ctor_get(v_slice_1365_, 1);
lean_inc(v_endExclusive_1369_);
lean_dec_ref(v_slice_1365_);
v_it_1338_ = v_nextIt_1367_;
v_startInclusive_1339_ = v_startInclusive_1368_;
v_endExclusive_1340_ = v_endExclusive_1369_;
goto v___jp_1337_;
}
}
}
else
{
lean_object* v___x_1371_; 
lean_del_object(v___x_1348_);
lean_dec(v_searcher_1346_);
v___x_1371_ = lean_box(1);
lean_inc(v___x_1334_);
v_it_1338_ = v___x_1371_;
v_startInclusive_1339_ = v_currPos_1345_;
v_endExclusive_1340_ = v___x_1334_;
goto v___jp_1337_;
}
}
}
else
{
lean_dec(v___x_1334_);
lean_dec_ref(v_spec_1332_);
return v_b_1336_;
}
v___jp_1337_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_inc_ref(v_spec_1332_);
v___x_1341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1341_, 0, v_spec_1332_);
lean_ctor_set(v___x_1341_, 1, v_startInclusive_1339_);
lean_ctor_set(v___x_1341_, 2, v_endExclusive_1340_);
v___x_1342_ = l_String_Slice_toString(v___x_1341_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = lean_array_push(v_b_1336_, v___x_1342_);
v_a_1335_ = v_it_1338_;
v_b_1336_ = v___x_1343_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg___boxed(lean_object* v_spec_1373_, lean_object* v___x_1374_, lean_object* v___x_1375_, lean_object* v_a_1376_, lean_object* v_b_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1373_, v___x_1374_, v___x_1375_, v_a_1376_, v_b_1377_);
lean_dec_ref(v___x_1374_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec(lean_object* v_ws_1381_, lean_object* v_spec_1382_){
_start:
{
uint32_t v___x_1384_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1384_ = 58;
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = lean_string_utf8_byte_size(v_spec_1382_);
lean_inc_ref_n(v_spec_1382_, 2);
v___x_1390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1390_, 0, v_spec_1382_);
lean_ctor_set(v___x_1390_, 1, v___x_1388_);
lean_ctor_set(v___x_1390_, 2, v___x_1389_);
v___x_1391_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Lake_parseTargetSpec___closed__0));
v___x_1393_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1382_, v___x_1390_, v___x_1389_, v___x_1391_, v___x_1392_);
lean_dec_ref(v___x_1390_);
v___x_1394_ = lean_array_to_list(v___x_1393_);
if (lean_obj_tag(v___x_1394_) == 1)
{
lean_object* v_tail_1395_; 
v_tail_1395_ = lean_ctor_get(v___x_1394_, 1);
lean_inc(v_tail_1395_);
if (lean_obj_tag(v_tail_1395_) == 0)
{
lean_object* v_head_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec_ref(v_spec_1382_);
v_head_1396_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_head_1396_);
lean_dec_ref(v___x_1394_);
v___x_1397_ = lean_box(0);
v___x_1398_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1381_, v_head_1396_, v___x_1397_);
return v___x_1398_;
}
else
{
lean_object* v_tail_1399_; 
v_tail_1399_ = lean_ctor_get(v_tail_1395_, 1);
if (lean_obj_tag(v_tail_1399_) == 0)
{
lean_object* v_head_1400_; lean_object* v_head_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_dec_ref(v_spec_1382_);
v_head_1400_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_head_1400_);
lean_dec_ref(v___x_1394_);
v_head_1401_ = lean_ctor_get(v_tail_1395_, 0);
lean_inc(v_head_1401_);
lean_dec_ref(v_tail_1395_);
v___x_1402_ = l_String_toName(v_head_1401_);
v___x_1403_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1381_, v_head_1400_, v___x_1402_);
return v___x_1403_;
}
else
{
lean_dec_ref(v_tail_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v_ws_1381_);
goto v___jp_1385_;
}
}
}
else
{
lean_dec(v___x_1394_);
lean_dec_ref(v_ws_1381_);
goto v___jp_1385_;
}
v___jp_1385_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_1386_, 0, v_spec_1382_);
lean_ctor_set_uint32(v___x_1386_, sizeof(void*)*1, v___x_1384_);
v___x_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec___boxed(lean_object* v_ws_1404_, lean_object* v_spec_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lake_parseTargetSpec(v_ws_1404_, v_spec_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(lean_object* v_spec_1408_, lean_object* v___x_1409_, lean_object* v___x_1410_, lean_object* v_inst_1411_, lean_object* v_R_1412_, lean_object* v_a_1413_, lean_object* v_b_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1408_, v___x_1409_, v___x_1410_, v_a_1413_, v_b_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___boxed(lean_object* v_spec_1416_, lean_object* v___x_1417_, lean_object* v___x_1418_, lean_object* v_inst_1419_, lean_object* v_R_1420_, lean_object* v_a_1421_, lean_object* v_b_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(v_spec_1416_, v___x_1417_, v___x_1418_, v_inst_1419_, v_R_1420_, v_a_1421_, v_b_1422_);
lean_dec_ref(v___x_1417_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(lean_object* v_ws_1424_, lean_object* v_as_x27_1425_, lean_object* v_b_1426_){
_start:
{
if (lean_obj_tag(v_as_x27_1425_) == 0)
{
lean_object* v___x_1428_; 
lean_dec_ref(v_ws_1424_);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_b_1426_);
return v___x_1428_;
}
else
{
lean_object* v_head_1429_; lean_object* v_tail_1430_; lean_object* v___x_1431_; 
v_head_1429_ = lean_ctor_get(v_as_x27_1425_, 0);
lean_inc(v_head_1429_);
v_tail_1430_ = lean_ctor_get(v_as_x27_1425_, 1);
lean_inc(v_tail_1430_);
lean_dec_ref(v_as_x27_1425_);
lean_inc_ref(v_ws_1424_);
v___x_1431_ = l_Lake_parseTargetSpec(v_ws_1424_, v_head_1429_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref(v___x_1431_);
v___x_1433_ = l_Array_append___redArg(v_b_1426_, v_a_1432_);
lean_dec(v_a_1432_);
v_as_x27_1425_ = v_tail_1430_;
v_b_1426_ = v___x_1433_;
goto _start;
}
else
{
lean_dec(v_tail_1430_);
lean_dec_ref(v_b_1426_);
lean_dec_ref(v_ws_1424_);
return v___x_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg___boxed(lean_object* v_ws_1435_, lean_object* v_as_x27_1436_, lean_object* v_b_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1435_, v_as_x27_1436_, v_b_1437_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs(lean_object* v_ws_1442_, lean_object* v_specs_1443_){
_start:
{
lean_object* v___x_1445_; lean_object* v_results_1446_; lean_object* v___x_1447_; 
v___x_1445_ = lean_unsigned_to_nat(0u);
v_results_1446_ = ((lean_object*)(l_Lake_parseTargetSpecs___closed__0));
lean_inc_ref(v_ws_1442_);
v___x_1447_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1442_, v_specs_1443_, v_results_1446_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
v___x_1449_ = lean_array_get_size(v_a_1448_);
lean_dec(v_a_1448_);
v___x_1450_ = lean_nat_dec_eq(v___x_1449_, v___x_1445_);
if (v___x_1450_ == 0)
{
lean_dec_ref(v_ws_1442_);
return v___x_1447_;
}
else
{
lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1464_; 
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; 
v_unused_1465_ = lean_ctor_get(v___x_1447_, 0);
lean_dec(v_unused_1465_);
v___x_1452_ = v___x_1447_;
v_isShared_1453_ = v_isSharedCheck_1464_;
goto v_resetjp_1451_;
}
else
{
lean_dec(v___x_1447_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1464_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v_root_1454_; lean_object* v___x_1455_; 
v_root_1454_ = lean_ctor_get(v_ws_1442_, 0);
lean_inc_ref(v_root_1454_);
v___x_1455_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_1442_, v_root_1454_);
lean_dec_ref(v_ws_1442_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref(v___x_1455_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set_tag(v___x_1452_, 1);
lean_ctor_set(v___x_1452_, 0, v_a_1456_);
v___x_1458_ = v___x_1452_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; 
v_a_1460_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1460_);
lean_dec_ref(v___x_1455_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v_a_1460_);
v___x_1462_ = v___x_1452_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
else
{
lean_dec_ref(v_ws_1442_);
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___boxed(lean_object* v_ws_1466_, lean_object* v_specs_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lake_parseTargetSpecs(v_ws_1466_, v_specs_1467_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(lean_object* v_ws_1470_, lean_object* v_as_1471_, lean_object* v_as_x27_1472_, lean_object* v_b_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1470_, v_as_x27_1472_, v_b_1473_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___boxed(lean_object* v_ws_1477_, lean_object* v_as_1478_, lean_object* v_as_x27_1479_, lean_object* v_b_1480_, lean_object* v_a_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(v_ws_1477_, v_as_1478_, v_as_x27_1479_, v_b_1480_, v_a_1481_);
lean_dec(v_as_1478_);
return v_res_1483_;
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
