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
extern lean_object* l_Lake_Module_irArtsFacet;
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
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lake_BuildInfo_key(lean_object*);
lean_object* l_Lake_BuildKey_toSimpleString(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0 = (const lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1 = (const lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0 = (const lean_object*)&l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___closed__0;
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
lean_object* l_Lake_BuildSpec_fetch(lean_object* v_self_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
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
lean_object* v_registeredJobs_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; lean_object* v_job_62_; 
v_registeredJobs_57_ = lean_ctor_get(v_a_38_, 4);
v___x_58_ = l_Lake_BuildInfo_key(v_info_41_);
v___x_59_ = l_Lake_BuildKey_toSimpleString(v___x_58_);
v___x_60_ = 0;
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 2, v___x_59_);
v_job_62_ = v___x_49_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_task_45_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_kind_46_);
lean_ctor_set(v_reuseFailAlloc_71_, 2, v___x_59_);
v_job_62_ = v_reuseFailAlloc_71_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_69_; 
lean_ctor_set_uint8(v_job_62_, sizeof(void*)*3, v___x_60_);
v___x_63_ = lean_st_ref_take(v_registeredJobs_57_);
lean_inc_ref(v_job_62_);
v___x_64_ = l_Lake_Job_toOpaque___redArg(v_job_62_);
v___x_65_ = lean_array_push(v___x_63_, v___x_64_);
v___x_66_ = lean_st_ref_put(v_registeredJobs_57_, v___x_65_);
v___x_67_ = l_Lake_Job_renew___redArg(v_job_62_);
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
LEAN_EXPORT void l_Lake_BuildSpec_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_33_ = stack[0].m_obj;
lean_object* v_a_34_ = stack[1].m_obj;
lean_object* v_a_35_ = stack[2].m_obj;
lean_object* v_a_36_ = stack[3].m_obj;
lean_object* v_a_37_ = stack[4].m_obj;
lean_object* v_a_38_ = stack[5].m_obj;
lean_object* v_a_39_ = stack[6].m_obj;
lean_object* v_res_76_;
v_res_76_ = l_Lake_BuildSpec_fetch(v_self_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_fetch___boxed(lean_object* v_self_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lake_BuildSpec_fetch(v_self_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
lean_dec_ref(v_a_82_);
lean_dec(v_a_81_);
lean_dec(v_a_80_);
lean_dec(v_a_79_);
return v_res_85_;
}
}
lean_object* l_Lake_BuildSpec_build(lean_object* v_self_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v_info_99_; lean_object* v___x_100_; 
v_info_99_ = lean_ctor_get(v_self_86_, 0);
lean_inc_ref_n(v_info_99_, 2);
lean_dec_ref(v_self_86_);
lean_inc_ref(v_a_91_);
lean_inc(v_a_90_);
lean_inc(v_a_89_);
lean_inc(v_a_88_);
v___x_100_ = lean_apply_7(v_a_87_, v_info_99_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, lean_box(0));
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v_a_102_; lean_object* v_task_103_; lean_object* v_kind_104_; lean_object* v_caption_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
v_a_102_ = lean_ctor_get(v___x_100_, 1);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_100_, 2);
v_task_103_ = lean_ctor_get(v_a_101_, 0);
v_kind_104_ = lean_ctor_get(v_a_101_, 1);
v_caption_105_ = lean_ctor_get(v_a_101_, 2);
v___x_106_ = lean_string_utf8_byte_size(v_caption_105_);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_nat_dec_eq(v___x_106_, v___x_107_);
if (v___x_108_ == 0)
{
lean_dec_ref(v_info_99_);
v_a_95_ = v_a_101_;
v_a_96_ = v_a_102_;
goto v___jp_94_;
}
else
{
lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_124_; 
lean_inc(v_kind_104_);
lean_inc_ref(v_task_103_);
v_isSharedCheck_124_ = !lean_is_exclusive(v_a_101_);
if (v_isSharedCheck_124_ == 0)
{
lean_object* v_unused_125_; lean_object* v_unused_126_; lean_object* v_unused_127_; 
v_unused_125_ = lean_ctor_get(v_a_101_, 2);
lean_dec(v_unused_125_);
v_unused_126_ = lean_ctor_get(v_a_101_, 1);
lean_dec(v_unused_126_);
v_unused_127_ = lean_ctor_get(v_a_101_, 0);
lean_dec(v_unused_127_);
v___x_110_ = v_a_101_;
v_isShared_111_ = v_isSharedCheck_124_;
goto v_resetjp_109_;
}
else
{
lean_dec(v_a_101_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_124_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v_registeredJobs_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; lean_object* v_job_117_; 
v_registeredJobs_112_ = lean_ctor_get(v_a_91_, 4);
v___x_113_ = l_Lake_BuildInfo_key(v_info_99_);
v___x_114_ = l_Lake_BuildKey_toSimpleString(v___x_113_);
v___x_115_ = 0;
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 2, v___x_114_);
v_job_117_ = v___x_110_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_task_103_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_kind_104_);
lean_ctor_set(v_reuseFailAlloc_123_, 2, v___x_114_);
v_job_117_ = v_reuseFailAlloc_123_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
lean_ctor_set_uint8(v_job_117_, sizeof(void*)*3, v___x_115_);
v___x_118_ = lean_st_ref_take(v_registeredJobs_112_);
lean_inc_ref(v_job_117_);
v___x_119_ = l_Lake_Job_toOpaque___redArg(v_job_117_);
v___x_120_ = lean_array_push(v___x_118_, v___x_119_);
v___x_121_ = lean_st_ref_put(v_registeredJobs_112_, v___x_120_);
v___x_122_ = l_Lake_Job_renew___redArg(v_job_117_);
v_a_95_ = v___x_122_;
v_a_96_ = v_a_102_;
goto v___jp_94_;
}
}
}
}
else
{
lean_dec_ref(v_info_99_);
return v___x_100_;
}
v___jp_94_:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = l_Lake_Job_toOpaque___redArg(v_a_95_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v_a_96_);
return v___x_98_;
}
}
}
LEAN_EXPORT void l_Lake_BuildSpec_build_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_86_ = stack[0].m_obj;
lean_object* v_a_87_ = stack[1].m_obj;
lean_object* v_a_88_ = stack[2].m_obj;
lean_object* v_a_89_ = stack[3].m_obj;
lean_object* v_a_90_ = stack[4].m_obj;
lean_object* v_a_91_ = stack[5].m_obj;
lean_object* v_a_92_ = stack[6].m_obj;
lean_object* v_res_128_;
v_res_128_ = l_Lake_BuildSpec_build(v_self_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_build___boxed(lean_object* v_self_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lake_BuildSpec_build(v_self_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec(v_a_132_);
lean_dec(v_a_131_);
return v_res_137_;
}
}
lean_object* l_Lake_BuildSpec_query___lam__0(lean_object* v_format_138_, uint8_t v_fmt_139_, lean_object* v_x_140_){
_start:
{
if (lean_obj_tag(v_x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_151_; 
v_a_141_ = lean_ctor_get(v_x_140_, 0);
v_a_142_ = lean_ctor_get(v_x_140_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_140_);
if (v_isSharedCheck_151_ == 0)
{
v___x_144_ = v_x_140_;
v_isShared_145_ = v_isSharedCheck_151_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_inc(v_a_141_);
lean_dec(v_x_140_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_151_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_146_ = lean_box(v_fmt_139_);
v___x_147_ = lean_apply_2(v_format_138_, v___x_146_, v_a_141_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_147_);
v___x_149_ = v___x_144_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_a_142_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
else
{
lean_object* v_a_152_; lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
lean_dec_ref(v_format_138_);
v_a_152_ = lean_ctor_get(v_x_140_, 0);
v_a_153_ = lean_ctor_get(v_x_140_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_x_140_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v_x_140_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_inc(v_a_152_);
lean_dec(v_x_140_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_152_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_BuildSpec_query___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_format_138_ = stack[0].m_obj;
uint8_t v_fmt_139_ = stack[1].m_num;
lean_object* v_x_140_ = stack[2].m_obj;
lean_object* v_res_161_;
v_res_161_ = l_Lake_BuildSpec_query___lam__0(v_format_138_, v_fmt_139_, v_x_140_);
stack->m_obj
 = v_res_161_;
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___lam__0___boxed(lean_object* v_format_162_, lean_object* v_fmt_163_, lean_object* v_x_164_){
_start:
{
uint8_t v_fmt_boxed_165_; lean_object* v_res_166_; 
v_fmt_boxed_165_ = lean_unbox(v_fmt_163_);
v_res_166_ = l_Lake_BuildSpec_query___lam__0(v_format_162_, v_fmt_boxed_165_, v_x_164_);
return v_res_166_;
}
}
lean_object* l_Lake_BuildSpec_query(lean_object* v_self_167_, uint8_t v_fmt_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_info_176_; lean_object* v_format_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___f_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_info_176_ = lean_ctor_get(v_self_167_, 0);
lean_inc_ref_n(v_info_176_, 2);
v_format_177_ = lean_ctor_get(v_self_167_, 1);
lean_inc_ref(v_format_177_);
lean_dec_ref(v_self_167_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_box(v_fmt_168_);
v___f_180_ = lean_alloc_closure((void*)(l_Lake_BuildSpec_query___lam__0___boxed), 3, 2);
lean_closure_set(v___f_180_, 0, v_format_177_);
lean_closure_set(v___f_180_, 1, v___x_179_);
v___x_181_ = l_Lake_BuildInfo_key(v_info_176_);
v___x_182_ = l_Lake_BuildKey_toSimpleString(v___x_181_);
lean_inc_ref(v_a_173_);
lean_inc(v_a_172_);
lean_inc(v_a_171_);
lean_inc(v_a_170_);
v___x_183_ = lean_apply_7(v_a_169_, v_info_176_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, lean_box(0));
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_220_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_a_185_ = lean_ctor_get(v___x_183_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_220_ == 0)
{
v___x_187_ = v___x_183_;
v_isShared_188_ = v_isSharedCheck_220_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_220_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_task_189_; lean_object* v_caption_190_; uint8_t v_optional_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_218_; 
v_task_189_ = lean_ctor_get(v_a_184_, 0);
v_caption_190_ = lean_ctor_get(v_a_184_, 2);
v_optional_191_ = lean_ctor_get_uint8(v_a_184_, sizeof(void*)*3);
v_isSharedCheck_218_ = !lean_is_exclusive(v_a_184_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_a_184_, 1);
lean_dec(v_unused_219_);
v___x_193_ = v_a_184_;
v_isShared_194_ = v_isSharedCheck_218_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_caption_190_);
lean_inc(v_task_189_);
lean_dec(v_a_184_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_218_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = 0;
v___x_197_ = lean_task_map(v___f_180_, v_task_189_, v___x_195_, v___x_196_);
v___x_198_ = lean_string_utf8_byte_size(v_caption_190_);
v___x_199_ = lean_nat_dec_eq(v___x_198_, v___x_195_);
if (v___x_199_ == 0)
{
lean_object* v___x_201_; 
lean_dec_ref(v___x_182_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 1, v___x_178_);
lean_ctor_set(v___x_193_, 0, v___x_197_);
v___x_201_ = v___x_193_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_caption_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, sizeof(void*)*3, v_optional_191_);
v___x_201_ = v_reuseFailAlloc_205_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_203_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_201_);
v___x_203_ = v___x_187_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_a_185_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
else
{
lean_object* v_registeredJobs_206_; lean_object* v_job_208_; 
lean_dec_ref(v_caption_190_);
v_registeredJobs_206_ = lean_ctor_get(v_a_173_, 4);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 2, v___x_182_);
lean_ctor_set(v___x_193_, 1, v___x_178_);
lean_ctor_set(v___x_193_, 0, v___x_197_);
v_job_208_ = v___x_193_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v___x_182_);
v_job_208_ = v_reuseFailAlloc_217_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
lean_ctor_set_uint8(v_job_208_, sizeof(void*)*3, v___x_196_);
v___x_209_ = lean_st_ref_take(v_registeredJobs_206_);
lean_inc_ref(v_job_208_);
v___x_210_ = l_Lake_Job_toOpaque___redArg(v_job_208_);
v___x_211_ = lean_array_push(v___x_209_, v___x_210_);
v___x_212_ = lean_st_ref_put(v_registeredJobs_206_, v___x_211_);
v___x_213_ = l_Lake_Job_renew___redArg(v_job_208_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_213_);
v___x_215_ = v___x_187_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_a_185_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
}
else
{
lean_object* v_a_221_; lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v___x_182_);
lean_dec_ref(v___f_180_);
v_a_221_ = lean_ctor_get(v___x_183_, 0);
v_a_222_ = lean_ctor_get(v___x_183_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_183_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_inc(v_a_221_);
lean_dec(v___x_183_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_221_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_BuildSpec_query_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_167_ = stack[0].m_obj;
uint8_t v_fmt_168_ = stack[1].m_num;
lean_object* v_a_169_ = stack[2].m_obj;
lean_object* v_a_170_ = stack[3].m_obj;
lean_object* v_a_171_ = stack[4].m_obj;
lean_object* v_a_172_ = stack[5].m_obj;
lean_object* v_a_173_ = stack[6].m_obj;
lean_object* v_a_174_ = stack[7].m_obj;
lean_object* v_res_230_;
v_res_230_ = l_Lake_BuildSpec_query(v_self_167_, v_fmt_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
stack->m_obj
 = v_res_230_;
}
LEAN_EXPORT lean_object* l_Lake_BuildSpec_query___boxed(lean_object* v_self_231_, lean_object* v_fmt_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
uint8_t v_fmt_boxed_240_; lean_object* v_res_241_; 
v_fmt_boxed_240_ = lean_unbox(v_fmt_232_);
v_res_241_ = l_Lake_BuildSpec_query(v_self_231_, v_fmt_boxed_240_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec(v_a_235_);
lean_dec(v_a_234_);
return v_res_241_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(size_t v_sz_242_, size_t v_i_243_, lean_object* v_bs_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
uint8_t v___x_252_; 
v___x_252_ = lean_usize_dec_lt(v_i_243_, v_sz_242_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec_ref(v___y_245_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v_bs_244_);
lean_ctor_set(v___x_253_, 1, v___y_250_);
return v___x_253_;
}
else
{
lean_object* v_v_254_; lean_object* v_info_255_; lean_object* v___x_256_; lean_object* v_bs_x27_257_; lean_object* v_a_259_; lean_object* v_a_260_; lean_object* v___x_266_; 
v_v_254_ = lean_array_uget_borrowed(v_bs_244_, v_i_243_);
v_info_255_ = lean_ctor_get(v_v_254_, 0);
lean_inc_ref_n(v_info_255_, 2);
v___x_256_ = lean_unsigned_to_nat(0u);
v_bs_x27_257_ = lean_array_uset(v_bs_244_, v_i_243_, v___x_256_);
lean_inc_ref(v___y_245_);
lean_inc_ref(v___y_249_);
lean_inc(v___y_248_);
lean_inc(v___y_247_);
lean_inc(v___y_246_);
v___x_266_ = lean_apply_7(v___y_245_, v_info_255_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, lean_box(0));
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v_a_268_; lean_object* v_task_269_; lean_object* v_kind_270_; lean_object* v_caption_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
v_a_268_ = lean_ctor_get(v___x_266_, 1);
lean_inc(v_a_268_);
lean_dec_ref_known(v___x_266_, 2);
v_task_269_ = lean_ctor_get(v_a_267_, 0);
v_kind_270_ = lean_ctor_get(v_a_267_, 1);
v_caption_271_ = lean_ctor_get(v_a_267_, 2);
v___x_272_ = lean_string_utf8_byte_size(v_caption_271_);
v___x_273_ = lean_nat_dec_eq(v___x_272_, v___x_256_);
if (v___x_273_ == 0)
{
lean_dec_ref(v_info_255_);
v_a_259_ = v_a_267_;
v_a_260_ = v_a_268_;
goto v___jp_258_;
}
else
{
lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_289_; 
lean_inc(v_kind_270_);
lean_inc_ref(v_task_269_);
v_isSharedCheck_289_ = !lean_is_exclusive(v_a_267_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; 
v_unused_290_ = lean_ctor_get(v_a_267_, 2);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_a_267_, 1);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_a_267_, 0);
lean_dec(v_unused_292_);
v___x_275_ = v_a_267_;
v_isShared_276_ = v_isSharedCheck_289_;
goto v_resetjp_274_;
}
else
{
lean_dec(v_a_267_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_289_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v_registeredJobs_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; lean_object* v_job_282_; 
v_registeredJobs_277_ = lean_ctor_get(v___y_249_, 4);
v___x_278_ = l_Lake_BuildInfo_key(v_info_255_);
v___x_279_ = l_Lake_BuildKey_toSimpleString(v___x_278_);
v___x_280_ = 0;
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 2, v___x_279_);
v_job_282_ = v___x_275_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_task_269_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_kind_270_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v___x_279_);
v_job_282_ = v_reuseFailAlloc_288_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_ctor_set_uint8(v_job_282_, sizeof(void*)*3, v___x_280_);
v___x_283_ = lean_st_ref_take(v_registeredJobs_277_);
lean_inc_ref(v_job_282_);
v___x_284_ = l_Lake_Job_toOpaque___redArg(v_job_282_);
v___x_285_ = lean_array_push(v___x_283_, v___x_284_);
v___x_286_ = lean_st_ref_put(v_registeredJobs_277_, v___x_285_);
v___x_287_ = l_Lake_Job_renew___redArg(v_job_282_);
v_a_259_ = v___x_287_;
v_a_260_ = v_a_268_;
goto v___jp_258_;
}
}
}
}
else
{
lean_object* v_a_293_; lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec_ref(v_bs_x27_257_);
lean_dec_ref(v_info_255_);
lean_dec_ref(v___y_245_);
v_a_293_ = lean_ctor_get(v___x_266_, 0);
v_a_294_ = lean_ctor_get(v___x_266_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_266_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_inc(v_a_293_);
lean_dec(v___x_266_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_293_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
v___jp_258_:
{
lean_object* v___x_261_; size_t v___x_262_; size_t v___x_263_; lean_object* v___x_264_; 
v___x_261_ = l_Lake_Job_toOpaque___redArg(v_a_259_);
v___x_262_ = ((size_t)1ULL);
v___x_263_ = lean_usize_add(v_i_243_, v___x_262_);
v___x_264_ = lean_array_uset(v_bs_x27_257_, v_i_243_, v___x_261_);
v_i_243_ = v___x_263_;
v_bs_244_ = v___x_264_;
v___y_250_ = v_a_260_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_242_ = stack[0].m_num;
size_t v_i_243_ = stack[1].m_num;
lean_object* v_bs_244_ = stack[2].m_obj;
lean_object* v___y_245_ = stack[3].m_obj;
lean_object* v___y_246_ = stack[4].m_obj;
lean_object* v___y_247_ = stack[5].m_obj;
lean_object* v___y_248_ = stack[6].m_obj;
lean_object* v___y_249_ = stack[7].m_obj;
lean_object* v___y_250_ = stack[8].m_obj;
lean_object* v_res_302_;
v_res_302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(v_sz_242_, v_i_243_, v_bs_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
stack->m_obj
 = v_res_302_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0___boxed(lean_object* v_sz_303_, lean_object* v_i_304_, lean_object* v_bs_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
size_t v_sz_boxed_313_; size_t v_i_boxed_314_; lean_object* v_res_315_; 
v_sz_boxed_313_ = lean_unbox_usize(v_sz_303_);
lean_dec(v_sz_303_);
v_i_boxed_314_ = lean_unbox_usize(v_i_304_);
lean_dec(v_i_304_);
v_res_315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(v_sz_boxed_313_, v_i_boxed_314_, v_bs_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec(v___y_308_);
lean_dec(v___y_307_);
return v_res_315_;
}
}
lean_object* l_Lake_buildSpecs(lean_object* v_specs_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
size_t v_sz_325_; size_t v___x_326_; lean_object* v___x_327_; 
v_sz_325_ = lean_array_size(v_specs_317_);
v___x_326_ = ((size_t)0ULL);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(v_sz_325_, v___x_326_, v_specs_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_338_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_a_329_ = lean_ctor_get(v___x_327_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_338_ == 0)
{
v___x_331_ = v___x_327_;
v_isShared_332_ = v_isSharedCheck_338_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_338_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_333_ = ((lean_object*)(l_Lake_buildSpecs___closed__0));
v___x_334_ = l_Lake_Job_mixArray___redArg(v_a_328_, v___x_333_);
lean_dec(v_a_328_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_334_);
v___x_336_ = v___x_331_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_a_329_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
else
{
lean_object* v_a_339_; lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_a_339_ = lean_ctor_get(v___x_327_, 0);
v_a_340_ = lean_ctor_get(v___x_327_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_327_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_inc(v_a_339_);
lean_dec(v___x_327_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_339_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_buildSpecs_0interp(lean_interpreter_value* stack)
{
lean_object* v_specs_317_ = stack[0].m_obj;
lean_object* v_a_318_ = stack[1].m_obj;
lean_object* v_a_319_ = stack[2].m_obj;
lean_object* v_a_320_ = stack[3].m_obj;
lean_object* v_a_321_ = stack[4].m_obj;
lean_object* v_a_322_ = stack[5].m_obj;
lean_object* v_a_323_ = stack[6].m_obj;
lean_object* v_res_348_;
v_res_348_ = l_Lake_buildSpecs(v_specs_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l_Lake_buildSpecs___boxed(lean_object* v_specs_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lake_buildSpecs(v_specs_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec(v_a_352_);
lean_dec(v_a_351_);
return v_res_357_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0(lean_object* v_format_358_, uint8_t v_fmt_359_, lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_371_; 
v_a_361_ = lean_ctor_get(v_x_360_, 0);
v_a_362_ = lean_ctor_get(v_x_360_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_371_ == 0)
{
v___x_364_ = v_x_360_;
v_isShared_365_ = v_isSharedCheck_371_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_inc(v_a_361_);
lean_dec(v_x_360_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_371_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_366_ = lean_box(v_fmt_359_);
v___x_367_ = lean_apply_2(v_format_358_, v___x_366_, v_a_361_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_367_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_a_362_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
else
{
lean_object* v_a_372_; lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v_format_358_);
v_a_372_ = lean_ctor_get(v_x_360_, 0);
v_a_373_ = lean_ctor_get(v_x_360_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v_x_360_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_inc(v_a_372_);
lean_dec(v_x_360_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_372_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_format_358_ = stack[0].m_obj;
uint8_t v_fmt_359_ = stack[1].m_num;
lean_object* v_x_360_ = stack[2].m_obj;
lean_object* v_res_381_;
v_res_381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0(v_format_358_, v_fmt_359_, v_x_360_);
stack->m_obj
 = v_res_381_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0___boxed(lean_object* v_format_382_, lean_object* v_fmt_383_, lean_object* v_x_384_){
_start:
{
uint8_t v_fmt_boxed_385_; lean_object* v_res_386_; 
v_fmt_boxed_385_ = lean_unbox(v_fmt_383_);
v_res_386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0(v_format_382_, v_fmt_boxed_385_, v_x_384_);
return v_res_386_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(uint8_t v_fmt_387_, size_t v_sz_388_, size_t v_i_389_, lean_object* v_bs_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
uint8_t v___x_398_; 
v___x_398_ = lean_usize_dec_lt(v_i_389_, v_sz_388_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec_ref(v___y_391_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_bs_390_);
lean_ctor_set(v___x_399_, 1, v___y_396_);
return v___x_399_;
}
else
{
lean_object* v_v_400_; lean_object* v_info_401_; lean_object* v_format_402_; lean_object* v___x_403_; lean_object* v_bs_x27_404_; lean_object* v_a_406_; lean_object* v_a_407_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___f_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_v_400_ = lean_array_uget_borrowed(v_bs_390_, v_i_389_);
v_info_401_ = lean_ctor_get(v_v_400_, 0);
lean_inc_ref_n(v_info_401_, 2);
v_format_402_ = lean_ctor_get(v_v_400_, 1);
lean_inc_ref(v_format_402_);
v___x_403_ = lean_unsigned_to_nat(0u);
v_bs_x27_404_ = lean_array_uset(v_bs_390_, v_i_389_, v___x_403_);
v___x_412_ = lean_box(0);
v___x_413_ = lean_box(v_fmt_387_);
v___f_414_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_414_, 0, v_format_402_);
lean_closure_set(v___f_414_, 1, v___x_413_);
v___x_415_ = l_Lake_BuildInfo_key(v_info_401_);
v___x_416_ = l_Lake_BuildKey_toSimpleString(v___x_415_);
lean_inc_ref(v___y_391_);
lean_inc_ref(v___y_395_);
lean_inc(v___y_394_);
lean_inc(v___y_393_);
lean_inc(v___y_392_);
v___x_417_ = lean_apply_7(v___y_391_, v_info_401_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, lean_box(0));
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v_a_419_; lean_object* v_task_420_; lean_object* v_caption_421_; uint8_t v_optional_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_442_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
v_a_419_ = lean_ctor_get(v___x_417_, 1);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_417_, 2);
v_task_420_ = lean_ctor_get(v_a_418_, 0);
v_caption_421_ = lean_ctor_get(v_a_418_, 2);
v_optional_422_ = lean_ctor_get_uint8(v_a_418_, sizeof(void*)*3);
v_isSharedCheck_442_ = !lean_is_exclusive(v_a_418_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; 
v_unused_443_ = lean_ctor_get(v_a_418_, 1);
lean_dec(v_unused_443_);
v___x_424_ = v_a_418_;
v_isShared_425_ = v_isSharedCheck_442_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_caption_421_);
lean_inc(v_task_420_);
lean_dec(v_a_418_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_442_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_426_ = 0;
v___x_427_ = lean_task_map(v___f_414_, v_task_420_, v___x_403_, v___x_426_);
v___x_428_ = lean_string_utf8_byte_size(v_caption_421_);
v___x_429_ = lean_nat_dec_eq(v___x_428_, v___x_403_);
if (v___x_429_ == 0)
{
lean_object* v___x_431_; 
lean_dec_ref(v___x_416_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v___x_412_);
lean_ctor_set(v___x_424_, 0, v___x_427_);
v___x_431_ = v___x_424_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_caption_421_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*3, v_optional_422_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
v_a_406_ = v___x_431_;
v_a_407_ = v_a_419_;
goto v___jp_405_;
}
}
else
{
lean_object* v_registeredJobs_433_; lean_object* v_job_435_; 
lean_dec_ref(v_caption_421_);
v_registeredJobs_433_ = lean_ctor_get(v___y_395_, 4);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 2, v___x_416_);
lean_ctor_set(v___x_424_, 1, v___x_412_);
lean_ctor_set(v___x_424_, 0, v___x_427_);
v_job_435_ = v___x_424_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v___x_416_);
v_job_435_ = v_reuseFailAlloc_441_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
lean_ctor_set_uint8(v_job_435_, sizeof(void*)*3, v___x_426_);
v___x_436_ = lean_st_ref_take(v_registeredJobs_433_);
lean_inc_ref(v_job_435_);
v___x_437_ = l_Lake_Job_toOpaque___redArg(v_job_435_);
v___x_438_ = lean_array_push(v___x_436_, v___x_437_);
v___x_439_ = lean_st_ref_put(v_registeredJobs_433_, v___x_438_);
v___x_440_ = l_Lake_Job_renew___redArg(v_job_435_);
v_a_406_ = v___x_440_;
v_a_407_ = v_a_419_;
goto v___jp_405_;
}
}
}
}
else
{
lean_object* v_a_444_; lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec_ref(v___x_416_);
lean_dec_ref(v___f_414_);
lean_dec_ref(v_bs_x27_404_);
lean_dec_ref(v___y_391_);
v_a_444_ = lean_ctor_get(v___x_417_, 0);
v_a_445_ = lean_ctor_get(v___x_417_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_417_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_inc(v_a_444_);
lean_dec(v___x_417_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_444_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
v___jp_405_:
{
size_t v___x_408_; size_t v___x_409_; lean_object* v___x_410_; 
v___x_408_ = ((size_t)1ULL);
v___x_409_ = lean_usize_add(v_i_389_, v___x_408_);
v___x_410_ = lean_array_uset(v_bs_x27_404_, v_i_389_, v_a_406_);
v_i_389_ = v___x_409_;
v_bs_390_ = v___x_410_;
v___y_396_ = v_a_407_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_387_ = stack[0].m_num;
size_t v_sz_388_ = stack[1].m_num;
size_t v_i_389_ = stack[2].m_num;
lean_object* v_bs_390_ = stack[3].m_obj;
lean_object* v___y_391_ = stack[4].m_obj;
lean_object* v___y_392_ = stack[5].m_obj;
lean_object* v___y_393_ = stack[6].m_obj;
lean_object* v___y_394_ = stack[7].m_obj;
lean_object* v___y_395_ = stack[8].m_obj;
lean_object* v___y_396_ = stack[9].m_obj;
lean_object* v_res_453_;
v_res_453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(v_fmt_387_, v_sz_388_, v_i_389_, v_bs_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___boxed(lean_object* v_fmt_454_, lean_object* v_sz_455_, lean_object* v_i_456_, lean_object* v_bs_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
uint8_t v_fmt_boxed_465_; size_t v_sz_boxed_466_; size_t v_i_boxed_467_; lean_object* v_res_468_; 
v_fmt_boxed_465_ = lean_unbox(v_fmt_454_);
v_sz_boxed_466_ = lean_unbox_usize(v_sz_455_);
lean_dec(v_sz_455_);
v_i_boxed_467_ = lean_unbox_usize(v_i_456_);
lean_dec(v_i_456_);
v_res_468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(v_fmt_boxed_465_, v_sz_boxed_466_, v_i_boxed_467_, v_bs_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec(v___y_460_);
lean_dec(v___y_459_);
return v_res_468_;
}
}
lean_object* l_Lake_querySpecs(lean_object* v_specs_469_, uint8_t v_fmt_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
size_t v_sz_478_; size_t v___x_479_; lean_object* v___x_480_; 
v_sz_478_ = lean_array_size(v_specs_469_);
v___x_479_ = ((size_t)0ULL);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(v_fmt_470_, v_sz_478_, v___x_479_, v_specs_469_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_491_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
v_a_482_ = lean_ctor_get(v___x_480_, 1);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_491_ == 0)
{
v___x_484_ = v___x_480_;
v_isShared_485_ = v_isSharedCheck_491_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_inc(v_a_481_);
lean_dec(v___x_480_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_491_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_486_ = ((lean_object*)(l_Lake_buildSpecs___closed__0));
v___x_487_ = l_Lake_Job_collectArray___redArg(v_a_481_, v___x_486_);
lean_dec(v_a_481_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_487_);
v___x_489_ = v___x_484_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_a_482_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
else
{
lean_object* v_a_492_; lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v_a_492_ = lean_ctor_get(v___x_480_, 0);
v_a_493_ = lean_ctor_get(v___x_480_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_480_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_inc(v_a_492_);
lean_dec(v___x_480_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_492_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_querySpecs_0interp(lean_interpreter_value* stack)
{
lean_object* v_specs_469_ = stack[0].m_obj;
uint8_t v_fmt_470_ = stack[1].m_num;
lean_object* v_a_471_ = stack[2].m_obj;
lean_object* v_a_472_ = stack[3].m_obj;
lean_object* v_a_473_ = stack[4].m_obj;
lean_object* v_a_474_ = stack[5].m_obj;
lean_object* v_a_475_ = stack[6].m_obj;
lean_object* v_a_476_ = stack[7].m_obj;
lean_object* v_res_501_;
v_res_501_ = l_Lake_querySpecs(v_specs_469_, v_fmt_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
stack->m_obj
 = v_res_501_;
}
LEAN_EXPORT lean_object* l_Lake_querySpecs___boxed(lean_object* v_specs_502_, lean_object* v_fmt_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
uint8_t v_fmt_boxed_511_; lean_object* v_res_512_; 
v_fmt_boxed_511_ = lean_unbox(v_fmt_503_);
v_res_512_ = l_Lake_querySpecs(v_specs_502_, v_fmt_boxed_511_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec(v_a_506_);
lean_dec(v_a_505_);
return v_res_512_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(lean_object* v___x_516_, lean_object* v_as_517_, size_t v_sz_518_, size_t v_i_519_, lean_object* v_b_520_){
_start:
{
uint8_t v___x_521_; 
v___x_521_ = lean_usize_dec_lt(v_i_519_, v_sz_518_);
if (v___x_521_ == 0)
{
lean_inc_ref(v_b_520_);
return v_b_520_;
}
else
{
lean_object* v_a_522_; lean_object* v_baseName_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_a_522_ = lean_array_uget_borrowed(v_as_517_, v_i_519_);
v_baseName_523_ = lean_ctor_get(v_a_522_, 1);
v___x_524_ = lean_box(0);
v___x_525_ = lean_name_eq(v_baseName_523_, v___x_516_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; size_t v___x_527_; size_t v___x_528_; 
v___x_526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0));
v___x_527_ = ((size_t)1ULL);
v___x_528_ = lean_usize_add(v_i_519_, v___x_527_);
v_i_519_ = v___x_528_;
v_b_520_ = v___x_526_;
goto _start;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
lean_inc(v_a_522_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v_a_522_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v___x_524_);
return v___x_532_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_516_ = stack[0].m_obj;
lean_object* v_as_517_ = stack[1].m_obj;
size_t v_sz_518_ = stack[2].m_num;
size_t v_i_519_ = stack[3].m_num;
lean_object* v_b_520_ = stack[4].m_obj;
lean_object* v_res_533_;
v_res_533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v___x_516_, v_as_517_, v_sz_518_, v_i_519_, v_b_520_);
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___boxed(lean_object* v___x_534_, lean_object* v_as_535_, lean_object* v_sz_536_, lean_object* v_i_537_, lean_object* v_b_538_){
_start:
{
size_t v_sz_boxed_539_; size_t v_i_boxed_540_; lean_object* v_res_541_; 
v_sz_boxed_539_ = lean_unbox_usize(v_sz_536_);
lean_dec(v_sz_536_);
v_i_boxed_540_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v___x_534_, v_as_535_, v_sz_boxed_539_, v_i_boxed_540_, v_b_538_);
lean_dec_ref(v_b_538_);
lean_dec_ref(v_as_535_);
lean_dec(v___x_534_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec(lean_object* v_ws_542_, lean_object* v_spec_543_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_547_ = lean_string_utf8_byte_size(v_spec_543_);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_nat_dec_eq(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v_packages_550_; lean_object* v___x_551_; lean_object* v___x_552_; size_t v_sz_553_; size_t v___x_554_; lean_object* v___x_555_; lean_object* v_fst_556_; 
v_packages_550_ = lean_ctor_get(v_ws_542_, 4);
lean_inc_ref(v_spec_543_);
v___x_551_ = l_Lake_stringToLegalOrSimpleName(v_spec_543_);
v___x_552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0));
v_sz_553_ = lean_array_size(v_packages_550_);
v___x_554_ = ((size_t)0ULL);
v___x_555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v___x_551_, v_packages_550_, v_sz_553_, v___x_554_, v___x_552_);
lean_dec(v___x_551_);
v_fst_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_fst_556_);
lean_dec_ref(v___x_555_);
if (lean_obj_tag(v_fst_556_) == 0)
{
goto v___jp_544_;
}
else
{
lean_object* v_val_557_; 
v_val_557_ = lean_ctor_get(v_fst_556_, 0);
lean_inc(v_val_557_);
lean_dec_ref_known(v_fst_556_, 1);
if (lean_obj_tag(v_val_557_) == 0)
{
goto v___jp_544_;
}
else
{
lean_object* v_val_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec_ref(v_spec_543_);
v_val_558_ = lean_ctor_get(v_val_557_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v_val_557_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v_val_557_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_val_558_);
lean_dec(v_val_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_val_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
else
{
lean_object* v_packages_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec_ref(v_spec_543_);
v_packages_566_ = lean_ctor_get(v_ws_542_, 4);
v___x_567_ = lean_array_fget_borrowed(v_packages_566_, v___x_548_);
lean_inc(v___x_567_);
v___x_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
v___jp_544_:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_545_, 0, v_spec_543_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parsePackageSpec___boxed(lean_object* v_ws_569_, lean_object* v_spec_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lake_parsePackageSpec(v_ws_569_, v_spec_570_);
lean_dec_ref(v_ws_569_);
return v_res_571_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_box(0);
v___x_574_ = l_Lean_Json_compress(v___x_573_);
return v___x_574_;
}
}
lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(uint8_t v_fmt_575_){
_start:
{
if (v_fmt_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = ((lean_object*)(l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0));
return v___x_576_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1, &l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1_once, _init_l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1);
return v___x_577_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_575_ = stack[0].m_num;
lean_object* v_res_578_;
v_res_578_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(v_fmt_575_);
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___boxed(lean_object* v_fmt_579_){
_start:
{
uint8_t v_fmt_boxed_580_; lean_object* v_res_581_; 
v_fmt_boxed_580_ = lean_unbox(v_fmt_579_);
v_res_581_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(v_fmt_boxed_580_);
return v_res_581_;
}
}
lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(uint8_t v_fmt_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(v_fmt_582_);
return v___x_584_;
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_582_ = stack[0].m_num;
lean_object* v_a_583_ = stack[1].m_obj;
lean_object* v_res_585_;
v_res_585_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(v_fmt_582_, v_a_583_);
stack->m_obj
 = v_res_585_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___boxed(lean_object* v_fmt_586_, lean_object* v_a_587_){
_start:
{
uint8_t v_fmt_boxed_588_; lean_object* v_res_589_; 
v_fmt_boxed_588_ = lean_unbox(v_fmt_586_);
v_res_589_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(v_fmt_boxed_588_, v_a_587_);
lean_dec_ref(v_a_587_);
return v_res_589_;
}
}
lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(uint8_t v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(v___y_590_);
return v___x_592_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_590_ = stack[0].m_num;
lean_object* v___y_591_ = stack[1].m_obj;
lean_object* v_res_593_;
v_res_593_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(v___y_590_, v___y_591_);
stack->m_obj
 = v_res_593_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0___boxed(lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
uint8_t v___y_288__boxed_596_; lean_object* v_res_597_; 
v___y_288__boxed_596_ = lean_unbox(v___y_594_);
v_res_597_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(v___y_288__boxed_596_, v___y_595_);
lean_dec_ref(v___y_595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(lean_object* v_ws_600_, lean_object* v_mod_601_, lean_object* v_facet_602_){
_start:
{
uint8_t v___x_603_; 
v___x_603_ = l_Lean_Name_isAnonymous(v_facet_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = l_Lake_Module_keyword;
lean_inc(v_facet_602_);
v___x_605_ = l_Lean_Name_append(v___x_604_, v_facet_602_);
v___x_606_ = l_Lake_Workspace_findModuleFacetConfig_x3f(v___x_605_, v_ws_600_);
if (lean_obj_tag(v___x_606_) == 1)
{
lean_object* v_lib_607_; lean_object* v_pkg_608_; lean_object* v_val_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_facet_602_);
v_lib_607_ = lean_ctor_get(v_mod_601_, 0);
v_pkg_608_ = lean_ctor_get(v_lib_607_, 0);
v_val_609_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_623_ == 0)
{
v___x_611_ = v___x_606_;
v_isShared_612_ = v_isSharedCheck_623_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_val_609_);
lean_dec(v___x_606_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_623_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_name_613_; lean_object* v_keyName_614_; uint8_t v_buildable_615_; lean_object* v_format_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v_name_613_ = lean_ctor_get(v_mod_601_, 1);
v_keyName_614_ = lean_ctor_get(v_pkg_608_, 2);
v_buildable_615_ = lean_ctor_get_uint8(v_val_609_, sizeof(void*)*4);
v_format_616_ = lean_ctor_get(v_val_609_, 3);
lean_inc_ref(v_format_616_);
lean_dec(v_val_609_);
lean_inc(v_name_613_);
lean_inc(v_keyName_614_);
v___x_617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_617_, 0, v_keyName_614_);
lean_ctor_set(v___x_617_, 1, v_name_613_);
v___x_618_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___x_604_);
lean_ctor_set(v___x_618_, 2, v_mod_601_);
lean_ctor_set(v___x_618_, 3, v___x_605_);
v___x_619_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v_format_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*2, v_buildable_615_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_619_);
v___x_621_ = v___x_611_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v___x_606_);
lean_dec(v___x_605_);
lean_dec_ref(v_mod_601_);
v___x_624_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0));
v___x_625_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v_facet_602_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
else
{
lean_object* v_lib_627_; lean_object* v_pkg_628_; lean_object* v_name_629_; lean_object* v_keyName_630_; lean_object* v___f_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
lean_dec(v_facet_602_);
v_lib_627_ = lean_ctor_get(v_mod_601_, 0);
v_pkg_628_ = lean_ctor_get(v_lib_627_, 0);
v_name_629_ = lean_ctor_get(v_mod_601_, 1);
v_keyName_630_ = lean_ctor_get(v_pkg_628_, 2);
v___f_631_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1));
v___x_632_ = l_Lake_Module_irArtsFacet;
lean_inc(v_name_629_);
lean_inc(v_keyName_630_);
v___x_633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_633_, 0, v_keyName_630_);
lean_ctor_set(v___x_633_, 1, v_name_629_);
v___x_634_ = l_Lake_Module_keyword;
v___x_635_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
lean_ctor_set(v___x_635_, 2, v_mod_601_);
lean_ctor_set(v___x_635_, 3, v___x_632_);
v___x_636_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___f_631_);
lean_ctor_set_uint8(v___x_636_, sizeof(void*)*2, v___x_603_);
v___x_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___boxed(lean_object* v_ws_638_, lean_object* v_mod_639_, lean_object* v_facet_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_638_, v_mod_639_, v_facet_640_);
lean_dec_ref(v_ws_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(lean_object* v_pkg_642_, lean_object* v_name_643_, lean_object* v_facet_644_, lean_object* v_config_645_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = l_Lean_Name_isAnonymous(v_facet_644_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec_ref(v_config_645_);
lean_dec_ref(v_pkg_642_);
v___x_647_ = lean_alloc_ctor(20, 2, 0);
lean_ctor_set(v___x_647_, 0, v_name_643_);
lean_ctor_set(v___x_647_, 1, v_facet_644_);
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
else
{
lean_object* v_format_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_658_; 
lean_dec(v_facet_644_);
v_format_649_ = lean_ctor_get(v_config_645_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_config_645_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; 
v_unused_659_ = lean_ctor_get(v_config_645_, 0);
lean_dec(v_unused_659_);
v___x_651_ = v_config_645_;
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_format_649_);
lean_dec(v_config_645_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v_name_643_);
lean_ctor_set(v___x_651_, 0, v_pkg_642_);
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_pkg_642_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_name_643_);
v___x_654_ = v_reuseFailAlloc_657_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_format_649_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*2, v___x_646_);
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(lean_object* v_ws_663_, lean_object* v_pkg_664_, lean_object* v_target_665_, lean_object* v_decl_666_, lean_object* v_facet_667_){
_start:
{
lean_object* v_name_668_; lean_object* v_kind_669_; lean_object* v_config_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_726_; 
v_name_668_ = lean_ctor_get(v_decl_666_, 1);
v_kind_669_ = lean_ctor_get(v_decl_666_, 2);
v_config_670_ = lean_ctor_get(v_decl_666_, 3);
v_isSharedCheck_726_ = !lean_is_exclusive(v_decl_666_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v_decl_666_, 0);
lean_dec(v_unused_727_);
v___x_672_ = v_decl_666_;
v_isShared_673_ = v_isSharedCheck_726_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_config_670_);
lean_inc(v_kind_669_);
lean_inc(v_name_668_);
lean_dec(v_decl_666_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_726_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
uint8_t v___x_674_; 
v___x_674_ = l_Lean_Name_isAnonymous(v_kind_669_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; lean_object* v___y_677_; uint8_t v___x_704_; 
lean_dec(v_target_665_);
v___x_675_ = 1;
v___x_704_ = l_Lean_Name_isAnonymous(v_facet_667_);
if (v___x_704_ == 0)
{
v___y_677_ = v_facet_667_;
goto v___jp_676_;
}
else
{
lean_object* v___x_705_; 
lean_dec(v_facet_667_);
v___x_705_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1));
v___y_677_ = v___x_705_;
goto v___jp_676_;
}
v___jp_676_:
{
lean_object* v_facetConfigs_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_facetConfigs_678_ = lean_ctor_get(v_ws_663_, 6);
lean_inc(v___y_677_);
lean_inc(v_kind_669_);
v___x_679_ = l_Lean_Name_append(v_kind_669_, v___y_677_);
v___x_680_ = l_Lake_FacetConfigMap_get_x3f(v___x_679_, v_facetConfigs_678_);
if (lean_obj_tag(v___x_680_) == 1)
{
lean_object* v_val_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_700_; 
lean_dec(v___y_677_);
v_val_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_700_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_700_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_val_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_700_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v_keyName_685_; uint8_t v_buildable_686_; lean_object* v_format_687_; lean_object* v_tgt_688_; lean_object* v___x_689_; lean_object* v_info_691_; 
v_keyName_685_ = lean_ctor_get(v_pkg_664_, 2);
lean_inc(v_keyName_685_);
v_buildable_686_ = lean_ctor_get_uint8(v_val_681_, sizeof(void*)*4);
v_format_687_ = lean_ctor_get(v_val_681_, 3);
lean_inc_ref(v_format_687_);
lean_dec(v_val_681_);
lean_inc(v_name_668_);
v_tgt_688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_tgt_688_, 0, v_pkg_664_);
lean_ctor_set(v_tgt_688_, 1, v_name_668_);
lean_ctor_set(v_tgt_688_, 2, v_config_670_);
v___x_689_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_689_, 0, v_keyName_685_);
lean_ctor_set(v___x_689_, 1, v_name_668_);
if (v_isShared_673_ == 0)
{
lean_ctor_set_tag(v___x_672_, 1);
lean_ctor_set(v___x_672_, 3, v___x_679_);
lean_ctor_set(v___x_672_, 2, v_tgt_688_);
lean_ctor_set(v___x_672_, 1, v_kind_669_);
lean_ctor_set(v___x_672_, 0, v___x_689_);
v_info_691_ = v___x_672_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_kind_669_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_tgt_688_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v___x_679_);
v_info_691_ = v_reuseFailAlloc_699_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_692_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_692_, 0, v_info_691_);
lean_ctor_set(v___x_692_, 1, v_format_687_);
lean_ctor_set_uint8(v___x_692_, sizeof(void*)*2, v_buildable_686_);
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = lean_mk_empty_array_with_capacity(v___x_693_);
v___x_695_ = lean_array_push(v___x_694_, v___x_692_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_695_);
v___x_697_ = v___x_683_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_del_object(v___x_672_);
lean_dec(v_config_670_);
lean_dec(v_name_668_);
lean_dec_ref(v_pkg_664_);
v___x_701_ = l_Lean_Name_toString(v_kind_669_, v___x_675_);
v___x_702_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___y_677_);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
}
}
else
{
lean_object* v___x_706_; 
lean_del_object(v___x_672_);
lean_dec(v_kind_669_);
lean_dec(v_name_668_);
v___x_706_ = l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(v_pkg_664_, v_target_665_, v_facet_667_, v_config_670_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_725_; 
v_a_715_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_725_ == 0)
{
v___x_717_ = v___x_706_;
v_isShared_718_ = v_isSharedCheck_725_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_706_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_725_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_mk_empty_array_with_capacity(v___x_719_);
v___x_721_ = lean_array_push(v___x_720_, v_a_715_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_721_);
v___x_723_ = v___x_717_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___boxed(lean_object* v_ws_728_, lean_object* v_pkg_729_, lean_object* v_target_730_, lean_object* v_decl_731_, lean_object* v_facet_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_728_, v_pkg_729_, v_target_730_, v_decl_731_, v_facet_732_);
lean_dec_ref(v_ws_728_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(lean_object* v_ws_734_, lean_object* v_pkg_735_, lean_object* v_target_736_, lean_object* v_facet_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lake_Package_findTargetDecl_x3f(v_target_736_, v_pkg_735_);
if (lean_obj_tag(v___x_738_) == 1)
{
lean_object* v_val_739_; lean_object* v___x_740_; 
v_val_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_734_, v_pkg_735_, v_target_736_, v_val_739_, v_facet_737_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; 
lean_dec(v___x_738_);
lean_inc_ref(v_pkg_735_);
lean_inc(v_target_736_);
v___x_741_ = l_Lake_Package_findTargetModule_x3f(v_target_736_, v_pkg_735_);
if (lean_obj_tag(v___x_741_) == 1)
{
lean_object* v_val_742_; lean_object* v___x_743_; 
lean_dec(v_target_736_);
lean_dec_ref(v_pkg_735_);
v_val_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_734_, v_val_742_, v_facet_737_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_762_; 
v_a_752_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_762_ == 0)
{
v___x_754_ = v___x_743_;
v_isShared_755_ = v_isSharedCheck_762_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_743_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_762_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = lean_mk_empty_array_with_capacity(v___x_756_);
v___x_758_ = lean_array_push(v___x_757_, v_a_752_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_758_);
v___x_760_ = v___x_754_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v_baseName_763_; uint8_t v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec(v___x_741_);
lean_dec(v_facet_737_);
v_baseName_763_ = lean_ctor_get(v_pkg_735_, 1);
lean_inc(v_baseName_763_);
lean_dec_ref(v_pkg_735_);
v___x_764_ = 0;
v___x_765_ = l_Lean_Name_toString(v_target_736_, v___x_764_);
v___x_766_ = lean_alloc_ctor(17, 2, 0);
lean_ctor_set(v___x_766_, 0, v_baseName_763_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage___boxed(lean_object* v_ws_768_, lean_object* v_pkg_769_, lean_object* v_target_770_, lean_object* v_facet_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_768_, v_pkg_769_, v_target_770_, v_facet_771_);
lean_dec_ref(v_ws_768_);
return v_res_772_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(lean_object* v_ws_773_, lean_object* v_pkg_774_, lean_object* v_as_775_, size_t v_i_776_, size_t v_stop_777_, lean_object* v_b_778_){
_start:
{
lean_object* v_a_780_; uint8_t v___x_784_; 
v___x_784_ = lean_usize_dec_eq(v_i_776_, v_stop_777_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_array_uget_borrowed(v_as_775_, v_i_776_);
v___x_786_ = lean_box(0);
lean_inc(v___x_785_);
lean_inc_ref(v_pkg_774_);
v___x_787_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_773_, v_pkg_774_, v___x_785_, v___x_786_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_dec_ref(v_b_778_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_dec_ref(v_pkg_774_);
return v___x_787_;
}
else
{
lean_object* v_a_788_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
v_a_780_ = v_a_788_;
goto v___jp_779_;
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_787_, 1);
v___x_790_ = l_Array_append___redArg(v_b_778_, v_a_789_);
lean_dec(v_a_789_);
v_a_780_ = v___x_790_;
goto v___jp_779_;
}
}
else
{
lean_object* v___x_791_; 
lean_dec_ref(v_pkg_774_);
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v_b_778_);
return v___x_791_;
}
v___jp_779_:
{
size_t v___x_781_; size_t v___x_782_; 
v___x_781_ = ((size_t)1ULL);
v___x_782_ = lean_usize_add(v_i_776_, v___x_781_);
v_i_776_ = v___x_782_;
v_b_778_ = v_a_780_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_773_ = stack[0].m_obj;
lean_object* v_pkg_774_ = stack[1].m_obj;
lean_object* v_as_775_ = stack[2].m_obj;
size_t v_i_776_ = stack[3].m_num;
size_t v_stop_777_ = stack[4].m_num;
lean_object* v_b_778_ = stack[5].m_obj;
lean_object* v_res_792_;
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_773_, v_pkg_774_, v_as_775_, v_i_776_, v_stop_777_, v_b_778_);
stack->m_obj
 = v_res_792_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0___boxed(lean_object* v_ws_793_, lean_object* v_pkg_794_, lean_object* v_as_795_, lean_object* v_i_796_, lean_object* v_stop_797_, lean_object* v_b_798_){
_start:
{
size_t v_i_boxed_799_; size_t v_stop_boxed_800_; lean_object* v_res_801_; 
v_i_boxed_799_ = lean_unbox_usize(v_i_796_);
lean_dec(v_i_796_);
v_stop_boxed_800_ = lean_unbox_usize(v_stop_797_);
lean_dec(v_stop_797_);
v_res_801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_793_, v_pkg_794_, v_as_795_, v_i_boxed_799_, v_stop_boxed_800_, v_b_798_);
lean_dec_ref(v_as_795_);
lean_dec_ref(v_ws_793_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(lean_object* v_ws_806_, lean_object* v_pkg_807_){
_start:
{
lean_object* v_defaultTargets_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_defaultTargets_808_ = lean_ctor_get(v_pkg_807_, 17);
lean_inc_ref(v_defaultTargets_808_);
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0));
v___x_811_ = lean_array_get_size(v_defaultTargets_808_);
v___x_812_ = lean_nat_dec_lt(v___x_809_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
lean_dec_ref(v_defaultTargets_808_);
lean_dec_ref(v_pkg_807_);
v___x_813_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1));
return v___x_813_;
}
else
{
size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; 
v___x_814_ = ((size_t)0ULL);
v___x_815_ = lean_usize_of_nat(v___x_811_);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_806_, v_pkg_807_, v_defaultTargets_808_, v___x_814_, v___x_815_, v___x_810_);
lean_dec_ref(v_defaultTargets_808_);
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___boxed(lean_object* v_ws_817_, lean_object* v_pkg_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_817_, v_pkg_818_);
lean_dec_ref(v_ws_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(lean_object* v_ws_821_, lean_object* v_pkg_822_, lean_object* v_facet_823_){
_start:
{
uint8_t v___x_824_; 
v___x_824_ = l_Lean_Name_isAnonymous(v_facet_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = l_Lake_Package_keyword;
lean_inc(v_facet_823_);
v___x_826_ = l_Lean_Name_append(v___x_825_, v_facet_823_);
v___x_827_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v___x_826_, v_ws_821_);
if (lean_obj_tag(v___x_827_) == 1)
{
lean_object* v_val_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_844_; 
lean_dec(v_facet_823_);
v_val_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_844_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_844_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_val_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_844_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_keyName_832_; uint8_t v_buildable_833_; lean_object* v_format_834_; lean_object* v___x_836_; 
v_keyName_832_ = lean_ctor_get(v_pkg_822_, 2);
v_buildable_833_ = lean_ctor_get_uint8(v_val_828_, sizeof(void*)*4);
v_format_834_ = lean_ctor_get(v_val_828_, 3);
lean_inc_ref(v_format_834_);
lean_dec(v_val_828_);
lean_inc(v_keyName_832_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v_keyName_832_);
v___x_836_ = v___x_830_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_keyName_832_);
v___x_836_ = v_reuseFailAlloc_843_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_837_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_825_);
lean_ctor_set(v___x_837_, 2, v_pkg_822_);
lean_ctor_set(v___x_837_, 3, v___x_826_);
v___x_838_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v_format_834_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*2, v_buildable_833_);
v___x_839_ = lean_unsigned_to_nat(1u);
v___x_840_ = lean_mk_empty_array_with_capacity(v___x_839_);
v___x_841_ = lean_array_push(v___x_840_, v___x_838_);
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v___x_827_);
lean_dec(v___x_826_);
lean_dec_ref(v_pkg_822_);
v___x_845_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0));
v___x_846_ = lean_alloc_ctor(14, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v_facet_823_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
else
{
lean_object* v___x_848_; 
lean_dec(v_facet_823_);
v___x_848_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_821_, v_pkg_822_);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___boxed(lean_object* v_ws_849_, lean_object* v_pkg_850_, lean_object* v_facet_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_849_, v_pkg_850_, v_facet_851_);
lean_dec_ref(v_ws_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(lean_object* v_ws_853_, lean_object* v_target_854_, lean_object* v_facet_855_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lake_Workspace_findTargetDecl_x3f(v_target_854_, v_ws_853_);
if (lean_obj_tag(v___x_881_) == 1)
{
lean_object* v_val_882_; lean_object* v_fst_883_; lean_object* v_snd_884_; lean_object* v___x_885_; 
v_val_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v___x_881_, 1);
v_fst_883_ = lean_ctor_get(v_val_882_, 0);
lean_inc(v_fst_883_);
v_snd_884_ = lean_ctor_get(v_val_882_, 1);
lean_inc(v_snd_884_);
lean_dec(v_val_882_);
v___x_885_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(v_ws_853_, v_fst_883_, v_target_854_, v_snd_884_, v_facet_855_);
return v___x_885_;
}
else
{
lean_object* v_packages_886_; lean_object* v___x_887_; size_t v_sz_888_; size_t v___x_889_; lean_object* v___x_890_; lean_object* v_fst_891_; 
lean_dec(v___x_881_);
v_packages_886_ = lean_ctor_get(v_ws_853_, 4);
v___x_887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0));
v_sz_888_ = lean_array_size(v_packages_886_);
v___x_889_ = ((size_t)0ULL);
v___x_890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v_target_854_, v_packages_886_, v_sz_888_, v___x_889_, v___x_887_);
v_fst_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_fst_891_);
lean_dec_ref(v___x_890_);
if (lean_obj_tag(v_fst_891_) == 0)
{
goto v___jp_856_;
}
else
{
lean_object* v_val_892_; 
v_val_892_ = lean_ctor_get(v_fst_891_, 0);
lean_inc(v_val_892_);
lean_dec_ref_known(v_fst_891_, 1);
if (lean_obj_tag(v_val_892_) == 1)
{
lean_object* v_val_893_; lean_object* v___x_894_; 
lean_dec(v_target_854_);
v_val_893_ = lean_ctor_get(v_val_892_, 0);
lean_inc(v_val_893_);
lean_dec_ref_known(v_val_892_, 1);
v___x_894_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_853_, v_val_893_, v_facet_855_);
return v___x_894_;
}
else
{
lean_dec(v_val_892_);
goto v___jp_856_;
}
}
}
v___jp_856_:
{
lean_object* v___x_857_; 
lean_inc(v_target_854_);
v___x_857_ = l_Lake_Workspace_findTargetModule_x3f(v_target_854_, v_ws_853_);
if (lean_obj_tag(v___x_857_) == 1)
{
lean_object* v_val_858_; lean_object* v___x_859_; 
lean_dec(v_target_854_);
v_val_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_853_, v_val_858_, v_facet_855_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_878_; 
v_a_868_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_878_ == 0)
{
v___x_870_ = v___x_859_;
v_isShared_871_ = v_isSharedCheck_878_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_859_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_878_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_mk_empty_array_with_capacity(v___x_872_);
v___x_874_ = lean_array_push(v___x_873_, v_a_868_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_874_);
v___x_876_ = v___x_870_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec(v___x_857_);
lean_dec(v_facet_855_);
v___x_879_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v___x_879_, 0, v_target_854_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace___boxed(lean_object* v_ws_895_, lean_object* v_target_896_, lean_object* v_facet_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(v_ws_895_, v_target_896_, v_facet_897_);
lean_dec_ref(v_ws_895_);
return v_res_898_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___redArg(){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___redArg___closed__0));
return v___x_902_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_903_;
v_res_903_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___redArg();
stack->m_obj
 = v_res_903_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___redArg___boxed(lean_object* v___dummy_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___redArg();
return v_res_905_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0(void){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___redArg();
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(lean_object* v_s_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___boxed(lean_object* v_s_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v_s_909_);
lean_dec_ref(v_s_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(lean_object* v_spec_911_, lean_object* v___x_912_, lean_object* v___x_913_, lean_object* v_a_914_, lean_object* v_b_915_){
_start:
{
lean_object* v_it_917_; lean_object* v_startInclusive_918_; lean_object* v_endExclusive_919_; 
if (lean_obj_tag(v_a_914_) == 0)
{
lean_object* v_currPos_923_; lean_object* v_searcher_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_947_; 
v_currPos_923_ = lean_ctor_get(v_a_914_, 0);
v_searcher_924_ = lean_ctor_get(v_a_914_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v_a_914_);
if (v_isSharedCheck_947_ == 0)
{
v___x_926_ = v_a_914_;
v_isShared_927_ = v_isSharedCheck_947_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_searcher_924_);
lean_inc(v_currPos_923_);
lean_dec(v_a_914_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_947_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
uint8_t v_decide_928_; 
v_decide_928_ = lean_nat_dec_eq(v_searcher_924_, v___x_913_);
if (v_decide_928_ == 0)
{
uint32_t v___x_929_; uint32_t v___x_930_; uint8_t v___x_931_; 
v___x_929_ = 47;
v___x_930_ = lean_string_utf8_get_fast(v_spec_911_, v_searcher_924_);
v___x_931_ = lean_uint32_dec_eq(v___x_930_, v___x_929_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_string_utf8_next_fast(v_spec_911_, v_searcher_924_);
lean_dec(v_searcher_924_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_932_);
v___x_934_ = v___x_926_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_currPos_923_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_932_);
v___x_934_ = v_reuseFailAlloc_936_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
v_a_914_ = v___x_934_;
goto _start;
}
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v_slice_940_; lean_object* v_nextIt_942_; 
v___x_937_ = lean_string_utf8_next_fast(v_spec_911_, v_searcher_924_);
v___x_938_ = lean_nat_sub(v___x_937_, v_searcher_924_);
v___x_939_ = lean_nat_add(v_searcher_924_, v___x_938_);
lean_dec(v___x_938_);
v_slice_940_ = l_String_Slice_subslice_x21(v___x_912_, v_currPos_923_, v_searcher_924_);
lean_inc(v___x_939_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_939_);
lean_ctor_set(v___x_926_, 0, v___x_939_);
v_nextIt_942_ = v___x_926_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v___x_939_);
v_nextIt_942_ = v_reuseFailAlloc_945_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v_startInclusive_943_; lean_object* v_endExclusive_944_; 
v_startInclusive_943_ = lean_ctor_get(v_slice_940_, 0);
lean_inc(v_startInclusive_943_);
v_endExclusive_944_ = lean_ctor_get(v_slice_940_, 1);
lean_inc(v_endExclusive_944_);
lean_dec_ref(v_slice_940_);
v_it_917_ = v_nextIt_942_;
v_startInclusive_918_ = v_startInclusive_943_;
v_endExclusive_919_ = v_endExclusive_944_;
goto v___jp_916_;
}
}
}
else
{
lean_object* v___x_946_; 
lean_del_object(v___x_926_);
lean_dec(v_searcher_924_);
v___x_946_ = lean_box(1);
lean_inc(v___x_913_);
v_it_917_ = v___x_946_;
v_startInclusive_918_ = v_currPos_923_;
v_endExclusive_919_ = v___x_913_;
goto v___jp_916_;
}
}
}
else
{
lean_dec(v___x_913_);
lean_dec_ref(v_spec_911_);
return v_b_915_;
}
v___jp_916_:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
lean_inc_ref(v_spec_911_);
v___x_920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_920_, 0, v_spec_911_);
lean_ctor_set(v___x_920_, 1, v_startInclusive_918_);
lean_ctor_set(v___x_920_, 2, v_endExclusive_919_);
v___x_921_ = lean_array_push(v_b_915_, v___x_920_);
v_a_914_ = v_it_917_;
v_b_915_ = v___x_921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg___boxed(lean_object* v_spec_948_, lean_object* v___x_949_, lean_object* v___x_950_, lean_object* v_a_951_, lean_object* v_b_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_948_, v___x_949_, v___x_950_, v_a_951_, v_b_952_);
lean_dec_ref(v___x_949_);
return v_res_953_;
}
}
lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(lean_object* v_ws_957_, lean_object* v_spec_958_, lean_object* v_facet_959_, uint8_t v_isMaybePath_960_, uint8_t v_explicit_961_){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_string_utf8_byte_size(v_spec_958_);
lean_inc_ref_n(v_spec_958_, 2);
v___x_970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_970_, 0, v_spec_958_);
lean_ctor_set(v___x_970_, 1, v___x_968_);
lean_ctor_set(v___x_970_, 2, v___x_969_);
v___x_971_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0);
v___x_972_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0));
v___x_973_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_958_, v___x_970_, v___x_969_, v___x_971_, v___x_972_);
lean_dec_ref_known(v___x_970_, 3);
v___x_974_ = lean_array_to_list(v___x_973_);
if (lean_obj_tag(v___x_974_) == 1)
{
lean_object* v_tail_975_; 
v_tail_975_ = lean_ctor_get(v___x_974_, 1);
if (lean_obj_tag(v_tail_975_) == 0)
{
lean_object* v_head_976_; lean_object* v_str_977_; lean_object* v_startInclusive_978_; lean_object* v_endExclusive_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
lean_dec_ref(v_spec_958_);
v_head_976_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_head_976_);
lean_dec_ref_known(v___x_974_, 2);
v_str_977_ = lean_ctor_get(v_head_976_, 0);
lean_inc_ref(v_str_977_);
v_startInclusive_978_ = lean_ctor_get(v_head_976_, 1);
lean_inc(v_startInclusive_978_);
v_endExclusive_979_ = lean_ctor_get(v_head_976_, 2);
lean_inc(v_endExclusive_979_);
lean_dec(v_head_976_);
v___x_980_ = lean_nat_sub(v_endExclusive_979_, v_startInclusive_978_);
v___x_981_ = lean_nat_dec_eq(v___x_980_, v___x_968_);
lean_dec(v___x_980_);
if (v___x_981_ == 0)
{
if (v_explicit_961_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_string_utf8_extract_fast(v_str_977_, v_startInclusive_978_, v_endExclusive_979_);
lean_dec(v_endExclusive_979_);
lean_dec(v_startInclusive_978_);
lean_dec_ref(v_str_977_);
v___x_983_ = l_Lake_stringToLegalOrSimpleName(v___x_982_);
v___x_984_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(v_ws_957_, v___x_983_, v_facet_959_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_string_utf8_extract_fast(v_str_977_, v_startInclusive_978_, v_endExclusive_979_);
lean_dec(v_endExclusive_979_);
lean_dec(v_startInclusive_978_);
lean_dec_ref(v_str_977_);
v___x_986_ = l_Lake_parsePackageSpec(v_ws_957_, v___x_985_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec(v_facet_959_);
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_996_; 
v_a_995_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_986_, 1);
v___x_996_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_957_, v_a_995_, v_facet_959_);
return v___x_996_;
}
}
}
else
{
lean_object* v_packages_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec(v_endExclusive_979_);
lean_dec(v_startInclusive_978_);
lean_dec_ref(v_str_977_);
v_packages_997_ = lean_ctor_get(v_ws_957_, 4);
v___x_998_ = lean_array_fget_borrowed(v_packages_997_, v___x_968_);
lean_inc(v___x_998_);
v___x_999_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_957_, v___x_998_, v_facet_959_);
return v___x_999_;
}
}
else
{
lean_object* v_tail_1000_; 
lean_inc_ref(v_tail_975_);
v_tail_1000_ = lean_ctor_get(v_tail_975_, 1);
if (lean_obj_tag(v_tail_1000_) == 0)
{
lean_object* v_head_1001_; lean_object* v_head_1002_; lean_object* v_str_1003_; lean_object* v_startInclusive_1004_; lean_object* v_endExclusive_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec_ref(v_spec_958_);
v_head_1001_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_head_1001_);
lean_dec_ref_known(v___x_974_, 2);
v_head_1002_ = lean_ctor_get(v_tail_975_, 0);
lean_inc(v_head_1002_);
lean_dec_ref_known(v_tail_975_, 2);
v_str_1003_ = lean_ctor_get(v_head_1001_, 0);
lean_inc_ref(v_str_1003_);
v_startInclusive_1004_ = lean_ctor_get(v_head_1001_, 1);
lean_inc(v_startInclusive_1004_);
v_endExclusive_1005_ = lean_ctor_get(v_head_1001_, 2);
lean_inc(v_endExclusive_1005_);
lean_dec(v_head_1001_);
v___x_1006_ = lean_string_utf8_extract_fast(v_str_1003_, v_startInclusive_1004_, v_endExclusive_1005_);
lean_dec(v_endExclusive_1005_);
lean_dec(v_startInclusive_1004_);
lean_dec_ref(v_str_1003_);
v___x_1007_ = l_Lake_parsePackageSpec(v_ws_957_, v___x_1006_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v_head_1002_);
lean_dec(v_facet_959_);
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1063_; 
v_a_1016_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1018_ = v___x_1007_;
v_isShared_1019_ = v_isSharedCheck_1063_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1007_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1063_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_str_1020_; lean_object* v_startInclusive_1021_; lean_object* v_endExclusive_1022_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v_str_1020_ = lean_ctor_get(v_head_1002_, 0);
lean_inc_ref(v_str_1020_);
v_startInclusive_1021_ = lean_ctor_get(v_head_1002_, 1);
lean_inc(v_startInclusive_1021_);
v_endExclusive_1022_ = lean_ctor_get(v_head_1002_, 2);
lean_inc(v_endExclusive_1022_);
v___x_1027_ = lean_nat_sub(v_endExclusive_1022_, v_startInclusive_1021_);
v___x_1028_ = lean_nat_dec_eq(v___x_1027_, v___x_968_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_dec_le(v___x_1029_, v___x_1027_);
lean_dec(v___x_1027_);
if (v___x_1030_ == 0)
{
lean_del_object(v___x_1018_);
lean_dec(v_head_1002_);
goto v___jp_1023_;
}
else
{
lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1031_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_1032_ = lean_string_memcmp(v_str_1020_, v___x_1031_, v_startInclusive_1021_, v___x_968_, v___x_1029_);
if (v___x_1032_ == 0)
{
lean_del_object(v___x_1018_);
lean_dec(v_head_1002_);
goto v___jp_1023_;
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1033_ = l_String_Slice_Pos_nextn(v_head_1002_, v___x_968_, v___x_1029_);
lean_dec(v_head_1002_);
v___x_1034_ = lean_nat_add(v_startInclusive_1021_, v___x_1033_);
lean_dec(v___x_1033_);
lean_dec(v_startInclusive_1021_);
v___x_1035_ = lean_string_utf8_extract_fast(v_str_1020_, v___x_1034_, v_endExclusive_1022_);
lean_dec(v_endExclusive_1022_);
lean_dec(v___x_1034_);
lean_dec_ref(v_str_1020_);
v___x_1036_ = l_String_toName(v___x_1035_);
lean_inc(v___x_1036_);
v___x_1037_ = l_Lake_Package_findTargetModule_x3f(v___x_1036_, v_a_1016_);
if (lean_obj_tag(v___x_1037_) == 1)
{
lean_object* v_val_1038_; lean_object* v___x_1039_; 
lean_dec(v___x_1036_);
lean_del_object(v___x_1018_);
v_val_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_val_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v___x_1039_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_957_, v_val_1038_, v_facet_959_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1057_; 
v_a_1048_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1050_ = v___x_1039_;
v_isShared_1051_ = v_isSharedCheck_1057_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1039_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1057_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1052_ = lean_mk_empty_array_with_capacity(v___x_1029_);
v___x_1053_ = lean_array_push(v___x_1052_, v_a_1048_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1053_);
v___x_1055_ = v___x_1050_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1060_; 
lean_dec(v___x_1037_);
lean_dec(v_facet_959_);
v___x_1058_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1036_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set_tag(v___x_1018_, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1058_);
v___x_1060_ = v___x_1018_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
else
{
lean_object* v___x_1062_; 
lean_dec(v___x_1027_);
lean_dec(v_endExclusive_1022_);
lean_dec(v_startInclusive_1021_);
lean_dec_ref(v_str_1020_);
lean_del_object(v___x_1018_);
lean_dec(v_head_1002_);
v___x_1062_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(v_ws_957_, v_a_1016_, v_facet_959_);
return v___x_1062_;
}
v___jp_1023_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = lean_string_utf8_extract_fast(v_str_1020_, v_startInclusive_1021_, v_endExclusive_1022_);
lean_dec(v_endExclusive_1022_);
lean_dec(v_startInclusive_1021_);
lean_dec_ref(v_str_1020_);
v___x_1025_ = l_Lake_stringToLegalOrSimpleName(v___x_1024_);
v___x_1026_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(v_ws_957_, v_a_1016_, v___x_1025_, v_facet_959_);
return v___x_1026_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_975_, 2);
lean_dec_ref_known(v___x_974_, 2);
lean_dec(v_facet_959_);
goto v___jp_962_;
}
}
}
else
{
lean_dec(v___x_974_);
lean_dec(v_facet_959_);
goto v___jp_962_;
}
v___jp_962_:
{
if (v_isMaybePath_960_ == 0)
{
uint32_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_963_ = 47;
v___x_964_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_964_, 0, v_spec_958_);
lean_ctor_set_uint32(v___x_964_, sizeof(void*)*1, v___x_963_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_966_, 0, v_spec_958_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_957_ = stack[0].m_obj;
lean_object* v_spec_958_ = stack[1].m_obj;
lean_object* v_facet_959_ = stack[2].m_obj;
uint8_t v_isMaybePath_960_ = stack[3].m_num;
uint8_t v_explicit_961_ = stack[4].m_num;
lean_object* v_res_1064_;
v_res_1064_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_957_, v_spec_958_, v_facet_959_, v_isMaybePath_960_, v_explicit_961_);
stack->m_obj
 = v_res_1064_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___boxed(lean_object* v_ws_1065_, lean_object* v_spec_1066_, lean_object* v_facet_1067_, lean_object* v_isMaybePath_1068_, lean_object* v_explicit_1069_){
_start:
{
uint8_t v_isMaybePath_boxed_1070_; uint8_t v_explicit_boxed_1071_; lean_object* v_res_1072_; 
v_isMaybePath_boxed_1070_ = lean_unbox(v_isMaybePath_1068_);
v_explicit_boxed_1071_ = lean_unbox(v_explicit_1069_);
v_res_1072_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1065_, v_spec_1066_, v_facet_1067_, v_isMaybePath_boxed_1070_, v_explicit_boxed_1071_);
lean_dec_ref(v_ws_1065_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(lean_object* v_spec_1073_, lean_object* v___x_1074_, lean_object* v___x_1075_, lean_object* v_inst_1076_, lean_object* v_R_1077_, lean_object* v_a_1078_, lean_object* v_b_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_1073_, v___x_1074_, v___x_1075_, v_a_1078_, v_b_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___boxed(lean_object* v_spec_1081_, lean_object* v___x_1082_, lean_object* v___x_1083_, lean_object* v_inst_1084_, lean_object* v_R_1085_, lean_object* v_a_1086_, lean_object* v_b_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(v_spec_1081_, v___x_1082_, v___x_1083_, v_inst_1084_, v_R_1085_, v_a_1086_, v_b_1087_);
lean_dec_ref(v___x_1082_);
return v_res_1088_;
}
}
lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(lean_object* v_ws_1090_, lean_object* v_spec_1091_, lean_object* v_facet_1092_){
_start:
{
uint8_t v___y_1095_; uint8_t v___y_1096_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1210_ = lean_string_utf8_byte_size(v_spec_1091_);
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = lean_nat_dec_le(v___x_1211_, v___x_1210_);
if (v___x_1212_ == 0)
{
goto v___jp_1175_;
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1213_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1214_ = lean_unsigned_to_nat(0u);
v___x_1215_ = lean_string_memcmp(v_spec_1091_, v___x_1213_, v___x_1214_, v___x_1214_, v___x_1211_);
if (v___x_1215_ == 0)
{
goto v___jp_1175_;
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; lean_object* v___x_1220_; 
lean_inc_ref(v_spec_1091_);
v___x_1216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1216_, 0, v_spec_1091_);
lean_ctor_set(v___x_1216_, 1, v___x_1214_);
lean_ctor_set(v___x_1216_, 2, v___x_1210_);
v___x_1217_ = l_String_Slice_Pos_nextn(v___x_1216_, v___x_1214_, v___x_1211_);
lean_dec_ref_known(v___x_1216_, 3);
v___x_1218_ = lean_string_utf8_extract_fast(v_spec_1091_, v___x_1217_, v___x_1210_);
lean_dec(v___x_1217_);
lean_dec_ref(v_spec_1091_);
v___x_1219_ = 0;
v___x_1220_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1090_, v___x_1218_, v_facet_1092_, v___x_1219_, v___x_1212_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 1);
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_a_1229_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1220_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1220_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set_tag(v___x_1231_, 0);
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
v___jp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
lean_inc_ref(v_spec_1091_);
v___x_1097_ = l_Lake_resolvePath(v_spec_1091_);
v___x_1098_ = lean_string_utf8_byte_size(v___x_1097_);
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = lean_nat_dec_eq(v___x_1098_, v___x_1099_);
if (v___x_1100_ == 0)
{
uint8_t v___x_1101_; 
v___x_1101_ = l_System_FilePath_isDir(v___x_1097_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lake_Workspace_findModuleBySrc_x3f(v___x_1097_, v_ws_1090_);
if (lean_obj_tag(v___x_1102_) == 1)
{
lean_object* v_val_1103_; lean_object* v___x_1104_; 
lean_dec_ref(v_spec_1091_);
v_val_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_val_1103_);
lean_dec_ref_known(v___x_1102_, 1);
v___x_1104_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_1090_, v_val_1103_, v_facet_1092_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set_tag(v___x_1107_, 1);
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1123_; 
v_a_1113_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1115_ = v___x_1104_;
v_isShared_1116_ = v_isSharedCheck_1123_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1104_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1123_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_mk_empty_array_with_capacity(v___x_1117_);
v___x_1119_ = lean_array_push(v___x_1118_, v_a_1113_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set_tag(v___x_1115_, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1119_);
v___x_1121_ = v___x_1115_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_object* v___x_1124_; 
lean_dec(v___x_1102_);
v___x_1124_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1090_, v_spec_1091_, v_facet_1092_, v___y_1095_, v___x_1101_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set_tag(v___x_1127_, 1);
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
v_a_1133_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1124_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1124_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 0);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
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
}
}
else
{
lean_object* v___x_1141_; 
lean_dec_ref(v___x_1097_);
v___x_1141_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1090_, v_spec_1091_, v_facet_1092_, v___y_1096_, v___y_1096_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set_tag(v___x_1144_, 1);
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v_a_1150_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1141_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1141_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 0);
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
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
}
}
else
{
lean_object* v___x_1158_; 
lean_dec_ref(v___x_1097_);
v___x_1158_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(v_ws_1090_, v_spec_1091_, v_facet_1092_, v___y_1095_, v___y_1096_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set_tag(v___x_1161_, 1);
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_a_1167_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1158_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1158_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 0);
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
v___jp_1175_:
{
uint8_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1176_ = 1;
v___x_1177_ = lean_string_utf8_byte_size(v_spec_1091_);
v___x_1178_ = lean_unsigned_to_nat(1u);
v___x_1179_ = lean_nat_dec_le(v___x_1178_, v___x_1177_);
if (v___x_1179_ == 0)
{
v___y_1095_ = v___x_1176_;
v___y_1096_ = v___x_1179_;
goto v___jp_1094_;
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1180_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1));
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = lean_string_memcmp(v_spec_1091_, v___x_1180_, v___x_1181_, v___x_1181_, v___x_1178_);
if (v___x_1182_ == 0)
{
v___y_1095_ = v___x_1176_;
v___y_1096_ = v___x_1182_;
goto v___jp_1094_;
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v_mod_1186_; lean_object* v___x_1187_; 
lean_inc_ref(v_spec_1091_);
v___x_1183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1183_, 0, v_spec_1091_);
lean_ctor_set(v___x_1183_, 1, v___x_1181_);
lean_ctor_set(v___x_1183_, 2, v___x_1177_);
v___x_1184_ = l_String_Slice_Pos_nextn(v___x_1183_, v___x_1181_, v___x_1178_);
lean_dec_ref_known(v___x_1183_, 3);
v___x_1185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1185_, 0, v_spec_1091_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
lean_ctor_set(v___x_1185_, 2, v___x_1177_);
v_mod_1186_ = l_String_Slice_toName(v___x_1185_);
lean_dec_ref_known(v___x_1185_, 3);
lean_inc(v_mod_1186_);
v___x_1187_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_1186_, v_ws_1090_);
if (lean_obj_tag(v___x_1187_) == 1)
{
lean_object* v_val_1188_; lean_object* v___x_1189_; 
lean_dec(v_mod_1186_);
v_val_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_val_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v___x_1189_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(v_ws_1090_, v_val_1188_, v_facet_1092_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set_tag(v___x_1192_, 1);
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1207_; 
v_a_1198_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1200_ = v___x_1189_;
v_isShared_1201_ = v_isSharedCheck_1207_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1189_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1207_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1202_ = lean_mk_empty_array_with_capacity(v___x_1178_);
v___x_1203_ = lean_array_push(v___x_1202_, v_a_1198_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set_tag(v___x_1200_, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1203_);
v___x_1205_ = v___x_1200_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v___x_1187_);
lean_dec(v_facet_1092_);
v___x_1208_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_mod_1186_);
v___x_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_1090_ = stack[0].m_obj;
lean_object* v_spec_1091_ = stack[1].m_obj;
lean_object* v_facet_1092_ = stack[2].m_obj;
lean_object* v_res_1237_;
v_res_1237_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1090_, v_spec_1091_, v_facet_1092_);
stack->m_obj
 = v_res_1237_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___boxed(lean_object* v_ws_1238_, lean_object* v_spec_1239_, lean_object* v_facet_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1238_, v_spec_1239_, v_facet_1240_);
lean_dec_ref(v_ws_1238_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec(lean_object* v_ws_1243_, lean_object* v_spec_1244_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = lean_string_utf8_byte_size(v_spec_1244_);
lean_inc_ref_n(v_spec_1244_, 2);
v___x_1254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1254_, 0, v_spec_1244_);
lean_ctor_set(v___x_1254_, 1, v___x_1252_);
lean_ctor_set(v___x_1254_, 2, v___x_1253_);
v___x_1255_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0);
v___x_1256_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0));
v___x_1257_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_1244_, v___x_1254_, v___x_1253_, v___x_1255_, v___x_1256_);
lean_dec_ref_known(v___x_1254_, 3);
v___x_1258_ = lean_array_to_list(v___x_1257_);
if (lean_obj_tag(v___x_1258_) == 1)
{
lean_object* v_tail_1259_; 
v_tail_1259_ = lean_ctor_get(v___x_1258_, 1);
if (lean_obj_tag(v_tail_1259_) == 0)
{
lean_object* v_head_1260_; lean_object* v_str_1261_; lean_object* v_startInclusive_1262_; lean_object* v_endExclusive_1263_; lean_object* v___x_1264_; lean_object* v_targetName_1265_; lean_object* v___x_1266_; 
v_head_1260_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_head_1260_);
lean_dec_ref_known(v___x_1258_, 2);
v_str_1261_ = lean_ctor_get(v_head_1260_, 0);
lean_inc_ref(v_str_1261_);
v_startInclusive_1262_ = lean_ctor_get(v_head_1260_, 1);
lean_inc(v_startInclusive_1262_);
v_endExclusive_1263_ = lean_ctor_get(v_head_1260_, 2);
lean_inc(v_endExclusive_1263_);
lean_dec(v_head_1260_);
v___x_1264_ = lean_string_utf8_extract_fast(v_str_1261_, v_startInclusive_1262_, v_endExclusive_1263_);
lean_dec(v_endExclusive_1263_);
lean_dec(v_startInclusive_1262_);
lean_dec_ref(v_str_1261_);
v_targetName_1265_ = l_Lake_stringToLegalOrSimpleName(v___x_1264_);
v___x_1266_ = l_Lake_Workspace_findLeanExe_x3f(v_targetName_1265_, v_ws_1243_);
lean_dec(v_targetName_1265_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_spec_1244_);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
else
{
lean_object* v_val_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref(v_spec_1244_);
v_val_1269_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1266_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_val_1269_);
lean_dec(v___x_1266_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_val_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
else
{
lean_object* v_head_1277_; lean_object* v_head_1278_; lean_object* v_tail_1279_; lean_object* v_str_1281_; lean_object* v_startInclusive_1282_; lean_object* v_endExclusive_1283_; 
lean_inc_ref(v_tail_1259_);
v_head_1277_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_head_1277_);
lean_dec_ref_known(v___x_1258_, 2);
v_head_1278_ = lean_ctor_get(v_tail_1259_, 0);
lean_inc(v_head_1278_);
v_tail_1279_ = lean_ctor_get(v_tail_1259_, 1);
lean_inc(v_tail_1279_);
lean_dec_ref_known(v_tail_1259_, 2);
if (lean_obj_tag(v_tail_1279_) == 0)
{
lean_object* v_str_1321_; lean_object* v_startInclusive_1322_; lean_object* v_endExclusive_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_str_1321_ = lean_ctor_get(v_head_1277_, 0);
lean_inc_ref(v_str_1321_);
v_startInclusive_1322_ = lean_ctor_get(v_head_1277_, 1);
lean_inc(v_startInclusive_1322_);
v_endExclusive_1323_ = lean_ctor_get(v_head_1277_, 2);
lean_inc(v_endExclusive_1323_);
v___x_1324_ = lean_unsigned_to_nat(1u);
v___x_1325_ = lean_nat_sub(v_endExclusive_1323_, v_startInclusive_1322_);
v___x_1326_ = lean_nat_dec_le(v___x_1324_, v___x_1325_);
lean_dec(v___x_1325_);
if (v___x_1326_ == 0)
{
lean_dec(v_head_1277_);
v_str_1281_ = v_str_1321_;
v_startInclusive_1282_ = v_startInclusive_1322_;
v_endExclusive_1283_ = v_endExclusive_1323_;
goto v___jp_1280_;
}
else
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = ((lean_object*)(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0));
v___x_1328_ = lean_string_memcmp(v_str_1321_, v___x_1327_, v_startInclusive_1322_, v___x_1252_, v___x_1324_);
if (v___x_1328_ == 0)
{
lean_dec(v_head_1277_);
v_str_1281_ = v_str_1321_;
v_startInclusive_1282_ = v_startInclusive_1322_;
v_endExclusive_1283_ = v_endExclusive_1323_;
goto v___jp_1280_;
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = l_String_Slice_Pos_nextn(v_head_1277_, v___x_1252_, v___x_1324_);
lean_dec(v_head_1277_);
v___x_1330_ = lean_nat_add(v_startInclusive_1322_, v___x_1329_);
lean_dec(v___x_1329_);
lean_dec(v_startInclusive_1322_);
v_str_1281_ = v_str_1321_;
v_startInclusive_1282_ = v___x_1330_;
v_endExclusive_1283_ = v_endExclusive_1323_;
goto v___jp_1280_;
}
}
}
else
{
lean_dec(v_tail_1279_);
lean_dec(v_head_1278_);
lean_dec(v_head_1277_);
goto v___jp_1248_;
}
v___jp_1280_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_string_utf8_extract_fast(v_str_1281_, v_startInclusive_1282_, v_endExclusive_1283_);
lean_dec(v_endExclusive_1283_);
lean_dec(v_startInclusive_1282_);
lean_dec_ref(v_str_1281_);
v___x_1285_ = l_Lake_parsePackageSpec(v_ws_1243_, v___x_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v_head_1278_);
lean_dec_ref(v_spec_1244_);
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1320_; 
v_a_1294_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1296_ = v___x_1285_;
v_isShared_1297_ = v_isSharedCheck_1320_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1285_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1320_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_str_1298_; lean_object* v_startInclusive_1299_; lean_object* v_endExclusive_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1319_; 
v_str_1298_ = lean_ctor_get(v_head_1278_, 0);
v_startInclusive_1299_ = lean_ctor_get(v_head_1278_, 1);
v_endExclusive_1300_ = lean_ctor_get(v_head_1278_, 2);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_head_1278_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1302_ = v_head_1278_;
v_isShared_1303_ = v_isSharedCheck_1319_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_endExclusive_1300_);
lean_inc(v_startInclusive_1299_);
lean_inc(v_str_1298_);
lean_dec(v_head_1278_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1319_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = lean_string_utf8_extract_fast(v_str_1298_, v_startInclusive_1299_, v_endExclusive_1300_);
lean_dec(v_endExclusive_1300_);
lean_dec(v_startInclusive_1299_);
lean_dec_ref(v_str_1298_);
v___x_1305_ = l_Lake_stringToLegalOrSimpleName(v___x_1304_);
v___x_1306_ = l_Lake_Package_findTargetDecl_x3f(v___x_1305_, v_a_1294_);
lean_dec(v___x_1305_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_del_object(v___x_1302_);
lean_del_object(v___x_1296_);
lean_dec(v_a_1294_);
goto v___jp_1245_;
}
else
{
lean_object* v_val_1307_; lean_object* v_name_1308_; lean_object* v_kind_1309_; lean_object* v_config_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_val_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_val_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v_name_1308_ = lean_ctor_get(v_val_1307_, 1);
lean_inc(v_name_1308_);
v_kind_1309_ = lean_ctor_get(v_val_1307_, 2);
lean_inc(v_kind_1309_);
v_config_1310_ = lean_ctor_get(v_val_1307_, 3);
lean_inc(v_config_1310_);
lean_dec(v_val_1307_);
v___x_1311_ = l_Lake_LeanExe_keyword;
v___x_1312_ = lean_name_eq(v_kind_1309_, v___x_1311_);
lean_dec(v_kind_1309_);
if (v___x_1312_ == 0)
{
lean_dec(v_config_1310_);
lean_dec(v_name_1308_);
lean_del_object(v___x_1302_);
lean_del_object(v___x_1296_);
lean_dec(v_a_1294_);
goto v___jp_1245_;
}
else
{
lean_object* v___x_1314_; 
lean_dec_ref(v_spec_1244_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 2, v_config_1310_);
lean_ctor_set(v___x_1302_, 1, v_name_1308_);
lean_ctor_set(v___x_1302_, 0, v_a_1294_);
v___x_1314_ = v___x_1302_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1294_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_name_1308_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_config_1310_);
v___x_1314_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1314_);
v___x_1316_ = v___x_1296_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
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
lean_dec(v___x_1258_);
goto v___jp_1248_;
}
v___jp_1245_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_1246_, 0, v_spec_1244_);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
v___jp_1248_:
{
uint32_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = 47;
v___x_1250_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_1250_, 0, v_spec_1244_);
lean_ctor_set_uint32(v___x_1250_, sizeof(void*)*1, v___x_1249_);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_parseExeTargetSpec___boxed(lean_object* v_ws_1331_, lean_object* v_spec_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lake_parseExeTargetSpec(v_ws_1331_, v_spec_1332_);
lean_dec_ref(v_ws_1331_);
return v_res_1333_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___redArg(){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___redArg___closed__0));
return v___x_1335_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1336_;
v_res_1336_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___redArg();
stack->m_obj
 = v_res_1336_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___redArg___boxed(lean_object* v___dummy_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___redArg();
return v_res_1338_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___redArg();
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(lean_object* v_s_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___closed__0);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___boxed(lean_object* v_s_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(v_s_1342_);
lean_dec_ref(v_s_1342_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(lean_object* v_spec_1344_, lean_object* v___x_1345_, lean_object* v___x_1346_, lean_object* v_a_1347_, lean_object* v_b_1348_){
_start:
{
lean_object* v_it_1350_; lean_object* v_startInclusive_1351_; lean_object* v_endExclusive_1352_; 
if (lean_obj_tag(v_a_1347_) == 0)
{
lean_object* v_currPos_1357_; lean_object* v_searcher_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1381_; 
v_currPos_1357_ = lean_ctor_get(v_a_1347_, 0);
v_searcher_1358_ = lean_ctor_get(v_a_1347_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_a_1347_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1360_ = v_a_1347_;
v_isShared_1361_ = v_isSharedCheck_1381_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_searcher_1358_);
lean_inc(v_currPos_1357_);
lean_dec(v_a_1347_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1381_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
uint8_t v_decide_1362_; 
v_decide_1362_ = lean_nat_dec_eq(v_searcher_1358_, v___x_1346_);
if (v_decide_1362_ == 0)
{
uint32_t v___x_1363_; uint32_t v___x_1364_; uint8_t v___x_1365_; 
v___x_1363_ = 58;
v___x_1364_ = lean_string_utf8_get_fast(v_spec_1344_, v_searcher_1358_);
v___x_1365_ = lean_uint32_dec_eq(v___x_1364_, v___x_1363_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = lean_string_utf8_next_fast(v_spec_1344_, v_searcher_1358_);
lean_dec(v_searcher_1358_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v___x_1366_);
v___x_1368_ = v___x_1360_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_currPos_1357_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
v_a_1347_ = v___x_1368_;
goto _start;
}
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_slice_1374_; lean_object* v_nextIt_1376_; 
v___x_1371_ = lean_string_utf8_next_fast(v_spec_1344_, v_searcher_1358_);
v___x_1372_ = lean_nat_sub(v___x_1371_, v_searcher_1358_);
v___x_1373_ = lean_nat_add(v_searcher_1358_, v___x_1372_);
lean_dec(v___x_1372_);
v_slice_1374_ = l_String_Slice_subslice_x21(v___x_1345_, v_currPos_1357_, v_searcher_1358_);
lean_inc(v___x_1373_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v___x_1373_);
lean_ctor_set(v___x_1360_, 0, v___x_1373_);
v_nextIt_1376_ = v___x_1360_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v___x_1373_);
v_nextIt_1376_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v_startInclusive_1377_; lean_object* v_endExclusive_1378_; 
v_startInclusive_1377_ = lean_ctor_get(v_slice_1374_, 0);
lean_inc(v_startInclusive_1377_);
v_endExclusive_1378_ = lean_ctor_get(v_slice_1374_, 1);
lean_inc(v_endExclusive_1378_);
lean_dec_ref(v_slice_1374_);
v_it_1350_ = v_nextIt_1376_;
v_startInclusive_1351_ = v_startInclusive_1377_;
v_endExclusive_1352_ = v_endExclusive_1378_;
goto v___jp_1349_;
}
}
}
else
{
lean_object* v___x_1380_; 
lean_del_object(v___x_1360_);
lean_dec(v_searcher_1358_);
v___x_1380_ = lean_box(1);
lean_inc(v___x_1346_);
v_it_1350_ = v___x_1380_;
v_startInclusive_1351_ = v_currPos_1357_;
v_endExclusive_1352_ = v___x_1346_;
goto v___jp_1349_;
}
}
}
else
{
lean_dec(v___x_1346_);
lean_dec_ref(v_spec_1344_);
return v_b_1348_;
}
v___jp_1349_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_inc_ref(v_spec_1344_);
v___x_1353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1353_, 0, v_spec_1344_);
lean_ctor_set(v___x_1353_, 1, v_startInclusive_1351_);
lean_ctor_set(v___x_1353_, 2, v_endExclusive_1352_);
v___x_1354_ = l_String_Slice_toString(v___x_1353_);
lean_dec_ref_known(v___x_1353_, 3);
v___x_1355_ = lean_array_push(v_b_1348_, v___x_1354_);
v_a_1347_ = v_it_1350_;
v_b_1348_ = v___x_1355_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg___boxed(lean_object* v_spec_1382_, lean_object* v___x_1383_, lean_object* v___x_1384_, lean_object* v_a_1385_, lean_object* v_b_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1382_, v___x_1383_, v___x_1384_, v_a_1385_, v_b_1386_);
lean_dec_ref(v___x_1383_);
return v_res_1387_;
}
}
lean_object* l_Lake_parseTargetSpec(lean_object* v_ws_1390_, lean_object* v_spec_1391_){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = lean_string_utf8_byte_size(v_spec_1391_);
lean_inc_ref_n(v_spec_1391_, 2);
v___x_1399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1399_, 0, v_spec_1391_);
lean_ctor_set(v___x_1399_, 1, v___x_1397_);
lean_ctor_set(v___x_1399_, 2, v___x_1398_);
v___x_1400_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___closed__0);
v___x_1401_ = ((lean_object*)(l_Lake_parseTargetSpec___closed__0));
v___x_1402_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1391_, v___x_1399_, v___x_1398_, v___x_1400_, v___x_1401_);
lean_dec_ref_known(v___x_1399_, 3);
v___x_1403_ = lean_array_to_list(v___x_1402_);
if (lean_obj_tag(v___x_1403_) == 1)
{
lean_object* v_tail_1404_; 
v_tail_1404_ = lean_ctor_get(v___x_1403_, 1);
if (lean_obj_tag(v_tail_1404_) == 0)
{
lean_object* v_head_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec_ref(v_spec_1391_);
v_head_1405_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_head_1405_);
lean_dec_ref_known(v___x_1403_, 2);
v___x_1406_ = lean_box(0);
v___x_1407_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1390_, v_head_1405_, v___x_1406_);
return v___x_1407_;
}
else
{
lean_object* v_tail_1408_; 
lean_inc_ref(v_tail_1404_);
v_tail_1408_ = lean_ctor_get(v_tail_1404_, 1);
if (lean_obj_tag(v_tail_1408_) == 0)
{
lean_object* v_head_1409_; lean_object* v_head_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec_ref(v_spec_1391_);
v_head_1409_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_head_1409_);
lean_dec_ref_known(v___x_1403_, 2);
v_head_1410_ = lean_ctor_get(v_tail_1404_, 0);
lean_inc(v_head_1410_);
lean_dec_ref_known(v_tail_1404_, 2);
v___x_1411_ = l_String_toName(v_head_1410_);
v___x_1412_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(v_ws_1390_, v_head_1409_, v___x_1411_);
return v___x_1412_;
}
else
{
lean_dec_ref_known(v_tail_1404_, 2);
lean_dec_ref_known(v___x_1403_, 2);
goto v___jp_1393_;
}
}
}
else
{
lean_dec(v___x_1403_);
goto v___jp_1393_;
}
v___jp_1393_:
{
uint32_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = 58;
v___x_1395_ = lean_alloc_ctor(19, 1, 4);
lean_ctor_set(v___x_1395_, 0, v_spec_1391_);
lean_ctor_set_uint32(v___x_1395_, sizeof(void*)*1, v___x_1394_);
v___x_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
return v___x_1396_;
}
}
}
LEAN_EXPORT void l_Lake_parseTargetSpec_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_1390_ = stack[0].m_obj;
lean_object* v_spec_1391_ = stack[1].m_obj;
lean_object* v_res_1413_;
v_res_1413_ = l_Lake_parseTargetSpec(v_ws_1390_, v_spec_1391_);
stack->m_obj
 = v_res_1413_;
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpec___boxed(lean_object* v_ws_1414_, lean_object* v_spec_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lake_parseTargetSpec(v_ws_1414_, v_spec_1415_);
lean_dec_ref(v_ws_1414_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(lean_object* v_spec_1418_, lean_object* v___x_1419_, lean_object* v___x_1420_, lean_object* v_inst_1421_, lean_object* v_R_1422_, lean_object* v_a_1423_, lean_object* v_b_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_1418_, v___x_1419_, v___x_1420_, v_a_1423_, v_b_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___boxed(lean_object* v_spec_1426_, lean_object* v___x_1427_, lean_object* v___x_1428_, lean_object* v_inst_1429_, lean_object* v_R_1430_, lean_object* v_a_1431_, lean_object* v_b_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(v_spec_1426_, v___x_1427_, v___x_1428_, v_inst_1429_, v_R_1430_, v_a_1431_, v_b_1432_);
lean_dec_ref(v___x_1427_);
return v_res_1433_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(lean_object* v_ws_1434_, lean_object* v_as_x27_1435_, lean_object* v_b_1436_){
_start:
{
if (lean_obj_tag(v_as_x27_1435_) == 0)
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v_b_1436_);
return v___x_1438_;
}
else
{
lean_object* v_head_1439_; lean_object* v_tail_1440_; lean_object* v___x_1441_; 
v_head_1439_ = lean_ctor_get(v_as_x27_1435_, 0);
v_tail_1440_ = lean_ctor_get(v_as_x27_1435_, 1);
lean_inc(v_head_1439_);
v___x_1441_ = l_Lake_parseTargetSpec(v_ws_1434_, v_head_1439_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1443_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1441_, 1);
v___x_1443_ = l_Array_append___redArg(v_b_1436_, v_a_1442_);
lean_dec(v_a_1442_);
v_as_x27_1435_ = v_tail_1440_;
v_b_1436_ = v___x_1443_;
goto _start;
}
else
{
lean_dec_ref(v_b_1436_);
return v___x_1441_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_1434_ = stack[0].m_obj;
lean_object* v_as_x27_1435_ = stack[1].m_obj;
lean_object* v_b_1436_ = stack[2].m_obj;
lean_object* v_res_1445_;
v_res_1445_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1434_, v_as_x27_1435_, v_b_1436_);
stack->m_obj
 = v_res_1445_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg___boxed(lean_object* v_ws_1446_, lean_object* v_as_x27_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1446_, v_as_x27_1447_, v_b_1448_);
lean_dec(v_as_x27_1447_);
lean_dec_ref(v_ws_1446_);
return v_res_1450_;
}
}
lean_object* l_Lake_parseTargetSpecs(lean_object* v_ws_1453_, lean_object* v_specs_1454_){
_start:
{
lean_object* v___x_1456_; lean_object* v_results_1457_; lean_object* v___x_1458_; 
v___x_1456_ = lean_unsigned_to_nat(0u);
v_results_1457_ = ((lean_object*)(l_Lake_parseTargetSpecs___closed__0));
v___x_1458_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1453_, v_specs_1454_, v_results_1457_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v___x_1460_ = lean_array_get_size(v_a_1459_);
v___x_1461_ = lean_nat_dec_eq(v___x_1460_, v___x_1456_);
if (v___x_1461_ == 0)
{
return v___x_1458_;
}
else
{
lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1476_; 
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v___x_1458_, 0);
lean_dec(v_unused_1477_);
v___x_1463_ = v___x_1458_;
v_isShared_1464_ = v_isSharedCheck_1476_;
goto v_resetjp_1462_;
}
else
{
lean_dec(v___x_1458_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1476_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v_packages_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v_packages_1465_ = lean_ctor_get(v_ws_1453_, 4);
v___x_1466_ = lean_array_fget_borrowed(v_packages_1465_, v___x_1456_);
lean_inc(v___x_1466_);
v___x_1467_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_1453_, v___x_1466_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1470_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref_known(v___x_1467_, 1);
if (v_isShared_1464_ == 0)
{
lean_ctor_set_tag(v___x_1463_, 1);
lean_ctor_set(v___x_1463_, 0, v_a_1468_);
v___x_1470_ = v___x_1463_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; 
v_a_1472_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1467_, 1);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v_a_1472_);
v___x_1474_ = v___x_1463_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
else
{
return v___x_1458_;
}
}
}
LEAN_EXPORT void l_Lake_parseTargetSpecs_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_1453_ = stack[0].m_obj;
lean_object* v_specs_1454_ = stack[1].m_obj;
lean_object* v_res_1478_;
v_res_1478_ = l_Lake_parseTargetSpecs(v_ws_1453_, v_specs_1454_);
stack->m_obj
 = v_res_1478_;
}
LEAN_EXPORT lean_object* l_Lake_parseTargetSpecs___boxed(lean_object* v_ws_1479_, lean_object* v_specs_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lake_parseTargetSpecs(v_ws_1479_, v_specs_1480_);
lean_dec(v_specs_1480_);
lean_dec_ref(v_ws_1479_);
return v_res_1482_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(lean_object* v_ws_1483_, lean_object* v_as_1484_, lean_object* v_as_x27_1485_, lean_object* v_b_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(v_ws_1483_, v_as_x27_1485_, v_b_1486_);
return v___x_1489_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_1483_ = stack[0].m_obj;
lean_object* v_as_1484_ = stack[1].m_obj;
lean_object* v_as_x27_1485_ = stack[2].m_obj;
lean_object* v_b_1486_ = stack[3].m_obj;
lean_object* v_res_1490_;
v_res_1490_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(v_ws_1483_, v_as_1484_, v_as_x27_1485_, v_b_1486_, lean_box(0));
stack->m_obj
 = v_res_1490_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___boxed(lean_object* v_ws_1491_, lean_object* v_as_1492_, lean_object* v_as_x27_1493_, lean_object* v_b_1494_, lean_object* v_a_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(v_ws_1491_, v_as_1492_, v_as_x27_1493_, v_b_1494_, v_a_1495_);
lean_dec(v_as_x27_1493_);
lean_dec(v_as_1492_);
lean_dec_ref(v_ws_1491_);
return v_res_1497_;
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
