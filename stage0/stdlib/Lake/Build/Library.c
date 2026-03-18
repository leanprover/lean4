// Lean compiler output
// Module: Lake.Build.Library
// Imports: public import Lake.Config.FacetConfig import Lake.Build.Common import Lake.Build.Targets import Lake.Build.Job.Register import Lake.Build.Target.Fetch import Lake.Build.Infos
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
extern lean_object* l_Lake_LeanLib_modulesFacet;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_LeanLib_libName(lean_object*);
lean_object* l_Lake_nameToStaticLib(lean_object*, uint8_t);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lake_Job_await___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_ModuleFacet_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
extern lean_object* l_Lake_instDataKindDynlib;
lean_object* l_Lake_nameToSharedLib(lean_object*, uint8_t);
uint8_t l_Lake_LeanLib_isPlugin(lean_object*);
lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_dynlibFacet;
extern lean_object* l_Lake_ExternLib_keyword;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_sharedFacet;
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lake_Module_transImportsFacet;
extern lean_object* l_Lake_Module_keyword;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Target_fetchIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
extern lean_object* l_Lake_instDataKindUnit;
lean_object* l_Lake_Job_mixArray___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_defaultFacet;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_LeanLib_getModuleArray(lean_object*);
extern lean_object* l_Lake_Module_importsFacet;
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_Module_leanArtsFacet;
lean_object* l_Lake_Job_mix___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_leanArtsFacet;
lean_object* l_Lake_mkRelPathString(lean_object*);
extern lean_object* l_Lake_LeanLib_staticFacet;
extern lean_object* l_Lake_LeanLib_staticExportFacet;
extern lean_object* l_Lake_Package_extraDepFacet;
extern lean_object* l_Lake_Package_keyword;
lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_extraDepFacet;
lean_object* l_instMonadST(lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lake_EquipT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__0_value;
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__1 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__1_value;
static const lean_ctor_object l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2_value;
static const lean_closure_object l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__3 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__3_value;
static const lean_ctor_object l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2_value),((lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__4 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__4_value;
LEAN_EXPORT const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLib_leanArtsFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__0 = (const lean_object*)&l_Lake_LeanLib_leanArtsFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_LeanLib_leanArtsFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__1 = (const lean_object*)&l_Lake_LeanLib_leanArtsFacetConfig___closed__1_value;
static lean_once_cell_t l_Lake_LeanLib_leanArtsFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___closed__0_value;
static const lean_array_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___closed__1 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object**);
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0;
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ":static"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1_value;
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " (without exports)"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2_value;
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " (with exports)"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "type mismatch in target '"};
static const lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0_value;
static const lean_string_object l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "': expected '"};
static const lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1_value;
static lean_once_cell_t l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2;
static const lean_string_object l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "', got "};
static const lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3 = (const lean_object*)&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3_value;
static const lean_string_object l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4 = (const lean_object*)&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4_value;
static const lean_string_object l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unknown"};
static const lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5 = (const lean_object*)&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLib_staticFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLib_staticFacetConfig___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLib_staticFacetConfig___closed__0 = (const lean_object*)&l_Lake_LeanLib_staticFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_LeanLib_staticFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLib_staticFacetConfig___closed__1 = (const lean_object*)&l_Lake_LeanLib_staticFacetConfig___closed__1_value;
static lean_once_cell_t l_Lake_LeanLib_staticFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_staticFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig;
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLib_staticExportFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLib_staticExportFacetConfig___closed__0 = (const lean_object*)&l_Lake_LeanLib_staticExportFacetConfig___closed__0_value;
static lean_once_cell_t l_Lake_LeanLib_staticExportFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_staticExportFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig;
static lean_once_cell_t l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0 = (const lean_object*)&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0_value;
static lean_once_cell_t l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ":shared"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLib_sharedFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLib_sharedFacetConfig___closed__0 = (const lean_object*)&l_Lake_LeanLib_sharedFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_LeanLib_sharedFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLib_sharedFacetConfig___closed__1 = (const lean_object*)&l_Lake_LeanLib_sharedFacetConfig___closed__1_value;
static lean_once_cell_t l_Lake_LeanLib_sharedFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_sharedFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0_value;
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ":extraDep"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLib_extraDepFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLib_extraDepFacetConfig___closed__0 = (const lean_object*)&l_Lake_LeanLib_extraDepFacetConfig___closed__0_value;
static lean_once_cell_t l_Lake_LeanLib_extraDepFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_extraDepFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepFacetConfig;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "<collection>"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLib_defaultFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLib_defaultFacetConfig___closed__0 = (const lean_object*)&l_Lake_LeanLib_defaultFacetConfig___closed__0_value;
static lean_once_cell_t l_Lake_LeanLib_defaultFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_defaultFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacetConfig;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_LeanLib_initFacetConfigs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__0;
static lean_once_cell_t l_Lake_LeanLib_initFacetConfigs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__1;
static lean_once_cell_t l_Lake_LeanLib_initFacetConfigs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__2;
static lean_once_cell_t l_Lake_LeanLib_initFacetConfigs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__3;
static lean_once_cell_t l_Lake_LeanLib_initFacetConfigs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__4;
static lean_once_cell_t l_Lake_LeanLib_initFacetConfigs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__5;
static lean_once_cell_t l_Lake_LeanLib_initFacetConfigs___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__6;
LEAN_EXPORT lean_object* l_Lake_LeanLib_initFacetConfigs;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initLibraryFacetConfigs;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_tail_5_; lean_object* v_name_6_; lean_object* v_name_7_; uint8_t v___x_8_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v_name_6_ = lean_ctor_get(v_key_4_, 1);
v_name_7_ = lean_ctor_get(v_a_1_, 1);
v___x_8_ = lean_name_eq(v_name_6_, v_name_7_);
if (v___x_8_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec_ref(v_a_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_14_; uint64_t v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(1723u);
v___x_15_ = lean_uint64_of_nat(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
return v_x_16_;
}
else
{
lean_object* v_key_18_; lean_object* v_value_19_; lean_object* v_tail_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_47_; 
v_key_18_ = lean_ctor_get(v_x_17_, 0);
v_value_19_ = lean_ctor_get(v_x_17_, 1);
v_tail_20_ = lean_ctor_get(v_x_17_, 2);
v_isSharedCheck_47_ = !lean_is_exclusive(v_x_17_);
if (v_isSharedCheck_47_ == 0)
{
v___x_22_ = v_x_17_;
v_isShared_23_ = v_isSharedCheck_47_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_tail_20_);
lean_inc(v_value_19_);
lean_inc(v_key_18_);
lean_dec(v_x_17_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_47_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v_name_24_; lean_object* v___x_25_; uint64_t v___y_27_; 
v_name_24_ = lean_ctor_get(v_key_18_, 1);
v___x_25_ = lean_array_get_size(v_x_16_);
if (lean_obj_tag(v_name_24_) == 0)
{
uint64_t v___x_45_; 
v___x_45_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0);
v___y_27_ = v___x_45_;
goto v___jp_26_;
}
else
{
uint64_t v_hash_46_; 
v_hash_46_ = lean_ctor_get_uint64(v_name_24_, sizeof(void*)*2);
v___y_27_ = v_hash_46_;
goto v___jp_26_;
}
v___jp_26_:
{
uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v_fold_30_; uint64_t v___x_31_; uint64_t v___x_32_; uint64_t v___x_33_; size_t v___x_34_; size_t v___x_35_; size_t v___x_36_; size_t v___x_37_; size_t v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_28_ = 32ULL;
v___x_29_ = lean_uint64_shift_right(v___y_27_, v___x_28_);
v_fold_30_ = lean_uint64_xor(v___y_27_, v___x_29_);
v___x_31_ = 16ULL;
v___x_32_ = lean_uint64_shift_right(v_fold_30_, v___x_31_);
v___x_33_ = lean_uint64_xor(v_fold_30_, v___x_32_);
v___x_34_ = lean_uint64_to_usize(v___x_33_);
v___x_35_ = lean_usize_of_nat(v___x_25_);
v___x_36_ = ((size_t)1ULL);
v___x_37_ = lean_usize_sub(v___x_35_, v___x_36_);
v___x_38_ = lean_usize_land(v___x_34_, v___x_37_);
v___x_39_ = lean_array_uget_borrowed(v_x_16_, v___x_38_);
lean_inc(v___x_39_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 2, v___x_39_);
v___x_41_ = v___x_22_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_key_18_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_value_19_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v___x_39_);
v___x_41_ = v_reuseFailAlloc_44_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; 
v___x_42_ = lean_array_uset(v_x_16_, v___x_38_, v___x_41_);
v_x_16_ = v___x_42_;
v_x_17_ = v_tail_20_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(lean_object* v_i_48_, lean_object* v_source_49_, lean_object* v_target_50_){
_start:
{
lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_51_ = lean_array_get_size(v_source_49_);
v___x_52_ = lean_nat_dec_lt(v_i_48_, v___x_51_);
if (v___x_52_ == 0)
{
lean_dec_ref(v_source_49_);
lean_dec(v_i_48_);
return v_target_50_;
}
else
{
lean_object* v_es_53_; lean_object* v___x_54_; lean_object* v_source_55_; lean_object* v_target_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_es_53_ = lean_array_fget(v_source_49_, v_i_48_);
v___x_54_ = lean_box(0);
v_source_55_ = lean_array_fset(v_source_49_, v_i_48_, v___x_54_);
v_target_56_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(v_target_50_, v_es_53_);
v___x_57_ = lean_unsigned_to_nat(1u);
v___x_58_ = lean_nat_add(v_i_48_, v___x_57_);
lean_dec(v_i_48_);
v_i_48_ = v___x_58_;
v_source_49_ = v_source_55_;
v_target_50_ = v_target_56_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(lean_object* v_data_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v_nbuckets_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_61_ = lean_array_get_size(v_data_60_);
v___x_62_ = lean_unsigned_to_nat(2u);
v_nbuckets_63_ = lean_nat_mul(v___x_61_, v___x_62_);
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_box(0);
v___x_66_ = lean_mk_array(v_nbuckets_63_, v___x_65_);
v___x_67_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(v___x_64_, v_data_60_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(lean_object* v_m_68_, lean_object* v_a_69_, lean_object* v_b_70_){
_start:
{
lean_object* v_size_71_; lean_object* v_buckets_72_; lean_object* v_name_73_; lean_object* v___x_74_; uint64_t v___y_76_; 
v_size_71_ = lean_ctor_get(v_m_68_, 0);
v_buckets_72_ = lean_ctor_get(v_m_68_, 1);
v_name_73_ = lean_ctor_get(v_a_69_, 1);
v___x_74_ = lean_array_get_size(v_buckets_72_);
if (lean_obj_tag(v_name_73_) == 0)
{
uint64_t v___x_113_; 
v___x_113_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0);
v___y_76_ = v___x_113_;
goto v___jp_75_;
}
else
{
uint64_t v_hash_114_; 
v_hash_114_ = lean_ctor_get_uint64(v_name_73_, sizeof(void*)*2);
v___y_76_ = v_hash_114_;
goto v___jp_75_;
}
v___jp_75_:
{
uint64_t v___x_77_; uint64_t v___x_78_; uint64_t v_fold_79_; uint64_t v___x_80_; uint64_t v___x_81_; uint64_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; size_t v___x_86_; size_t v___x_87_; lean_object* v_bkt_88_; uint8_t v___x_89_; 
v___x_77_ = 32ULL;
v___x_78_ = lean_uint64_shift_right(v___y_76_, v___x_77_);
v_fold_79_ = lean_uint64_xor(v___y_76_, v___x_78_);
v___x_80_ = 16ULL;
v___x_81_ = lean_uint64_shift_right(v_fold_79_, v___x_80_);
v___x_82_ = lean_uint64_xor(v_fold_79_, v___x_81_);
v___x_83_ = lean_uint64_to_usize(v___x_82_);
v___x_84_ = lean_usize_of_nat(v___x_74_);
v___x_85_ = ((size_t)1ULL);
v___x_86_ = lean_usize_sub(v___x_84_, v___x_85_);
v___x_87_ = lean_usize_land(v___x_83_, v___x_86_);
v_bkt_88_ = lean_array_uget_borrowed(v_buckets_72_, v___x_87_);
v___x_89_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_69_, v_bkt_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_110_; 
lean_inc_ref(v_buckets_72_);
lean_inc(v_size_71_);
v_isSharedCheck_110_ = !lean_is_exclusive(v_m_68_);
if (v_isSharedCheck_110_ == 0)
{
lean_object* v_unused_111_; lean_object* v_unused_112_; 
v_unused_111_ = lean_ctor_get(v_m_68_, 1);
lean_dec(v_unused_111_);
v_unused_112_ = lean_ctor_get(v_m_68_, 0);
lean_dec(v_unused_112_);
v___x_91_ = v_m_68_;
v_isShared_92_ = v_isSharedCheck_110_;
goto v_resetjp_90_;
}
else
{
lean_dec(v_m_68_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_110_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v_size_x27_94_; lean_object* v___x_95_; lean_object* v_buckets_x27_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v_size_x27_94_ = lean_nat_add(v_size_71_, v___x_93_);
lean_dec(v_size_71_);
lean_inc(v_bkt_88_);
v___x_95_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_95_, 0, v_a_69_);
lean_ctor_set(v___x_95_, 1, v_b_70_);
lean_ctor_set(v___x_95_, 2, v_bkt_88_);
v_buckets_x27_96_ = lean_array_uset(v_buckets_72_, v___x_87_, v___x_95_);
v___x_97_ = lean_unsigned_to_nat(4u);
v___x_98_ = lean_nat_mul(v_size_x27_94_, v___x_97_);
v___x_99_ = lean_unsigned_to_nat(3u);
v___x_100_ = lean_nat_div(v___x_98_, v___x_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_array_get_size(v_buckets_x27_96_);
v___x_102_ = lean_nat_dec_le(v___x_100_, v___x_101_);
lean_dec(v___x_100_);
if (v___x_102_ == 0)
{
lean_object* v_val_103_; lean_object* v___x_105_; 
v_val_103_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(v_buckets_x27_96_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v_val_103_);
lean_ctor_set(v___x_91_, 0, v_size_x27_94_);
v___x_105_ = v___x_91_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_size_x27_94_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_val_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
else
{
lean_object* v___x_108_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v_buckets_x27_96_);
lean_ctor_set(v___x_91_, 0, v_size_x27_94_);
v___x_108_ = v___x_91_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_size_x27_94_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_buckets_x27_96_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
else
{
lean_dec(v_b_70_);
lean_dec_ref(v_a_69_);
return v_m_68_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(lean_object* v_m_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_buckets_117_; lean_object* v_name_118_; lean_object* v___x_119_; uint64_t v___y_121_; 
v_buckets_117_ = lean_ctor_get(v_m_115_, 1);
v_name_118_ = lean_ctor_get(v_a_116_, 1);
v___x_119_ = lean_array_get_size(v_buckets_117_);
if (lean_obj_tag(v_name_118_) == 0)
{
uint64_t v___x_135_; 
v___x_135_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0);
v___y_121_ = v___x_135_;
goto v___jp_120_;
}
else
{
uint64_t v_hash_136_; 
v_hash_136_ = lean_ctor_get_uint64(v_name_118_, sizeof(void*)*2);
v___y_121_ = v_hash_136_;
goto v___jp_120_;
}
v___jp_120_:
{
uint64_t v___x_122_; uint64_t v___x_123_; uint64_t v_fold_124_; uint64_t v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_122_ = 32ULL;
v___x_123_ = lean_uint64_shift_right(v___y_121_, v___x_122_);
v_fold_124_ = lean_uint64_xor(v___y_121_, v___x_123_);
v___x_125_ = 16ULL;
v___x_126_ = lean_uint64_shift_right(v_fold_124_, v___x_125_);
v___x_127_ = lean_uint64_xor(v_fold_124_, v___x_126_);
v___x_128_ = lean_uint64_to_usize(v___x_127_);
v___x_129_ = lean_usize_of_nat(v___x_119_);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_sub(v___x_129_, v___x_130_);
v___x_132_ = lean_usize_land(v___x_128_, v___x_131_);
v___x_133_ = lean_array_uget_borrowed(v_buckets_117_, v___x_132_);
v___x_134_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_116_, v___x_133_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg___boxed(lean_object* v_m_137_, lean_object* v_a_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_137_, v_a_138_);
lean_dec_ref(v_a_138_);
lean_dec_ref(v_m_137_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(lean_object* v_self_141_, lean_object* v_root_142_, lean_object* v_mods_143_, lean_object* v_modSet_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_mods_153_; lean_object* v_modSet_154_; lean_object* v___y_155_; uint8_t v___x_158_; 
v___x_158_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_modSet_144_, v_root_142_);
if (v___x_158_ == 0)
{
lean_object* v_lib_159_; lean_object* v_pkg_160_; lean_object* v_name_161_; lean_object* v_keyName_162_; lean_object* v___x_163_; lean_object* v_modSet_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_lib_159_ = lean_ctor_get(v_root_142_, 0);
v_pkg_160_ = lean_ctor_get(v_lib_159_, 0);
v_name_161_ = lean_ctor_get(v_root_142_, 1);
v_keyName_162_ = lean_ctor_get(v_pkg_160_, 2);
v___x_163_ = lean_box(0);
lean_inc_ref(v_root_142_);
v_modSet_164_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_modSet_144_, v_root_142_, v___x_163_);
v___x_165_ = l_Lake_Module_importsFacet;
lean_inc(v_name_161_);
lean_inc(v_keyName_162_);
v___x_166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_166_, 0, v_keyName_162_);
lean_ctor_set(v___x_166_, 1, v_name_161_);
v___x_167_ = l_Lake_Module_keyword;
lean_inc_ref(v_root_142_);
v___x_168_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
lean_ctor_set(v___x_168_, 2, v_root_142_);
lean_ctor_set(v___x_168_, 3, v___x_165_);
lean_inc_ref(v_a_145_);
lean_inc_ref(v_a_149_);
lean_inc(v_a_148_);
lean_inc(v_a_147_);
lean_inc(v_a_146_);
v___x_169_ = lean_apply_7(v_a_145_, v___x_168_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, lean_box(0));
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v_a_171_; lean_object* v___x_172_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_a_170_);
v_a_171_ = lean_ctor_get(v___x_169_, 1);
lean_inc(v_a_171_);
lean_dec_ref(v___x_169_);
v___x_172_ = l_Lake_Job_await___redArg(v_a_170_, v_a_171_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v_a_174_; lean_object* v___x_175_; size_t v_sz_176_; size_t v___x_177_; lean_object* v___x_178_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
v_a_174_ = lean_ctor_get(v___x_172_, 1);
lean_inc(v_a_174_);
lean_dec_ref(v___x_172_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_mods_143_);
lean_ctor_set(v___x_175_, 1, v_modSet_164_);
v_sz_176_ = lean_array_size(v_a_173_);
v___x_177_ = ((size_t)0ULL);
v___x_178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_141_, v_a_173_, v_sz_176_, v___x_177_, v___x_175_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_174_);
lean_dec(v_a_173_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v_a_180_; lean_object* v_fst_181_; lean_object* v_snd_182_; lean_object* v___x_183_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
v_a_180_ = lean_ctor_get(v___x_178_, 1);
lean_inc(v_a_180_);
lean_dec_ref(v___x_178_);
v_fst_181_ = lean_ctor_get(v_a_179_, 0);
lean_inc(v_fst_181_);
v_snd_182_ = lean_ctor_get(v_a_179_, 1);
lean_inc(v_snd_182_);
lean_dec(v_a_179_);
v___x_183_ = lean_array_push(v_fst_181_, v_root_142_);
v_mods_153_ = v___x_183_;
v_modSet_154_ = v_snd_182_;
v___y_155_ = v_a_180_;
goto v___jp_152_;
}
else
{
lean_dec_ref(v_root_142_);
return v___x_178_;
}
}
else
{
lean_object* v_a_184_; lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v_modSet_164_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec_ref(v_mods_143_);
lean_dec_ref(v_root_142_);
v_a_184_ = lean_ctor_get(v___x_172_, 0);
v_a_185_ = lean_ctor_get(v___x_172_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_172_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_inc(v_a_184_);
lean_dec(v___x_172_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_184_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec_ref(v_modSet_164_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec_ref(v_mods_143_);
lean_dec_ref(v_root_142_);
v_a_193_ = lean_ctor_get(v___x_169_, 0);
v_a_194_ = lean_ctor_get(v___x_169_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_169_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_inc(v_a_193_);
lean_dec(v___x_169_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_193_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec_ref(v_root_142_);
v_mods_153_ = v_mods_143_;
v_modSet_154_ = v_modSet_144_;
v___y_155_ = v_a_150_;
goto v___jp_152_;
}
v___jp_152_:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v_mods_153_);
lean_ctor_set(v___x_156_, 1, v_modSet_154_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___y_155_);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object* v_self_202_, lean_object* v_as_203_, size_t v_sz_204_, size_t v_i_205_, lean_object* v_b_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_a_215_; lean_object* v_a_216_; uint8_t v___x_220_; 
v___x_220_ = lean_usize_dec_lt(v_i_205_, v_sz_204_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v_b_206_);
lean_ctor_set(v___x_221_, 1, v___y_212_);
return v___x_221_;
}
else
{
lean_object* v_fst_222_; lean_object* v_snd_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_238_; 
v_fst_222_ = lean_ctor_get(v_b_206_, 0);
v_snd_223_ = lean_ctor_get(v_b_206_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_b_206_);
if (v_isSharedCheck_238_ == 0)
{
v___x_225_ = v_b_206_;
v_isShared_226_ = v_isSharedCheck_238_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_snd_223_);
lean_inc(v_fst_222_);
lean_dec(v_b_206_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_238_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_a_227_; lean_object* v_lib_228_; lean_object* v_name_229_; lean_object* v_name_230_; uint8_t v___x_231_; 
v_a_227_ = lean_array_uget_borrowed(v_as_203_, v_i_205_);
v_lib_228_ = lean_ctor_get(v_a_227_, 0);
v_name_229_ = lean_ctor_get(v_lib_228_, 1);
v_name_230_ = lean_ctor_get(v_self_202_, 1);
v___x_231_ = lean_name_eq(v_name_229_, v_name_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_233_; 
if (v_isShared_226_ == 0)
{
v___x_233_ = v___x_225_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_fst_222_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_snd_223_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
v_a_215_ = v___x_233_;
v_a_216_ = v___y_212_;
goto v___jp_214_;
}
}
else
{
lean_object* v___x_235_; 
lean_del_object(v___x_225_);
lean_inc_ref(v___y_211_);
lean_inc(v___y_210_);
lean_inc(v___y_209_);
lean_inc(v___y_208_);
lean_inc_ref(v___y_207_);
lean_inc(v_a_227_);
v___x_235_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_202_, v_a_227_, v_fst_222_, v_snd_223_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v_a_237_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
v_a_237_ = lean_ctor_get(v___x_235_, 1);
lean_inc(v_a_237_);
lean_dec_ref(v___x_235_);
v_a_215_ = v_a_236_;
v_a_216_ = v_a_237_;
goto v___jp_214_;
}
else
{
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
return v___x_235_;
}
}
}
}
v___jp_214_:
{
size_t v___x_217_; size_t v___x_218_; 
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_add(v_i_205_, v___x_217_);
v_i_205_ = v___x_218_;
v_b_206_ = v_a_215_;
v___y_212_ = v_a_216_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object* v_self_239_, lean_object* v_as_240_, lean_object* v_sz_241_, lean_object* v_i_242_, lean_object* v_b_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
size_t v_sz_boxed_251_; size_t v_i_boxed_252_; lean_object* v_res_253_; 
v_sz_boxed_251_ = lean_unbox_usize(v_sz_241_);
lean_dec(v_sz_241_);
v_i_boxed_252_ = lean_unbox_usize(v_i_242_);
lean_dec(v_i_242_);
v_res_253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_239_, v_as_240_, v_sz_boxed_251_, v_i_boxed_252_, v_b_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec_ref(v_as_240_);
lean_dec_ref(v_self_239_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object* v_self_254_, lean_object* v_root_255_, lean_object* v_mods_256_, lean_object* v_modSet_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_254_, v_root_255_, v_mods_256_, v_modSet_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
lean_dec_ref(v_self_254_);
return v_res_265_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object* v_00_u03b2_266_, lean_object* v_m_267_, lean_object* v_a_268_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_267_, v_a_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object* v_00_u03b2_270_, lean_object* v_m_271_, lean_object* v_a_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(v_00_u03b2_270_, v_m_271_, v_a_272_);
lean_dec_ref(v_a_272_);
lean_dec_ref(v_m_271_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object* v_00_u03b2_275_, lean_object* v_m_276_, lean_object* v_a_277_, lean_object* v_b_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_m_276_, v_a_277_, v_b_278_);
return v___x_279_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(lean_object* v_00_u03b2_280_, lean_object* v_a_281_, lean_object* v_x_282_){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_281_, v_x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_284_, lean_object* v_a_285_, lean_object* v_x_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(v_00_u03b2_284_, v_a_285_, v_x_286_);
lean_dec(v_x_286_);
lean_dec_ref(v_a_285_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2(lean_object* v_00_u03b2_289_, lean_object* v_data_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(v_data_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_292_, lean_object* v_i_293_, lean_object* v_source_294_, lean_object* v_target_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(v_i_293_, v_source_294_, v_target_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_297_, lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(v_x_298_, v_x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(lean_object* v_self_301_, lean_object* v_as_302_, size_t v_sz_303_, size_t v_i_304_, lean_object* v_b_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
uint8_t v___x_313_; 
v___x_313_ = lean_usize_dec_lt(v_i_304_, v_sz_303_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v_b_305_);
lean_ctor_set(v___x_314_, 1, v___y_311_);
return v___x_314_;
}
else
{
lean_object* v_fst_315_; lean_object* v_snd_316_; lean_object* v_a_317_; lean_object* v___x_318_; 
v_fst_315_ = lean_ctor_get(v_b_305_, 0);
lean_inc(v_fst_315_);
v_snd_316_ = lean_ctor_get(v_b_305_, 1);
lean_inc(v_snd_316_);
lean_dec_ref(v_b_305_);
v_a_317_ = lean_array_uget_borrowed(v_as_302_, v_i_304_);
lean_inc_ref(v___y_310_);
lean_inc(v___y_309_);
lean_inc(v___y_308_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
lean_inc(v_a_317_);
v___x_318_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_301_, v_a_317_, v_fst_315_, v_snd_316_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v_a_320_; size_t v___x_321_; size_t v___x_322_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
v_a_320_ = lean_ctor_get(v___x_318_, 1);
lean_inc(v_a_320_);
lean_dec_ref(v___x_318_);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_add(v_i_304_, v___x_321_);
v_i_304_ = v___x_322_;
v_b_305_ = v_a_319_;
v___y_311_ = v_a_320_;
goto _start;
}
else
{
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0___boxed(lean_object* v_self_324_, lean_object* v_as_325_, lean_object* v_sz_326_, lean_object* v_i_327_, lean_object* v_b_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
size_t v_sz_boxed_336_; size_t v_i_boxed_337_; lean_object* v_res_338_; 
v_sz_boxed_336_ = lean_unbox_usize(v_sz_326_);
lean_dec(v_sz_326_);
v_i_boxed_337_ = lean_unbox_usize(v_i_327_);
lean_dec(v_i_327_);
v_res_338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_324_, v_as_325_, v_sz_boxed_336_, v_i_boxed_337_, v_b_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
lean_dec_ref(v_as_325_);
lean_dec_ref(v_self_324_);
return v_res_338_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1));
v___x_342_ = l_Lake_BuildTrace_nil(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(lean_object* v_self_343_, lean_object* v_mods_344_, lean_object* v_modSet_345_, lean_object* v___x_346_, lean_object* v___x_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; 
lean_inc_ref(v_self_343_);
v___x_355_ = l_Lake_LeanLib_getModuleArray(v_self_343_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; size_t v_sz_358_; size_t v___x_359_; lean_object* v___x_360_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref(v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v_mods_344_);
lean_ctor_set(v___x_357_, 1, v_modSet_345_);
v_sz_358_ = lean_array_size(v_a_356_);
v___x_359_ = ((size_t)0ULL);
v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_343_, v_a_356_, v_sz_358_, v___x_359_, v___x_357_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
lean_dec(v_a_356_);
lean_dec_ref(v_self_343_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_386_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_a_362_ = lean_ctor_get(v___x_360_, 1);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_386_ == 0)
{
v___x_364_ = v___x_360_;
v_isShared_365_ = v_isSharedCheck_386_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_386_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v_fst_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_384_; 
v_fst_366_ = lean_ctor_get(v_a_361_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_a_361_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v_a_361_, 1);
lean_dec(v_unused_385_);
v___x_368_ = v_a_361_;
v_isShared_369_ = v_isSharedCheck_384_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_fst_366_);
lean_dec(v_a_361_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_384_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_370_ = lean_mk_empty_array_with_capacity(v___x_346_);
v___x_371_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_372_ = 0;
v___x_373_ = 0;
v___x_374_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_375_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_375_, 0, v___x_370_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
lean_ctor_set(v___x_375_, 2, v___x_346_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*3, v___x_372_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*3 + 1, v___x_373_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v___x_375_);
lean_ctor_set(v___x_364_, 0, v_fst_366_);
v___x_377_ = v___x_364_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_fst_366_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_375_);
v___x_377_ = v_reuseFailAlloc_383_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_378_ = lean_task_pure(v___x_377_);
v___x_379_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_347_);
lean_ctor_set(v___x_379_, 2, v___x_371_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3, v___x_373_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v_a_362_);
lean_ctor_set(v___x_368_, 0, v___x_379_);
v___x_381_ = v___x_368_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_a_362_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v___x_347_);
lean_dec(v___x_346_);
v_a_387_ = lean_ctor_get(v___x_360_, 0);
v_a_388_ = lean_ctor_get(v___x_360_, 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_360_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_inc(v_a_387_);
lean_dec(v___x_360_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_387_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_397_; uint8_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___x_347_);
lean_dec(v___x_346_);
lean_dec_ref(v_modSet_345_);
lean_dec_ref(v_mods_344_);
lean_dec_ref(v_self_343_);
v_a_396_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_396_);
lean_dec_ref(v___x_355_);
v___x_397_ = lean_io_error_to_string(v_a_396_);
v___x_398_ = 3;
v___x_399_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*1, v___x_398_);
v___x_400_ = lean_array_get_size(v___y_353_);
v___x_401_ = lean_array_push(v___y_353_, v___x_399_);
v___x_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object* v_self_403_, lean_object* v_mods_404_, lean_object* v_modSet_405_, lean_object* v___x_406_, lean_object* v___x_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(v_self_403_, v_mods_404_, v_modSet_405_, v___x_406_, v___x_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
return v_res_415_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_box(0);
v___x_419_ = lean_unsigned_to_nat(16u);
v___x_420_ = lean_mk_array(v___x_419_, v___x_418_);
return v___x_420_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_modSet_423_; 
v___x_421_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1);
v___x_422_ = lean_unsigned_to_nat(0u);
v_modSet_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_modSet_423_, 0, v___x_422_);
lean_ctor_set(v_modSet_423_, 1, v___x_421_);
return v_modSet_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(lean_object* v_self_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v_mods_434_; lean_object* v_modSet_435_; lean_object* v___f_436_; lean_object* v___x_437_; 
v___x_432_ = lean_box(0);
v___x_433_ = lean_unsigned_to_nat(0u);
v_mods_434_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0));
v_modSet_435_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___f_436_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed), 12, 5);
lean_closure_set(v___f_436_, 0, v_self_424_);
lean_closure_set(v___f_436_, 1, v_mods_434_);
lean_closure_set(v___f_436_, 2, v_modSet_435_);
lean_closure_set(v___f_436_, 3, v___x_433_);
lean_closure_set(v___f_436_, 4, v___x_432_);
v___x_437_ = l_Lake_ensureJob___redArg(v___x_432_, v___f_436_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___boxed(lean_object* v_self_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(v_self_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_447_, size_t v_i_448_, lean_object* v_bs_449_){
_start:
{
uint8_t v___x_450_; 
v___x_450_ = lean_usize_dec_lt(v_i_448_, v_sz_447_);
if (v___x_450_ == 0)
{
return v_bs_449_;
}
else
{
lean_object* v_v_451_; lean_object* v_name_452_; lean_object* v___x_453_; lean_object* v_bs_x27_454_; lean_object* v___x_455_; lean_object* v___x_456_; size_t v___x_457_; size_t v___x_458_; lean_object* v___x_459_; 
v_v_451_ = lean_array_uget_borrowed(v_bs_449_, v_i_448_);
v_name_452_ = lean_ctor_get(v_v_451_, 1);
lean_inc(v_name_452_);
v___x_453_ = lean_unsigned_to_nat(0u);
v_bs_x27_454_ = lean_array_uset(v_bs_449_, v_i_448_, v___x_453_);
v___x_455_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_452_, v___x_450_);
v___x_456_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
v___x_457_ = ((size_t)1ULL);
v___x_458_ = lean_usize_add(v_i_448_, v___x_457_);
v___x_459_ = lean_array_uset(v_bs_x27_454_, v_i_448_, v___x_456_);
v_i_448_ = v___x_458_;
v_bs_449_ = v___x_459_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_461_, lean_object* v_i_462_, lean_object* v_bs_463_){
_start:
{
size_t v_sz_boxed_464_; size_t v_i_boxed_465_; lean_object* v_res_466_; 
v_sz_boxed_464_ = lean_unbox_usize(v_sz_461_);
lean_dec(v_sz_461_);
v_i_boxed_465_ = lean_unbox_usize(v_i_462_);
lean_dec(v_i_462_);
v_res_466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_464_, v_i_boxed_465_, v_bs_463_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(lean_object* v_a_467_){
_start:
{
size_t v_sz_468_; size_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_sz_468_ = lean_array_size(v_a_467_);
v___x_469_ = ((size_t)0ULL);
v___x_470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_468_, v___x_469_, v_a_467_);
v___x_471_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object* v_as_473_, size_t v_i_474_, size_t v_stop_475_, lean_object* v_b_476_){
_start:
{
uint8_t v___x_477_; 
v___x_477_ = lean_usize_dec_eq(v_i_474_, v_stop_475_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v_name_479_; uint8_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; size_t v___x_485_; size_t v___x_486_; 
v___x_478_ = lean_array_uget_borrowed(v_as_473_, v_i_474_);
v_name_479_ = lean_ctor_get(v___x_478_, 1);
v___x_480_ = 1;
lean_inc(v_name_479_);
v___x_481_ = l_Lean_Name_toString(v_name_479_, v___x_480_);
v___x_482_ = lean_string_append(v_b_476_, v___x_481_);
lean_dec_ref(v___x_481_);
v___x_483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_484_ = lean_string_append(v___x_482_, v___x_483_);
v___x_485_ = ((size_t)1ULL);
v___x_486_ = lean_usize_add(v_i_474_, v___x_485_);
v_i_474_ = v___x_486_;
v_b_476_ = v___x_484_;
goto _start;
}
else
{
return v_b_476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_488_, lean_object* v_i_489_, lean_object* v_stop_490_, lean_object* v_b_491_){
_start:
{
size_t v_i_boxed_492_; size_t v_stop_boxed_493_; lean_object* v_res_494_; 
v_i_boxed_492_ = lean_unbox_usize(v_i_489_);
lean_dec(v_i_489_);
v_stop_boxed_493_ = lean_unbox_usize(v_stop_490_);
lean_dec(v_stop_490_);
v_res_494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_as_488_, v_i_boxed_492_, v_stop_boxed_493_, v_b_491_);
lean_dec_ref(v_as_488_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(uint8_t v_fmt_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___y_498_; 
if (v_fmt_495_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_505_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_array_get_size(v_a_496_);
v___x_508_ = lean_nat_dec_lt(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_dec_ref(v_a_496_);
v___y_498_ = v___x_505_;
goto v___jp_497_;
}
else
{
uint8_t v___x_509_; 
v___x_509_ = lean_nat_dec_le(v___x_507_, v___x_507_);
if (v___x_509_ == 0)
{
if (v___x_508_ == 0)
{
lean_dec_ref(v_a_496_);
v___y_498_ = v___x_505_;
goto v___jp_497_;
}
else
{
size_t v___x_510_; size_t v___x_511_; lean_object* v___x_512_; 
v___x_510_ = ((size_t)0ULL);
v___x_511_ = lean_usize_of_nat(v___x_507_);
v___x_512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_496_, v___x_510_, v___x_511_, v___x_505_);
lean_dec_ref(v_a_496_);
v___y_498_ = v___x_512_;
goto v___jp_497_;
}
}
else
{
size_t v___x_513_; size_t v___x_514_; lean_object* v___x_515_; 
v___x_513_ = ((size_t)0ULL);
v___x_514_ = lean_usize_of_nat(v___x_507_);
v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_496_, v___x_513_, v___x_514_, v___x_505_);
lean_dec_ref(v_a_496_);
v___y_498_ = v___x_515_;
goto v___jp_497_;
}
}
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = l_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(v_a_496_);
v___x_517_ = l_Lean_Json_compress(v___x_516_);
return v___x_517_;
}
v___jp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_string_utf8_byte_size(v___y_498_);
lean_inc_ref(v___y_498_);
v___x_502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_502_, 0, v___y_498_);
lean_ctor_set(v___x_502_, 1, v___x_500_);
lean_ctor_set(v___x_502_, 2, v___x_501_);
v___x_503_ = l_String_Slice_Pos_prevn(v___x_502_, v___x_501_, v___x_499_);
lean_dec_ref(v___x_502_);
v___x_504_ = lean_string_utf8_extract(v___y_498_, v___x_500_, v___x_503_);
lean_dec(v___x_503_);
lean_dec_ref(v___y_498_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object* v_fmt_518_, lean_object* v_a_519_){
_start:
{
uint8_t v_fmt_boxed_520_; lean_object* v_res_521_; 
v_fmt_boxed_520_ = lean_unbox(v_fmt_518_);
v_res_521_ = l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(v_fmt_boxed_520_, v_a_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(lean_object* v_as_535_, size_t v_i_536_, size_t v_stop_537_, lean_object* v_b_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
uint8_t v___x_546_; 
v___x_546_ = lean_usize_dec_eq(v_i_536_, v_stop_537_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v_lib_548_; lean_object* v_pkg_549_; lean_object* v_name_550_; lean_object* v_keyName_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_547_ = lean_array_uget_borrowed(v_as_535_, v_i_536_);
v_lib_548_ = lean_ctor_get(v___x_547_, 0);
v_pkg_549_ = lean_ctor_get(v_lib_548_, 0);
v_name_550_ = lean_ctor_get(v___x_547_, 1);
v_keyName_551_ = lean_ctor_get(v_pkg_549_, 2);
v___x_552_ = l_Lake_Module_leanArtsFacet;
lean_inc(v_name_550_);
lean_inc(v_keyName_551_);
v___x_553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_553_, 0, v_keyName_551_);
lean_ctor_set(v___x_553_, 1, v_name_550_);
v___x_554_ = l_Lake_Module_keyword;
lean_inc(v___x_547_);
v___x_555_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
lean_ctor_set(v___x_555_, 2, v___x_547_);
lean_ctor_set(v___x_555_, 3, v___x_552_);
lean_inc_ref(v___y_539_);
lean_inc_ref(v___y_543_);
lean_inc(v___y_542_);
lean_inc(v___y_541_);
lean_inc(v___y_540_);
v___x_556_ = lean_apply_7(v___y_539_, v___x_555_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, lean_box(0));
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v_a_558_; lean_object* v___x_559_; size_t v___x_560_; size_t v___x_561_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
v_a_558_ = lean_ctor_get(v___x_556_, 1);
lean_inc(v_a_558_);
lean_dec_ref(v___x_556_);
v___x_559_ = l_Lake_Job_mix___redArg(v_b_538_, v_a_557_);
v___x_560_ = ((size_t)1ULL);
v___x_561_ = lean_usize_add(v_i_536_, v___x_560_);
v_i_536_ = v___x_561_;
v_b_538_ = v___x_559_;
v___y_544_ = v_a_558_;
goto _start;
}
else
{
lean_object* v_a_563_; lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec_ref(v_b_538_);
v_a_563_ = lean_ctor_get(v___x_556_, 0);
v_a_564_ = lean_ctor_get(v___x_556_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_556_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_inc(v_a_563_);
lean_dec(v___x_556_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_563_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
lean_object* v___x_572_; 
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_b_538_);
lean_ctor_set(v___x_572_, 1, v___y_544_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0___boxed(lean_object* v_as_573_, lean_object* v_i_574_, lean_object* v_stop_575_, lean_object* v_b_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
size_t v_i_boxed_584_; size_t v_stop_boxed_585_; lean_object* v_res_586_; 
v_i_boxed_584_ = lean_unbox_usize(v_i_574_);
lean_dec(v_i_574_);
v_stop_boxed_585_ = lean_unbox_usize(v_stop_575_);
lean_dec(v_stop_575_);
v_res_586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_as_573_, v_i_boxed_584_, v_stop_boxed_585_, v_b_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec_ref(v_as_573_);
return v_res_586_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_591_ = 0;
v___x_592_ = 0;
v___x_593_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v___x_594_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_590_);
lean_ctor_set(v___x_594_, 2, v___x_589_);
lean_ctor_set_uint8(v___x_594_, sizeof(void*)*3, v___x_592_);
lean_ctor_set_uint8(v___x_594_, sizeof(void*)*3 + 1, v___x_591_);
return v___x_594_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1);
v___x_596_ = lean_box(0);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_595_);
return v___x_597_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2);
v___x_599_ = lean_task_pure(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4(void){
_start:
{
uint8_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_600_ = 0;
v___x_601_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_602_ = lean_box(0);
v___x_603_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3);
v___x_604_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___x_602_);
lean_ctor_set(v___x_604_, 2, v___x_601_);
lean_ctor_set_uint8(v___x_604_, sizeof(void*)*3, v___x_600_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(lean_object* v_self_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_pkg_613_; lean_object* v_name_614_; lean_object* v_keyName_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_pkg_613_ = lean_ctor_get(v_self_605_, 0);
v_name_614_ = lean_ctor_get(v_self_605_, 1);
v_keyName_615_ = lean_ctor_get(v_pkg_613_, 2);
v___x_616_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_614_);
lean_inc(v_keyName_615_);
v___x_617_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_617_, 0, v_keyName_615_);
lean_ctor_set(v___x_617_, 1, v_name_614_);
v___x_618_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_619_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
lean_ctor_set(v___x_619_, 2, v_self_605_);
lean_ctor_set(v___x_619_, 3, v___x_616_);
lean_inc_ref(v_a_606_);
lean_inc_ref(v_a_610_);
lean_inc(v_a_609_);
lean_inc(v_a_608_);
lean_inc(v_a_607_);
v___x_620_ = lean_apply_7(v_a_606_, v___x_619_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, lean_box(0));
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v_a_622_; lean_object* v___x_623_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
v_a_622_ = lean_ctor_get(v___x_620_, 1);
lean_inc(v_a_622_);
lean_dec_ref(v___x_620_);
v___x_623_ = l_Lake_Job_await___redArg(v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_646_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_a_625_ = lean_ctor_get(v___x_623_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_646_ == 0)
{
v___x_627_ = v___x_623_;
v_isShared_628_ = v_isSharedCheck_646_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_646_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4);
v___x_631_ = lean_array_get_size(v_a_624_);
v___x_632_ = lean_nat_dec_lt(v___x_629_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_634_; 
lean_dec(v_a_624_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_630_);
v___x_634_ = v___x_627_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_a_625_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
else
{
uint8_t v___x_636_; 
v___x_636_ = lean_nat_dec_le(v___x_631_, v___x_631_);
if (v___x_636_ == 0)
{
if (v___x_632_ == 0)
{
lean_object* v___x_638_; 
lean_dec(v_a_624_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_630_);
v___x_638_ = v___x_627_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_a_625_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
else
{
size_t v___x_640_; size_t v___x_641_; lean_object* v___x_642_; 
lean_del_object(v___x_627_);
v___x_640_ = ((size_t)0ULL);
v___x_641_ = lean_usize_of_nat(v___x_631_);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_624_, v___x_640_, v___x_641_, v___x_630_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_625_);
lean_dec(v_a_624_);
return v___x_642_;
}
}
else
{
size_t v___x_643_; size_t v___x_644_; lean_object* v___x_645_; 
lean_del_object(v___x_627_);
v___x_643_ = ((size_t)0ULL);
v___x_644_ = lean_usize_of_nat(v___x_631_);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_624_, v___x_643_, v___x_644_, v___x_630_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_625_);
lean_dec(v_a_624_);
return v___x_645_;
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
v_a_647_ = lean_ctor_get(v___x_623_, 0);
v_a_648_ = lean_ctor_get(v___x_623_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_623_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_inc(v_a_647_);
lean_dec(v___x_623_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_647_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
else
{
lean_object* v_a_656_; lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
v_a_656_ = lean_ctor_get(v___x_620_, 0);
v_a_657_ = lean_ctor_get(v___x_620_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_620_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_inc(v_a_656_);
lean_dec(v___x_620_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_656_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___boxed(lean_object* v_self_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(v_self_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v_res_673_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_box(0);
v___x_675_ = l_Lean_Json_compress(v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(uint8_t v_fmt_676_){
_start:
{
if (v_fmt_676_ == 0)
{
lean_object* v___x_677_; 
v___x_677_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
return v___x_677_;
}
else
{
lean_object* v___x_678_; 
v___x_678_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_679_){
_start:
{
uint8_t v_fmt_boxed_680_; lean_object* v_res_681_; 
v_fmt_boxed_680_ = lean_unbox(v_fmt_679_);
v_res_681_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_boxed_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(uint8_t v_fmt_682_, lean_object* v_a_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_682_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___boxed(lean_object* v_fmt_685_, lean_object* v_a_686_){
_start:
{
uint8_t v_fmt_boxed_687_; lean_object* v_res_688_; 
v_fmt_boxed_687_ = lean_unbox(v_fmt_685_);
v_res_688_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(v_fmt_boxed_687_, v_a_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(uint8_t v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v___y_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
uint8_t v___y_68__boxed_694_; lean_object* v_res_695_; 
v___y_68__boxed_694_ = lean_unbox(v___y_692_);
v_res_695_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v___y_68__boxed_694_, v___y_693_);
return v_res_695_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_698_; uint8_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___f_698_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_699_ = 1;
v___x_700_ = l_Lake_instDataKindUnit;
v___x_701_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__1));
v___x_702_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_703_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___x_701_);
lean_ctor_set(v___x_703_, 2, v___x_700_);
lean_ctor_set(v___x_703_, 3, v___f_698_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*4, v___x_699_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*4 + 1, v___x_699_);
return v___x_703_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig(void){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = lean_obj_once(&l_Lake_LeanLib_leanArtsFacetConfig___closed__2, &l_Lake_LeanLib_leanArtsFacetConfig___closed__2_once, _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(lean_object* v_a_705_, lean_object* v_x_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lake_ModuleFacet_fetch___redArg(v_x_706_, v_a_705_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* v_a_715_, lean_object* v_x_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(v_a_715_, v_x_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t v_shouldExport_725_, lean_object* v___x_726_, lean_object* v_bs_727_, lean_object* v_a_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_lib_736_; lean_object* v_config_737_; lean_object* v_nativeFacets_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_741_; size_t v_sz_742_; size_t v___x_743_; lean_object* v___x_28000__overap_744_; lean_object* v___x_745_; 
v_lib_736_ = lean_ctor_get(v_a_728_, 0);
v_config_737_ = lean_ctor_get(v_lib_736_, 2);
v_nativeFacets_738_ = lean_ctor_get(v_config_737_, 8);
lean_inc_ref(v_nativeFacets_738_);
v___f_739_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed), 9, 1);
lean_closure_set(v___f_739_, 0, v_a_728_);
v___x_740_ = lean_box(v_shouldExport_725_);
v___x_741_ = lean_apply_1(v_nativeFacets_738_, v___x_740_);
v_sz_742_ = lean_array_size(v___x_741_);
v___x_743_ = ((size_t)0ULL);
v___x_28000__overap_744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_726_, v___f_739_, v_sz_742_, v___x_743_, v___x_741_);
v___x_745_ = lean_apply_7(v___x_28000__overap_744_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, lean_box(0));
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_755_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_a_747_ = lean_ctor_get(v___x_745_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_755_ == 0)
{
v___x_749_ = v___x_745_;
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = l_Array_append___redArg(v_bs_727_, v_a_746_);
lean_dec(v_a_746_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_751_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_a_747_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
lean_dec_ref(v_bs_727_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(lean_object* v_shouldExport_756_, lean_object* v___x_757_, lean_object* v_bs_758_, lean_object* v_a_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
uint8_t v_shouldExport_boxed_767_; lean_object* v_res_768_; 
v_shouldExport_boxed_767_ = lean_unbox(v_shouldExport_756_);
v_res_768_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(v_shouldExport_boxed_767_, v___x_757_, v_bs_758_, v_a_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(lean_object* v___x_769_, lean_object* v_pkg_770_, lean_object* v_x_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lake_Target_fetchIn___redArg(v___x_769_, v_pkg_770_, v_x_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* v___x_780_, lean_object* v_pkg_781_, lean_object* v_x_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(v___x_780_, v_pkg_781_, v_x_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object* v___x_794_, lean_object* v___x_795_, uint8_t v_shouldExport_796_, lean_object* v_config_797_, lean_object* v_config_798_, lean_object* v___x_799_, lean_object* v___f_800_, lean_object* v_dir_801_, lean_object* v_self_802_, lean_object* v___f_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; uint8_t v___y_816_; lean_object* v___y_822_; uint8_t v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v_a_829_; lean_object* v_a_830_; lean_object* v___y_874_; lean_object* v___x_886_; 
lean_inc_ref(v___y_804_);
lean_inc_ref(v___y_808_);
lean_inc(v___y_807_);
lean_inc(v___y_806_);
lean_inc(v___x_795_);
v___x_886_ = lean_apply_7(v___y_804_, v___x_794_, v___x_795_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, lean_box(0));
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v_a_888_; lean_object* v___x_889_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
v_a_888_ = lean_ctor_get(v___x_886_, 1);
lean_inc(v_a_888_);
lean_dec_ref(v___x_886_);
v___x_889_ = l_Lake_Job_await___redArg(v_a_887_, v_a_888_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
v_a_891_ = lean_ctor_get(v___x_889_, 1);
lean_inc(v_a_891_);
lean_dec_ref(v___x_889_);
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___closed__1));
v___x_894_ = lean_array_get_size(v_a_890_);
v___x_895_ = lean_nat_dec_lt(v___x_892_, v___x_894_);
if (v___x_895_ == 0)
{
lean_dec(v_a_890_);
lean_dec_ref(v___f_803_);
v_a_829_ = v___x_893_;
v_a_830_ = v_a_891_;
goto v___jp_828_;
}
else
{
uint8_t v___x_896_; 
v___x_896_ = lean_nat_dec_le(v___x_894_, v___x_894_);
if (v___x_896_ == 0)
{
if (v___x_895_ == 0)
{
lean_dec(v_a_890_);
lean_dec_ref(v___f_803_);
v_a_829_ = v___x_893_;
v_a_830_ = v_a_891_;
goto v___jp_828_;
}
else
{
size_t v___x_897_; size_t v___x_898_; lean_object* v___x_28114__overap_899_; lean_object* v___x_900_; 
v___x_897_ = ((size_t)0ULL);
v___x_898_ = lean_usize_of_nat(v___x_894_);
lean_inc_ref(v___x_799_);
v___x_28114__overap_899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_799_, v___f_803_, v_a_890_, v___x_897_, v___x_898_, v___x_893_);
lean_inc_ref(v___y_808_);
lean_inc(v___y_807_);
lean_inc(v___y_806_);
lean_inc(v___x_795_);
lean_inc_ref(v___y_804_);
v___x_900_ = lean_apply_7(v___x_28114__overap_899_, v___y_804_, v___x_795_, v___y_806_, v___y_807_, v___y_808_, v_a_891_, lean_box(0));
v___y_874_ = v___x_900_;
goto v___jp_873_;
}
}
else
{
size_t v___x_901_; size_t v___x_902_; lean_object* v___x_28117__overap_903_; lean_object* v___x_904_; 
v___x_901_ = ((size_t)0ULL);
v___x_902_ = lean_usize_of_nat(v___x_894_);
lean_inc_ref(v___x_799_);
v___x_28117__overap_903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_799_, v___f_803_, v_a_890_, v___x_901_, v___x_902_, v___x_893_);
lean_inc_ref(v___y_808_);
lean_inc(v___y_807_);
lean_inc(v___y_806_);
lean_inc(v___x_795_);
lean_inc_ref(v___y_804_);
v___x_904_ = lean_apply_7(v___x_28117__overap_903_, v___y_804_, v___x_795_, v___y_806_, v___y_807_, v___y_808_, v_a_891_, lean_box(0));
v___y_874_ = v___x_904_;
goto v___jp_873_;
}
}
}
else
{
lean_object* v_a_905_; lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_804_);
lean_dec_ref(v___f_803_);
lean_dec_ref(v_self_802_);
lean_dec_ref(v_dir_801_);
lean_dec_ref(v___f_800_);
lean_dec_ref(v___x_799_);
lean_dec_ref(v_config_797_);
lean_dec(v___x_795_);
v_a_905_ = lean_ctor_get(v___x_889_, 0);
v_a_906_ = lean_ctor_get(v___x_889_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_889_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_inc(v_a_905_);
lean_dec(v___x_889_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_905_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_804_);
lean_dec_ref(v___f_803_);
lean_dec_ref(v_self_802_);
lean_dec_ref(v_dir_801_);
lean_dec_ref(v___f_800_);
lean_dec_ref(v___x_799_);
lean_dec_ref(v_config_797_);
lean_dec(v___x_795_);
v_a_914_ = lean_ctor_get(v___x_886_, 0);
v_a_915_ = lean_ctor_get(v___x_886_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_886_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_inc(v_a_914_);
lean_dec(v___x_886_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_914_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
v___jp_811_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_817_ = l_Array_append___redArg(v___y_812_, v___y_815_);
lean_dec_ref(v___y_815_);
v___x_818_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_819_ = l_Lake_buildStaticLib(v___y_813_, v___x_817_, v___y_816_, v___y_804_, v___x_795_, v___y_806_, v___y_807_, v___y_808_, v___x_818_);
lean_dec_ref(v___x_817_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v___y_814_);
return v___x_820_;
}
v___jp_821_:
{
if (v___y_823_ == 0)
{
v___y_812_ = v___y_822_;
v___y_813_ = v___y_826_;
v___y_814_ = v___y_825_;
v___y_815_ = v___y_824_;
v___y_816_ = v___y_823_;
goto v___jp_811_;
}
else
{
uint8_t v___x_827_; 
v___x_827_ = l_System_Platform_isWindows;
if (v___x_827_ == 0)
{
v___y_812_ = v___y_822_;
v___y_813_ = v___y_826_;
v___y_814_ = v___y_825_;
v___y_815_ = v___y_824_;
v___y_816_ = v___x_827_;
goto v___jp_811_;
}
else
{
v___y_812_ = v___y_822_;
v___y_813_ = v___y_826_;
v___y_814_ = v___y_825_;
v___y_815_ = v___y_824_;
v___y_816_ = v_shouldExport_796_;
goto v___jp_811_;
}
}
}
v___jp_828_:
{
lean_object* v_toLeanConfig_831_; lean_object* v_toLeanConfig_832_; uint8_t v_bootstrap_833_; lean_object* v_buildDir_834_; lean_object* v_nativeLibDir_835_; lean_object* v_moreLinkObjs_836_; lean_object* v_moreLinkObjs_837_; lean_object* v___x_838_; size_t v_sz_839_; size_t v___x_840_; lean_object* v___x_28071__overap_841_; lean_object* v___x_842_; 
v_toLeanConfig_831_ = lean_ctor_get(v_config_797_, 1);
lean_inc_ref(v_toLeanConfig_831_);
v_toLeanConfig_832_ = lean_ctor_get(v_config_798_, 0);
v_bootstrap_833_ = lean_ctor_get_uint8(v_config_797_, sizeof(void*)*26);
v_buildDir_834_ = lean_ctor_get(v_config_797_, 5);
lean_inc_ref(v_buildDir_834_);
v_nativeLibDir_835_ = lean_ctor_get(v_config_797_, 7);
lean_inc_ref(v_nativeLibDir_835_);
lean_dec_ref(v_config_797_);
v_moreLinkObjs_836_ = lean_ctor_get(v_toLeanConfig_831_, 6);
lean_inc_ref(v_moreLinkObjs_836_);
lean_dec_ref(v_toLeanConfig_831_);
v_moreLinkObjs_837_ = lean_ctor_get(v_toLeanConfig_832_, 6);
v___x_838_ = l_Array_append___redArg(v_moreLinkObjs_836_, v_moreLinkObjs_837_);
v_sz_839_ = lean_array_size(v___x_838_);
v___x_840_ = ((size_t)0ULL);
v___x_28071__overap_841_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_799_, v___f_800_, v_sz_839_, v___x_840_, v___x_838_);
lean_inc_ref(v___y_808_);
lean_inc(v___y_807_);
lean_inc(v___y_806_);
lean_inc(v___x_795_);
lean_inc_ref(v___y_804_);
v___x_842_ = lean_apply_7(v___x_28071__overap_841_, v___y_804_, v___x_795_, v___y_806_, v___y_807_, v___y_808_, v_a_830_, lean_box(0));
if (lean_obj_tag(v___x_842_) == 0)
{
if (v_shouldExport_796_ == 0)
{
lean_object* v_a_843_; lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
v_a_844_ = lean_ctor_get(v___x_842_, 1);
lean_inc(v_a_844_);
lean_dec_ref(v___x_842_);
v___x_845_ = l_System_FilePath_normalize(v_buildDir_834_);
v___x_846_ = l_Lake_joinRelative(v_dir_801_, v___x_845_);
v___x_847_ = l_System_FilePath_normalize(v_nativeLibDir_835_);
v___x_848_ = l_Lake_joinRelative(v___x_846_, v___x_847_);
v___x_849_ = l_Lake_LeanLib_libName(v_self_802_);
v___x_850_ = l_Lake_nameToStaticLib(v___x_849_, v_shouldExport_796_);
v___x_851_ = l_Lake_joinRelative(v___x_848_, v___x_850_);
v___y_822_ = v_a_829_;
v___y_823_ = v_bootstrap_833_;
v___y_824_ = v_a_843_;
v___y_825_ = v_a_844_;
v___y_826_ = v___x_851_;
goto v___jp_821_;
}
else
{
lean_object* v_a_852_; lean_object* v_a_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_a_852_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_852_);
v_a_853_ = lean_ctor_get(v___x_842_, 1);
lean_inc(v_a_853_);
lean_dec_ref(v___x_842_);
v___x_854_ = l_System_FilePath_normalize(v_buildDir_834_);
v___x_855_ = l_Lake_joinRelative(v_dir_801_, v___x_854_);
v___x_856_ = l_System_FilePath_normalize(v_nativeLibDir_835_);
v___x_857_ = l_Lake_joinRelative(v___x_855_, v___x_856_);
v___x_858_ = l_Lake_LeanLib_libName(v_self_802_);
v___x_859_ = 0;
v___x_860_ = l_Lake_nameToStaticLib(v___x_858_, v___x_859_);
v___x_861_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___closed__0));
v___x_862_ = l_System_FilePath_addExtension(v___x_860_, v___x_861_);
v___x_863_ = l_Lake_joinRelative(v___x_857_, v___x_862_);
v___y_822_ = v_a_829_;
v___y_823_ = v_bootstrap_833_;
v___y_824_ = v_a_852_;
v___y_825_ = v_a_853_;
v___y_826_ = v___x_863_;
goto v___jp_821_;
}
}
else
{
lean_object* v_a_864_; lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v_nativeLibDir_835_);
lean_dec_ref(v_buildDir_834_);
lean_dec_ref(v_a_829_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_804_);
lean_dec_ref(v_self_802_);
lean_dec_ref(v_dir_801_);
lean_dec(v___x_795_);
v_a_864_ = lean_ctor_get(v___x_842_, 0);
v_a_865_ = lean_ctor_get(v___x_842_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_842_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_inc(v_a_864_);
lean_dec(v___x_842_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_864_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
v___jp_873_:
{
if (lean_obj_tag(v___y_874_) == 0)
{
lean_object* v_a_875_; lean_object* v_a_876_; 
v_a_875_ = lean_ctor_get(v___y_874_, 0);
lean_inc(v_a_875_);
v_a_876_ = lean_ctor_get(v___y_874_, 1);
lean_inc(v_a_876_);
lean_dec_ref(v___y_874_);
v_a_829_ = v_a_875_;
v_a_830_ = v_a_876_;
goto v___jp_828_;
}
else
{
lean_object* v_a_877_; lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_804_);
lean_dec_ref(v_self_802_);
lean_dec_ref(v_dir_801_);
lean_dec_ref(v___f_800_);
lean_dec_ref(v___x_799_);
lean_dec_ref(v_config_797_);
lean_dec(v___x_795_);
v_a_877_ = lean_ctor_get(v___y_874_, 0);
v_a_878_ = lean_ctor_get(v___y_874_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v___y_874_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___y_874_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_inc(v_a_877_);
lean_dec(v___y_874_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_877_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object** _args){
lean_object* v___x_923_ = _args[0];
lean_object* v___x_924_ = _args[1];
lean_object* v_shouldExport_925_ = _args[2];
lean_object* v_config_926_ = _args[3];
lean_object* v_config_927_ = _args[4];
lean_object* v___x_928_ = _args[5];
lean_object* v___f_929_ = _args[6];
lean_object* v_dir_930_ = _args[7];
lean_object* v_self_931_ = _args[8];
lean_object* v___f_932_ = _args[9];
lean_object* v___y_933_ = _args[10];
lean_object* v___y_934_ = _args[11];
lean_object* v___y_935_ = _args[12];
lean_object* v___y_936_ = _args[13];
lean_object* v___y_937_ = _args[14];
lean_object* v___y_938_ = _args[15];
lean_object* v___y_939_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_940_; lean_object* v_res_941_; 
v_shouldExport_boxed_940_ = lean_unbox(v_shouldExport_925_);
v_res_941_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v___x_923_, v___x_924_, v_shouldExport_boxed_940_, v_config_926_, v_config_927_, v___x_928_, v___f_929_, v_dir_930_, v_self_931_, v___f_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_934_);
lean_dec(v_config_927_);
return v_res_941_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0(void){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_instMonadST(lean_box(0));
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_946_, uint8_t v_shouldExport_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_955_; lean_object* v_toApplicative_956_; lean_object* v_toBind_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_1045_; 
v___x_955_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0);
v_toApplicative_956_ = lean_ctor_get(v___x_955_, 0);
v_toBind_957_ = lean_ctor_get(v___x_955_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_959_ = v___x_955_;
v_isShared_960_ = v_isSharedCheck_1045_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_toBind_957_);
lean_inc(v_toApplicative_956_);
lean_dec(v___x_955_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_1045_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_toFunctor_961_; lean_object* v_toPure_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1041_; 
v_toFunctor_961_ = lean_ctor_get(v_toApplicative_956_, 0);
v_toPure_962_ = lean_ctor_get(v_toApplicative_956_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_toApplicative_956_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; lean_object* v_unused_1043_; lean_object* v_unused_1044_; 
v_unused_1042_ = lean_ctor_get(v_toApplicative_956_, 4);
lean_dec(v_unused_1042_);
v_unused_1043_ = lean_ctor_get(v_toApplicative_956_, 3);
lean_dec(v_unused_1043_);
v_unused_1044_ = lean_ctor_get(v_toApplicative_956_, 2);
lean_dec(v_unused_1044_);
v___x_964_ = v_toApplicative_956_;
v_isShared_965_ = v_isSharedCheck_1041_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_toPure_962_);
lean_inc(v_toFunctor_961_);
lean_dec(v_toApplicative_956_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1041_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___f_966_; lean_object* v___f_967_; lean_object* v___f_968_; lean_object* v___f_969_; lean_object* v___x_970_; lean_object* v___f_971_; lean_object* v___x_973_; 
lean_inc(v_toBind_957_);
lean_inc(v_toPure_962_);
v___f_966_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_966_, 0, v_toPure_962_);
lean_closure_set(v___f_966_, 1, v_toBind_957_);
lean_inc(v_toBind_957_);
lean_inc(v_toPure_962_);
v___f_967_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_967_, 0, v_toPure_962_);
lean_closure_set(v___f_967_, 1, v_toBind_957_);
lean_inc_ref(v___f_966_);
lean_inc(v_toPure_962_);
v___f_968_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_968_, 0, v_toPure_962_);
lean_closure_set(v___f_968_, 1, v___f_966_);
lean_inc(v_toPure_962_);
lean_inc_ref(v_toFunctor_961_);
v___f_969_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_969_, 0, v_toFunctor_961_);
lean_closure_set(v___f_969_, 1, v_toPure_962_);
lean_closure_set(v___f_969_, 2, v_toBind_957_);
v___x_970_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_961_);
v___f_971_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_971_, 0, v_toPure_962_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 4, v___f_967_);
lean_ctor_set(v___x_964_, 3, v___f_968_);
lean_ctor_set(v___x_964_, 2, v___f_969_);
lean_ctor_set(v___x_964_, 1, v___f_971_);
lean_ctor_set(v___x_964_, 0, v___x_970_);
v___x_973_ = v___x_964_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___f_971_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v___f_969_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v___f_968_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v___f_967_);
v___x_973_ = v_reuseFailAlloc_1040_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 1, v___f_966_);
lean_ctor_set(v___x_959_, 0, v___x_973_);
v___x_975_ = v___x_959_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___f_966_);
v___x_975_ = v_reuseFailAlloc_1039_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_toBuildConfig_981_; lean_object* v_registeredJobs_982_; uint8_t v_verbosity_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___f_986_; lean_object* v___y_988_; uint8_t v___x_1034_; uint8_t v___x_1035_; 
v___x_976_ = l_ReaderT_instMonad___redArg(v___x_975_);
v___x_977_ = l_ReaderT_instMonad___redArg(v___x_976_);
v___x_978_ = l_ReaderT_instMonad___redArg(v___x_977_);
v___x_979_ = l_ReaderT_instMonad___redArg(v___x_978_);
v___x_980_ = l_Lake_EquipT_instMonad___redArg(v___x_979_);
v_toBuildConfig_981_ = lean_ctor_get(v_a_952_, 0);
v_registeredJobs_982_ = lean_ctor_get(v_a_952_, 3);
lean_inc(v_registeredJobs_982_);
v_verbosity_983_ = lean_ctor_get_uint8(v_toBuildConfig_981_, sizeof(void*)*2 + 3);
v___x_984_ = l_Lake_instDataKindFilePath;
v___x_985_ = lean_box(v_shouldExport_947_);
lean_inc_ref(v___x_980_);
v___f_986_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_986_, 0, v___x_985_);
lean_closure_set(v___f_986_, 1, v___x_980_);
v___x_1034_ = 2;
v___x_1035_ = l_Lake_instDecidableEqVerbosity(v_verbosity_983_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; 
v___x_1036_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_988_ = v___x_1036_;
goto v___jp_987_;
}
else
{
if (v_shouldExport_947_ == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_988_ = v___x_1037_;
goto v___jp_987_;
}
else
{
lean_object* v___x_1038_; 
v___x_1038_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_988_ = v___x_1038_;
goto v___jp_987_;
}
}
v___jp_987_:
{
lean_object* v_pkg_989_; lean_object* v_name_990_; lean_object* v_config_991_; lean_object* v_keyName_992_; lean_object* v_dir_993_; lean_object* v_config_994_; lean_object* v___f_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; 
v_pkg_989_ = lean_ctor_get(v_self_946_, 0);
v_name_990_ = lean_ctor_get(v_self_946_, 1);
lean_inc(v_name_990_);
v_config_991_ = lean_ctor_get(v_self_946_, 2);
lean_inc(v_config_991_);
v_keyName_992_ = lean_ctor_get(v_pkg_989_, 2);
v_dir_993_ = lean_ctor_get(v_pkg_989_, 4);
lean_inc_ref(v_dir_993_);
v_config_994_ = lean_ctor_get(v_pkg_989_, 6);
lean_inc_ref(v_config_994_);
lean_inc_ref(v_pkg_989_);
v___f_995_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_995_, 0, v___x_984_);
lean_closure_set(v___f_995_, 1, v_pkg_989_);
v___x_996_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_990_);
lean_inc(v_keyName_992_);
v___x_997_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_997_, 0, v_keyName_992_);
lean_ctor_set(v___x_997_, 1, v_name_990_);
v___x_998_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_946_);
v___x_999_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
lean_ctor_set(v___x_999_, 2, v_self_946_);
lean_ctor_set(v___x_999_, 3, v___x_996_);
lean_inc_ref(v_pkg_989_);
v___x_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_pkg_989_);
v___x_1001_ = lean_box(v_shouldExport_947_);
v___f_1002_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed), 17, 10);
lean_closure_set(v___f_1002_, 0, v___x_999_);
lean_closure_set(v___f_1002_, 1, v___x_1000_);
lean_closure_set(v___f_1002_, 2, v___x_1001_);
lean_closure_set(v___f_1002_, 3, v_config_994_);
lean_closure_set(v___f_1002_, 4, v_config_991_);
lean_closure_set(v___f_1002_, 5, v___x_980_);
lean_closure_set(v___f_1002_, 6, v___f_995_);
lean_closure_set(v___f_1002_, 7, v_dir_993_);
lean_closure_set(v___f_1002_, 8, v_self_946_);
lean_closure_set(v___f_1002_, 9, v___f_986_);
v___x_1003_ = l_Lake_ensureJob___redArg(v___x_984_, v___f_1002_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1033_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_a_1005_ = lean_ctor_get(v___x_1003_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1007_ = v___x_1003_;
v_isShared_1008_ = v_isSharedCheck_1033_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1033_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_task_1009_; lean_object* v_kind_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1031_; 
v_task_1009_ = lean_ctor_get(v_a_1004_, 0);
v_kind_1010_ = lean_ctor_get(v_a_1004_, 1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_a_1004_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v_a_1004_, 2);
lean_dec(v_unused_1032_);
v___x_1012_ = v_a_1004_;
v_isShared_1013_ = v_isSharedCheck_1031_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_kind_1010_);
lean_inc(v_task_1009_);
lean_dec(v_a_1004_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1031_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; lean_object* v_job_1022_; 
v___x_1014_ = lean_st_ref_take(v_registeredJobs_982_);
v___x_1015_ = 1;
v___x_1016_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_990_, v___x_1015_);
v___x_1017_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_1018_ = lean_string_append(v___x_1016_, v___x_1017_);
v___x_1019_ = lean_string_append(v___x_1018_, v___y_988_);
lean_dec_ref(v___y_988_);
v___x_1020_ = 0;
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 2, v___x_1019_);
v_job_1022_ = v___x_1012_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_task_1009_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_kind_1010_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v___x_1019_);
v_job_1022_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
lean_ctor_set_uint8(v_job_1022_, sizeof(void*)*3, v___x_1020_);
lean_inc_ref(v_job_1022_);
v___x_1023_ = l_Lake_Job_toOpaque___redArg(v_job_1022_);
v___x_1024_ = lean_array_push(v___x_1014_, v___x_1023_);
v___x_1025_ = lean_st_ref_set(v_registeredJobs_982_, v___x_1024_);
lean_dec(v_registeredJobs_982_);
v___x_1026_ = l_Lake_Job_renew___redArg(v_job_1022_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1026_);
v___x_1028_ = v___x_1007_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_a_1005_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
else
{
lean_dec(v_name_990_);
lean_dec_ref(v___y_988_);
lean_dec(v_registeredJobs_982_);
return v___x_1003_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1046_, lean_object* v_shouldExport_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
uint8_t v_shouldExport_boxed_1055_; lean_object* v_res_1056_; 
v_shouldExport_boxed_1055_ = lean_unbox(v_shouldExport_1047_);
v_res_1056_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1046_, v_shouldExport_boxed_1055_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1057_, lean_object* v_a_1058_){
_start:
{
if (v_fmt_1057_ == 0)
{
return v_a_1058_;
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = l_Lake_mkRelPathString(v_a_1058_);
v___x_1060_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
v___x_1061_ = l_Lean_Json_compress(v___x_1060_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1062_, lean_object* v_a_1063_){
_start:
{
uint8_t v_fmt_boxed_1064_; lean_object* v_res_1065_; 
v_fmt_boxed_1064_ = lean_unbox(v_fmt_1062_);
v_res_1065_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1064_, v_a_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_1066_, size_t v_sz_1067_, size_t v_i_1068_, lean_object* v_bs_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
uint8_t v___x_1077_; 
v___x_1077_ = lean_usize_dec_lt(v_i_1068_, v_sz_1067_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; 
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec_ref(v_a_1066_);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_bs_1069_);
lean_ctor_set(v___x_1078_, 1, v___y_1075_);
return v___x_1078_;
}
else
{
lean_object* v_v_1079_; lean_object* v___x_1080_; 
v_v_1079_ = lean_array_uget_borrowed(v_bs_1069_, v_i_1068_);
lean_inc_ref(v___y_1074_);
lean_inc(v___y_1073_);
lean_inc(v___y_1072_);
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
lean_inc_ref(v_a_1066_);
lean_inc(v_v_1079_);
v___x_1080_ = l_Lake_ModuleFacet_fetch___redArg(v_v_1079_, v_a_1066_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v_bs_x27_1084_; size_t v___x_1085_; size_t v___x_1086_; lean_object* v___x_1087_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
v_a_1082_ = lean_ctor_get(v___x_1080_, 1);
lean_inc(v_a_1082_);
lean_dec_ref(v___x_1080_);
v___x_1083_ = lean_unsigned_to_nat(0u);
v_bs_x27_1084_ = lean_array_uset(v_bs_1069_, v_i_1068_, v___x_1083_);
v___x_1085_ = ((size_t)1ULL);
v___x_1086_ = lean_usize_add(v_i_1068_, v___x_1085_);
v___x_1087_ = lean_array_uset(v_bs_x27_1084_, v_i_1068_, v_a_1081_);
v_i_1068_ = v___x_1086_;
v_bs_1069_ = v___x_1087_;
v___y_1075_ = v_a_1082_;
goto _start;
}
else
{
lean_object* v_a_1089_; lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec_ref(v_bs_1069_);
lean_dec_ref(v_a_1066_);
v_a_1089_ = lean_ctor_get(v___x_1080_, 0);
v_a_1090_ = lean_ctor_get(v___x_1080_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1080_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_inc(v_a_1089_);
lean_dec(v___x_1080_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1089_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_1098_, lean_object* v_sz_1099_, lean_object* v_i_1100_, lean_object* v_bs_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
size_t v_sz_boxed_1109_; size_t v_i_boxed_1110_; lean_object* v_res_1111_; 
v_sz_boxed_1109_ = lean_unbox_usize(v_sz_1099_);
lean_dec(v_sz_1099_);
v_i_boxed_1110_ = lean_unbox_usize(v_i_1100_);
lean_dec(v_i_1100_);
v_res_1111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_1098_, v_sz_boxed_1109_, v_i_boxed_1110_, v_bs_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(uint8_t v_shouldExport_1112_, lean_object* v_as_1113_, size_t v_i_1114_, size_t v_stop_1115_, lean_object* v_b_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_usize_dec_eq(v_i_1114_, v_stop_1115_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v_lib_1126_; lean_object* v_config_1127_; lean_object* v_nativeFacets_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; size_t v_sz_1131_; size_t v___x_1132_; lean_object* v___x_1133_; 
v___x_1125_ = lean_array_uget_borrowed(v_as_1113_, v_i_1114_);
v_lib_1126_ = lean_ctor_get(v___x_1125_, 0);
v_config_1127_ = lean_ctor_get(v_lib_1126_, 2);
v_nativeFacets_1128_ = lean_ctor_get(v_config_1127_, 8);
v___x_1129_ = lean_box(v_shouldExport_1112_);
lean_inc_ref(v_nativeFacets_1128_);
v___x_1130_ = lean_apply_1(v_nativeFacets_1128_, v___x_1129_);
v_sz_1131_ = lean_array_size(v___x_1130_);
v___x_1132_ = ((size_t)0ULL);
lean_inc_ref(v___y_1121_);
lean_inc(v___y_1120_);
lean_inc(v___y_1119_);
lean_inc(v___y_1118_);
lean_inc_ref(v___y_1117_);
lean_inc(v___x_1125_);
v___x_1133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_1125_, v_sz_1131_, v___x_1132_, v___x_1130_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v_a_1135_; lean_object* v___x_1136_; size_t v___x_1137_; size_t v___x_1138_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
v_a_1135_ = lean_ctor_get(v___x_1133_, 1);
lean_inc(v_a_1135_);
lean_dec_ref(v___x_1133_);
v___x_1136_ = l_Array_append___redArg(v_b_1116_, v_a_1134_);
lean_dec(v_a_1134_);
v___x_1137_ = ((size_t)1ULL);
v___x_1138_ = lean_usize_add(v_i_1114_, v___x_1137_);
v_i_1114_ = v___x_1138_;
v_b_1116_ = v___x_1136_;
v___y_1122_ = v_a_1135_;
goto _start;
}
else
{
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec_ref(v_b_1116_);
return v___x_1133_;
}
}
else
{
lean_object* v___x_1140_; 
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_b_1116_);
lean_ctor_set(v___x_1140_, 1, v___y_1122_);
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_shouldExport_1141_, lean_object* v_as_1142_, lean_object* v_i_1143_, lean_object* v_stop_1144_, lean_object* v_b_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
uint8_t v_shouldExport_boxed_1153_; size_t v_i_boxed_1154_; size_t v_stop_boxed_1155_; lean_object* v_res_1156_; 
v_shouldExport_boxed_1153_ = lean_unbox(v_shouldExport_1141_);
v_i_boxed_1154_ = lean_unbox_usize(v_i_1143_);
lean_dec(v_i_1143_);
v_stop_boxed_1155_ = lean_unbox_usize(v_stop_1144_);
lean_dec(v_stop_1144_);
v_res_1156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_shouldExport_boxed_1153_, v_as_1142_, v_i_boxed_1154_, v_stop_boxed_1155_, v_b_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec_ref(v_as_1142_);
return v_res_1156_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1159_; lean_object* v_name_1160_; lean_object* v___x_1161_; 
v___x_1159_ = 1;
v_name_1160_ = l_Lake_instDataKindFilePath;
v___x_1161_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1160_, v___x_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1165_, lean_object* v_self_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
uint8_t v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = 1;
lean_inc_ref_n(v_self_1166_, 2);
v___x_1175_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1165_, v_self_1166_, v_self_1166_, v___x_1174_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v_snd_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1218_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
v_snd_1177_ = lean_ctor_get(v_a_1176_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_a_1176_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v_a_1176_, 0);
lean_dec(v_unused_1219_);
v___x_1179_ = v_a_1176_;
v_isShared_1180_ = v_isSharedCheck_1218_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_snd_1177_);
lean_dec(v_a_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1218_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1216_; 
v_a_1181_ = lean_ctor_get(v___x_1175_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v___x_1175_, 0);
lean_dec(v_unused_1217_);
v___x_1183_ = v___x_1175_;
v_isShared_1184_ = v_isSharedCheck_1216_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1175_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1216_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v_kind_1185_; lean_object* v_name_1186_; lean_object* v___y_1188_; uint8_t v___x_1206_; 
v_kind_1185_ = lean_ctor_get(v_snd_1177_, 1);
v_name_1186_ = l_Lake_instDataKindFilePath;
v___x_1206_ = lean_name_eq(v_kind_1185_, v_name_1186_);
if (v___x_1206_ == 0)
{
uint8_t v___x_1207_; 
lean_inc(v_kind_1185_);
lean_del_object(v___x_1179_);
lean_dec(v_snd_1177_);
v___x_1207_ = l_Lean_Name_isAnonymous(v_kind_1185_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1208_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1209_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1185_, v___x_1174_);
v___x_1210_ = lean_string_append(v___x_1208_, v___x_1209_);
lean_dec_ref(v___x_1209_);
v___x_1211_ = lean_string_append(v___x_1210_, v___x_1208_);
v___y_1188_ = v___x_1211_;
goto v___jp_1187_;
}
else
{
lean_object* v___x_1212_; 
lean_dec(v_kind_1185_);
v___x_1212_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1188_ = v___x_1212_;
goto v___jp_1187_;
}
}
else
{
lean_object* v___x_1214_; 
lean_del_object(v___x_1183_);
lean_dec_ref(v_self_1166_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 1, v_a_1181_);
lean_ctor_set(v___x_1179_, 0, v_snd_1177_);
v___x_1214_ = v___x_1179_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_snd_1177_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_a_1181_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
v___jp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1189_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1190_ = l_Lake_PartialBuildKey_toString(v_self_1166_);
v___x_1191_ = lean_string_append(v___x_1189_, v___x_1190_);
lean_dec_ref(v___x_1190_);
v___x_1192_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1193_ = lean_string_append(v___x_1191_, v___x_1192_);
v___x_1194_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1195_ = lean_string_append(v___x_1193_, v___x_1194_);
v___x_1196_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1197_ = lean_string_append(v___x_1195_, v___x_1196_);
v___x_1198_ = lean_string_append(v___x_1197_, v___y_1188_);
lean_dec_ref(v___y_1188_);
v___x_1199_ = 3;
v___x_1200_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*1, v___x_1199_);
v___x_1201_ = lean_array_get_size(v_a_1181_);
v___x_1202_ = lean_array_push(v_a_1181_, v___x_1200_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set_tag(v___x_1183_, 1);
lean_ctor_set(v___x_1183_, 1, v___x_1202_);
lean_ctor_set(v___x_1183_, 0, v___x_1201_);
v___x_1204_ = v___x_1183_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v_self_1166_);
v_a_1220_ = lean_ctor_get(v___x_1175_, 0);
v_a_1221_ = lean_ctor_get(v___x_1175_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1175_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_inc(v_a_1220_);
lean_dec(v___x_1175_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1220_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1229_, lean_object* v_self_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1229_, v_self_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1239_, size_t v_sz_1240_, size_t v_i_1241_, lean_object* v_bs_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
uint8_t v___x_1250_; 
v___x_1250_ = lean_usize_dec_lt(v_i_1241_, v_sz_1240_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; 
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec_ref(v___x_1239_);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_bs_1242_);
lean_ctor_set(v___x_1251_, 1, v___y_1248_);
return v___x_1251_;
}
else
{
lean_object* v_v_1252_; lean_object* v___x_1253_; 
v_v_1252_ = lean_array_uget_borrowed(v_bs_1242_, v_i_1241_);
lean_inc_ref(v___y_1247_);
lean_inc(v___y_1246_);
lean_inc(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v_v_1252_);
lean_inc_ref(v___x_1239_);
v___x_1253_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1239_, v_v_1252_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v_a_1255_; lean_object* v___x_1256_; lean_object* v_bs_x27_1257_; size_t v___x_1258_; size_t v___x_1259_; lean_object* v___x_1260_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
v_a_1255_ = lean_ctor_get(v___x_1253_, 1);
lean_inc(v_a_1255_);
lean_dec_ref(v___x_1253_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v_bs_x27_1257_ = lean_array_uset(v_bs_1242_, v_i_1241_, v___x_1256_);
v___x_1258_ = ((size_t)1ULL);
v___x_1259_ = lean_usize_add(v_i_1241_, v___x_1258_);
v___x_1260_ = lean_array_uset(v_bs_x27_1257_, v_i_1241_, v_a_1254_);
v_i_1241_ = v___x_1259_;
v_bs_1242_ = v___x_1260_;
v___y_1248_ = v_a_1255_;
goto _start;
}
else
{
lean_object* v_a_1262_; lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec_ref(v_bs_1242_);
lean_dec_ref(v___x_1239_);
v_a_1262_ = lean_ctor_get(v___x_1253_, 0);
v_a_1263_ = lean_ctor_get(v___x_1253_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1253_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_inc(v_a_1262_);
lean_dec(v___x_1253_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1262_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1271_, lean_object* v_sz_1272_, lean_object* v_i_1273_, lean_object* v_bs_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
size_t v_sz_boxed_1282_; size_t v_i_boxed_1283_; lean_object* v_res_1284_; 
v_sz_boxed_1282_ = lean_unbox_usize(v_sz_1272_);
lean_dec(v_sz_1272_);
v_i_boxed_1283_ = lean_unbox_usize(v_i_1273_);
lean_dec(v_i_1273_);
v_res_1284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1271_, v_sz_boxed_1282_, v_i_boxed_1283_, v_bs_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(lean_object* v___x_1285_, lean_object* v___x_1286_, uint8_t v_shouldExport_1287_, lean_object* v_config_1288_, lean_object* v_config_1289_, lean_object* v_pkg_1290_, lean_object* v_dir_1291_, lean_object* v_self_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; uint8_t v___y_1305_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; uint8_t v___y_1314_; lean_object* v___y_1315_; lean_object* v_a_1318_; lean_object* v_a_1319_; lean_object* v___y_1362_; lean_object* v___x_1374_; 
lean_inc_ref(v___y_1293_);
lean_inc_ref(v___y_1297_);
lean_inc(v___y_1296_);
lean_inc(v___y_1295_);
lean_inc(v___x_1286_);
v___x_1374_ = lean_apply_7(v___y_1293_, v___x_1285_, v___x_1286_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, lean_box(0));
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v_a_1376_; lean_object* v___x_1377_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
v_a_1376_ = lean_ctor_get(v___x_1374_, 1);
lean_inc(v_a_1376_);
lean_dec_ref(v___x_1374_);
v___x_1377_ = l_Lake_Job_await___redArg(v_a_1375_, v_a_1376_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v_a_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
v_a_1379_ = lean_ctor_get(v___x_1377_, 1);
lean_inc(v_a_1379_);
lean_dec_ref(v___x_1377_);
v___x_1380_ = lean_unsigned_to_nat(0u);
v___x_1381_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___closed__1));
v___x_1382_ = lean_array_get_size(v_a_1378_);
v___x_1383_ = lean_nat_dec_lt(v___x_1380_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_dec(v_a_1378_);
v_a_1318_ = v___x_1381_;
v_a_1319_ = v_a_1379_;
goto v___jp_1317_;
}
else
{
uint8_t v___x_1384_; 
v___x_1384_ = lean_nat_dec_le(v___x_1382_, v___x_1382_);
if (v___x_1384_ == 0)
{
if (v___x_1383_ == 0)
{
lean_dec(v_a_1378_);
v_a_1318_ = v___x_1381_;
v_a_1319_ = v_a_1379_;
goto v___jp_1317_;
}
else
{
size_t v___x_1385_; size_t v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = ((size_t)0ULL);
v___x_1386_ = lean_usize_of_nat(v___x_1382_);
lean_inc_ref(v___y_1297_);
lean_inc(v___y_1296_);
lean_inc(v___y_1295_);
lean_inc(v___x_1286_);
lean_inc_ref(v___y_1293_);
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_shouldExport_1287_, v_a_1378_, v___x_1385_, v___x_1386_, v___x_1381_, v___y_1293_, v___x_1286_, v___y_1295_, v___y_1296_, v___y_1297_, v_a_1379_);
lean_dec(v_a_1378_);
v___y_1362_ = v___x_1387_;
goto v___jp_1361_;
}
}
else
{
size_t v___x_1388_; size_t v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = lean_usize_of_nat(v___x_1382_);
lean_inc_ref(v___y_1297_);
lean_inc(v___y_1296_);
lean_inc(v___y_1295_);
lean_inc(v___x_1286_);
lean_inc_ref(v___y_1293_);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_shouldExport_1287_, v_a_1378_, v___x_1388_, v___x_1389_, v___x_1381_, v___y_1293_, v___x_1286_, v___y_1295_, v___y_1296_, v___y_1297_, v_a_1379_);
lean_dec(v_a_1378_);
v___y_1362_ = v___x_1390_;
goto v___jp_1361_;
}
}
}
else
{
lean_object* v_a_1391_; lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1293_);
lean_dec_ref(v_self_1292_);
lean_dec_ref(v_dir_1291_);
lean_dec_ref(v_pkg_1290_);
lean_dec_ref(v_config_1288_);
lean_dec(v___x_1286_);
v_a_1391_ = lean_ctor_get(v___x_1377_, 0);
v_a_1392_ = lean_ctor_get(v___x_1377_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1377_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_inc(v_a_1391_);
lean_dec(v___x_1377_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1391_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1293_);
lean_dec_ref(v_self_1292_);
lean_dec_ref(v_dir_1291_);
lean_dec_ref(v_pkg_1290_);
lean_dec_ref(v_config_1288_);
lean_dec(v___x_1286_);
v_a_1400_ = lean_ctor_get(v___x_1374_, 0);
v_a_1401_ = lean_ctor_get(v___x_1374_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1374_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_inc(v_a_1400_);
lean_dec(v___x_1374_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1400_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
v___jp_1300_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1306_ = l_Array_append___redArg(v___y_1301_, v___y_1303_);
lean_dec_ref(v___y_1303_);
v___x_1307_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_1308_ = l_Lake_buildStaticLib(v___y_1304_, v___x_1306_, v___y_1305_, v___y_1293_, v___x_1286_, v___y_1295_, v___y_1296_, v___y_1297_, v___x_1307_);
lean_dec_ref(v___x_1306_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v___y_1302_);
return v___x_1309_;
}
v___jp_1310_:
{
if (v___y_1314_ == 0)
{
v___y_1301_ = v___y_1311_;
v___y_1302_ = v___y_1312_;
v___y_1303_ = v___y_1313_;
v___y_1304_ = v___y_1315_;
v___y_1305_ = v___y_1314_;
goto v___jp_1300_;
}
else
{
uint8_t v___x_1316_; 
v___x_1316_ = l_System_Platform_isWindows;
if (v___x_1316_ == 0)
{
v___y_1301_ = v___y_1311_;
v___y_1302_ = v___y_1312_;
v___y_1303_ = v___y_1313_;
v___y_1304_ = v___y_1315_;
v___y_1305_ = v___x_1316_;
goto v___jp_1300_;
}
else
{
v___y_1301_ = v___y_1311_;
v___y_1302_ = v___y_1312_;
v___y_1303_ = v___y_1313_;
v___y_1304_ = v___y_1315_;
v___y_1305_ = v_shouldExport_1287_;
goto v___jp_1300_;
}
}
}
v___jp_1317_:
{
lean_object* v_toLeanConfig_1320_; lean_object* v_toLeanConfig_1321_; uint8_t v_bootstrap_1322_; lean_object* v_buildDir_1323_; lean_object* v_nativeLibDir_1324_; lean_object* v_moreLinkObjs_1325_; lean_object* v_moreLinkObjs_1326_; lean_object* v___x_1327_; size_t v_sz_1328_; size_t v___x_1329_; lean_object* v___x_1330_; 
v_toLeanConfig_1320_ = lean_ctor_get(v_config_1288_, 1);
lean_inc_ref(v_toLeanConfig_1320_);
v_toLeanConfig_1321_ = lean_ctor_get(v_config_1289_, 0);
v_bootstrap_1322_ = lean_ctor_get_uint8(v_config_1288_, sizeof(void*)*26);
v_buildDir_1323_ = lean_ctor_get(v_config_1288_, 5);
lean_inc_ref(v_buildDir_1323_);
v_nativeLibDir_1324_ = lean_ctor_get(v_config_1288_, 7);
lean_inc_ref(v_nativeLibDir_1324_);
lean_dec_ref(v_config_1288_);
v_moreLinkObjs_1325_ = lean_ctor_get(v_toLeanConfig_1320_, 6);
lean_inc_ref(v_moreLinkObjs_1325_);
lean_dec_ref(v_toLeanConfig_1320_);
v_moreLinkObjs_1326_ = lean_ctor_get(v_toLeanConfig_1321_, 6);
v___x_1327_ = l_Array_append___redArg(v_moreLinkObjs_1325_, v_moreLinkObjs_1326_);
v_sz_1328_ = lean_array_size(v___x_1327_);
v___x_1329_ = ((size_t)0ULL);
lean_inc_ref(v___y_1297_);
lean_inc(v___y_1296_);
lean_inc(v___y_1295_);
lean_inc(v___x_1286_);
lean_inc_ref(v___y_1293_);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_1290_, v_sz_1328_, v___x_1329_, v___x_1327_, v___y_1293_, v___x_1286_, v___y_1295_, v___y_1296_, v___y_1297_, v_a_1319_);
if (lean_obj_tag(v___x_1330_) == 0)
{
if (v_shouldExport_1287_ == 0)
{
lean_object* v_a_1331_; lean_object* v_a_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
v_a_1332_ = lean_ctor_get(v___x_1330_, 1);
lean_inc(v_a_1332_);
lean_dec_ref(v___x_1330_);
v___x_1333_ = l_System_FilePath_normalize(v_buildDir_1323_);
v___x_1334_ = l_Lake_joinRelative(v_dir_1291_, v___x_1333_);
v___x_1335_ = l_System_FilePath_normalize(v_nativeLibDir_1324_);
v___x_1336_ = l_Lake_joinRelative(v___x_1334_, v___x_1335_);
v___x_1337_ = l_Lake_LeanLib_libName(v_self_1292_);
v___x_1338_ = l_Lake_nameToStaticLib(v___x_1337_, v_shouldExport_1287_);
v___x_1339_ = l_Lake_joinRelative(v___x_1336_, v___x_1338_);
v___y_1311_ = v_a_1318_;
v___y_1312_ = v_a_1332_;
v___y_1313_ = v_a_1331_;
v___y_1314_ = v_bootstrap_1322_;
v___y_1315_ = v___x_1339_;
goto v___jp_1310_;
}
else
{
lean_object* v_a_1340_; lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_a_1340_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1340_);
v_a_1341_ = lean_ctor_get(v___x_1330_, 1);
lean_inc(v_a_1341_);
lean_dec_ref(v___x_1330_);
v___x_1342_ = l_System_FilePath_normalize(v_buildDir_1323_);
v___x_1343_ = l_Lake_joinRelative(v_dir_1291_, v___x_1342_);
v___x_1344_ = l_System_FilePath_normalize(v_nativeLibDir_1324_);
v___x_1345_ = l_Lake_joinRelative(v___x_1343_, v___x_1344_);
v___x_1346_ = l_Lake_LeanLib_libName(v_self_1292_);
v___x_1347_ = 0;
v___x_1348_ = l_Lake_nameToStaticLib(v___x_1346_, v___x_1347_);
v___x_1349_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___closed__0));
v___x_1350_ = l_System_FilePath_addExtension(v___x_1348_, v___x_1349_);
v___x_1351_ = l_Lake_joinRelative(v___x_1345_, v___x_1350_);
v___y_1311_ = v_a_1318_;
v___y_1312_ = v_a_1341_;
v___y_1313_ = v_a_1340_;
v___y_1314_ = v_bootstrap_1322_;
v___y_1315_ = v___x_1351_;
goto v___jp_1310_;
}
}
else
{
lean_object* v_a_1352_; lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v_nativeLibDir_1324_);
lean_dec_ref(v_buildDir_1323_);
lean_dec_ref(v_a_1318_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1293_);
lean_dec_ref(v_self_1292_);
lean_dec_ref(v_dir_1291_);
lean_dec(v___x_1286_);
v_a_1352_ = lean_ctor_get(v___x_1330_, 0);
v_a_1353_ = lean_ctor_get(v___x_1330_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1330_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_inc(v_a_1352_);
lean_dec(v___x_1330_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1352_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
v___jp_1361_:
{
if (lean_obj_tag(v___y_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v_a_1364_; 
v_a_1363_ = lean_ctor_get(v___y_1362_, 0);
lean_inc(v_a_1363_);
v_a_1364_ = lean_ctor_get(v___y_1362_, 1);
lean_inc(v_a_1364_);
lean_dec_ref(v___y_1362_);
v_a_1318_ = v_a_1363_;
v_a_1319_ = v_a_1364_;
goto v___jp_1317_;
}
else
{
lean_object* v_a_1365_; lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1293_);
lean_dec_ref(v_self_1292_);
lean_dec_ref(v_dir_1291_);
lean_dec_ref(v_pkg_1290_);
lean_dec_ref(v_config_1288_);
lean_dec(v___x_1286_);
v_a_1365_ = lean_ctor_get(v___y_1362_, 0);
v_a_1366_ = lean_ctor_get(v___y_1362_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___y_1362_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___y_1362_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_inc(v_a_1365_);
lean_dec(v___y_1362_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1365_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v___x_1409_, lean_object* v___x_1410_, lean_object* v_shouldExport_1411_, lean_object* v_config_1412_, lean_object* v_config_1413_, lean_object* v_pkg_1414_, lean_object* v_dir_1415_, lean_object* v_self_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v_shouldExport_boxed_1424_; lean_object* v_res_1425_; 
v_shouldExport_boxed_1424_ = lean_unbox(v_shouldExport_1411_);
v_res_1425_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v___x_1409_, v___x_1410_, v_shouldExport_boxed_1424_, v_config_1412_, v_config_1413_, v_pkg_1414_, v_dir_1415_, v_self_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1418_);
lean_dec(v_config_1413_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_1426_, lean_object* v_self_1427_, uint8_t v_shouldExport_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v_toBuildConfig_1435_; lean_object* v_registeredJobs_1436_; uint8_t v_verbosity_1437_; lean_object* v___x_1438_; lean_object* v___y_1440_; uint8_t v___x_1485_; uint8_t v___x_1486_; 
v_toBuildConfig_1435_ = lean_ctor_get(v_a_1432_, 0);
v_registeredJobs_1436_ = lean_ctor_get(v_a_1432_, 3);
lean_inc(v_registeredJobs_1436_);
v_verbosity_1437_ = lean_ctor_get_uint8(v_toBuildConfig_1435_, sizeof(void*)*2 + 3);
v___x_1438_ = l_Lake_instDataKindFilePath;
v___x_1485_ = 2;
v___x_1486_ = l_Lake_instDecidableEqVerbosity(v_verbosity_1437_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; 
v___x_1487_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1440_ = v___x_1487_;
goto v___jp_1439_;
}
else
{
if (v_shouldExport_1428_ == 0)
{
lean_object* v___x_1488_; 
v___x_1488_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1440_ = v___x_1488_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1489_; 
v___x_1489_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_1440_ = v___x_1489_;
goto v___jp_1439_;
}
}
v___jp_1439_:
{
lean_object* v_pkg_1441_; lean_object* v_name_1442_; lean_object* v_config_1443_; lean_object* v_keyName_1444_; lean_object* v_dir_1445_; lean_object* v_config_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___f_1453_; lean_object* v___x_1454_; 
v_pkg_1441_ = lean_ctor_get(v_self_1427_, 0);
lean_inc_ref(v_pkg_1441_);
v_name_1442_ = lean_ctor_get(v_self_1427_, 1);
lean_inc(v_name_1442_);
v_config_1443_ = lean_ctor_get(v_self_1427_, 2);
lean_inc(v_config_1443_);
v_keyName_1444_ = lean_ctor_get(v_pkg_1441_, 2);
v_dir_1445_ = lean_ctor_get(v_pkg_1441_, 4);
lean_inc_ref(v_dir_1445_);
v_config_1446_ = lean_ctor_get(v_pkg_1441_, 6);
lean_inc_ref(v_config_1446_);
v___x_1447_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_1442_);
lean_inc(v_keyName_1444_);
v___x_1448_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_keyName_1444_);
lean_ctor_set(v___x_1448_, 1, v_name_1442_);
v___x_1449_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1427_);
v___x_1450_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1448_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
lean_ctor_set(v___x_1450_, 2, v_self_1427_);
lean_ctor_set(v___x_1450_, 3, v___x_1447_);
lean_inc_ref(v_pkg_1441_);
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_pkg_1441_);
v___x_1452_ = lean_box(v_shouldExport_1428_);
v___f_1453_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1453_, 0, v___x_1450_);
lean_closure_set(v___f_1453_, 1, v___x_1451_);
lean_closure_set(v___f_1453_, 2, v___x_1452_);
lean_closure_set(v___f_1453_, 3, v_config_1446_);
lean_closure_set(v___f_1453_, 4, v_config_1443_);
lean_closure_set(v___f_1453_, 5, v_pkg_1441_);
lean_closure_set(v___f_1453_, 6, v_dir_1445_);
lean_closure_set(v___f_1453_, 7, v_self_1427_);
v___x_1454_ = l_Lake_ensureJob___redArg(v___x_1438_, v___f_1453_, v___y_1426_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1484_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_a_1456_ = lean_ctor_get(v___x_1454_, 1);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1458_ = v___x_1454_;
v_isShared_1459_ = v_isSharedCheck_1484_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1484_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v_task_1460_; lean_object* v_kind_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1482_; 
v_task_1460_ = lean_ctor_get(v_a_1455_, 0);
v_kind_1461_ = lean_ctor_get(v_a_1455_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_a_1455_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v_a_1455_, 2);
lean_dec(v_unused_1483_);
v___x_1463_ = v_a_1455_;
v_isShared_1464_ = v_isSharedCheck_1482_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_kind_1461_);
lean_inc(v_task_1460_);
lean_dec(v_a_1455_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1482_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; uint8_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; lean_object* v_job_1473_; 
v___x_1465_ = lean_st_ref_take(v_registeredJobs_1436_);
v___x_1466_ = 1;
v___x_1467_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1442_, v___x_1466_);
v___x_1468_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_1469_ = lean_string_append(v___x_1467_, v___x_1468_);
v___x_1470_ = lean_string_append(v___x_1469_, v___y_1440_);
lean_dec_ref(v___y_1440_);
v___x_1471_ = 0;
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 2, v___x_1470_);
v_job_1473_ = v___x_1463_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_task_1460_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_kind_1461_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v___x_1470_);
v_job_1473_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_ctor_set_uint8(v_job_1473_, sizeof(void*)*3, v___x_1471_);
lean_inc_ref(v_job_1473_);
v___x_1474_ = l_Lake_Job_toOpaque___redArg(v_job_1473_);
v___x_1475_ = lean_array_push(v___x_1465_, v___x_1474_);
v___x_1476_ = lean_st_ref_set(v_registeredJobs_1436_, v___x_1475_);
lean_dec(v_registeredJobs_1436_);
v___x_1477_ = l_Lake_Job_renew___redArg(v_job_1473_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1477_);
v___x_1479_ = v___x_1458_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_a_1456_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
else
{
lean_dec(v_name_1442_);
lean_dec_ref(v___y_1440_);
lean_dec(v_registeredJobs_1436_);
return v___x_1454_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_1490_, lean_object* v_self_1491_, lean_object* v_shouldExport_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
uint8_t v_shouldExport_boxed_1499_; lean_object* v_res_1500_; 
v_shouldExport_boxed_1499_ = lean_unbox(v_shouldExport_1492_);
v_res_1500_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_1490_, v_self_1491_, v_shouldExport_boxed_1499_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
uint8_t v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = 0;
v___x_1510_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_1502_, v_x_1501_, v___x_1509_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
return v_res_1519_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___f_1522_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_1523_ = 1;
v___x_1524_ = l_Lake_instDataKindFilePath;
v___f_1525_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_1526_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_1527_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v___f_1525_);
lean_ctor_set(v___x_1527_, 2, v___x_1524_);
lean_ctor_set(v___x_1527_, 3, v___f_1522_);
lean_ctor_set_uint8(v___x_1527_, sizeof(void*)*4, v___x_1523_);
lean_ctor_set_uint8(v___x_1527_, sizeof(void*)*4 + 1, v___x_1523_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
uint8_t v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = 1;
v___x_1538_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_1530_, v_x_1529_, v___x_1537_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v_res_1547_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___f_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___f_1549_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_1550_ = 1;
v___x_1551_ = l_Lake_instDataKindFilePath;
v___f_1552_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_1553_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_1554_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v___f_1552_);
lean_ctor_set(v___x_1554_, 2, v___x_1551_);
lean_ctor_set(v___x_1554_, 3, v___f_1549_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*4, v___x_1550_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*4 + 1, v___x_1550_);
return v___x_1554_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_1555_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_1556_; lean_object* v_name_1557_; lean_object* v___x_1558_; 
v___x_1556_ = 1;
v_name_1557_ = l_Lake_instDataKindDynlib;
v___x_1558_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1557_, v___x_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_1559_, lean_object* v_self_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
uint8_t v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = 1;
lean_inc_ref_n(v_self_1560_, 2);
v___x_1569_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1559_, v_self_1560_, v_self_1560_, v___x_1568_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v_snd_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1612_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
v_snd_1571_ = lean_ctor_get(v_a_1570_, 1);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_a_1570_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v_a_1570_, 0);
lean_dec(v_unused_1613_);
v___x_1573_ = v_a_1570_;
v_isShared_1574_ = v_isSharedCheck_1612_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_snd_1571_);
lean_dec(v_a_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1612_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1610_; 
v_a_1575_ = lean_ctor_get(v___x_1569_, 1);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; 
v_unused_1611_ = lean_ctor_get(v___x_1569_, 0);
lean_dec(v_unused_1611_);
v___x_1577_ = v___x_1569_;
v_isShared_1578_ = v_isSharedCheck_1610_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1569_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1610_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v_kind_1579_; lean_object* v_name_1580_; lean_object* v___y_1582_; uint8_t v___x_1600_; 
v_kind_1579_ = lean_ctor_get(v_snd_1571_, 1);
v_name_1580_ = l_Lake_instDataKindDynlib;
v___x_1600_ = lean_name_eq(v_kind_1579_, v_name_1580_);
if (v___x_1600_ == 0)
{
uint8_t v___x_1601_; 
lean_inc(v_kind_1579_);
lean_del_object(v___x_1573_);
lean_dec(v_snd_1571_);
v___x_1601_ = l_Lean_Name_isAnonymous(v_kind_1579_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1602_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1603_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1579_, v___x_1568_);
v___x_1604_ = lean_string_append(v___x_1602_, v___x_1603_);
lean_dec_ref(v___x_1603_);
v___x_1605_ = lean_string_append(v___x_1604_, v___x_1602_);
v___y_1582_ = v___x_1605_;
goto v___jp_1581_;
}
else
{
lean_object* v___x_1606_; 
lean_dec(v_kind_1579_);
v___x_1606_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1582_ = v___x_1606_;
goto v___jp_1581_;
}
}
else
{
lean_object* v___x_1608_; 
lean_del_object(v___x_1577_);
lean_dec_ref(v_self_1560_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 1, v_a_1575_);
lean_ctor_set(v___x_1573_, 0, v_snd_1571_);
v___x_1608_ = v___x_1573_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_snd_1571_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_a_1575_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
v___jp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1583_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1584_ = l_Lake_PartialBuildKey_toString(v_self_1560_);
v___x_1585_ = lean_string_append(v___x_1583_, v___x_1584_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1587_ = lean_string_append(v___x_1585_, v___x_1586_);
v___x_1588_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
v___x_1589_ = lean_string_append(v___x_1587_, v___x_1588_);
v___x_1590_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1591_ = lean_string_append(v___x_1589_, v___x_1590_);
v___x_1592_ = lean_string_append(v___x_1591_, v___y_1582_);
lean_dec_ref(v___y_1582_);
v___x_1593_ = 3;
v___x_1594_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set_uint8(v___x_1594_, sizeof(void*)*1, v___x_1593_);
v___x_1595_ = lean_array_get_size(v_a_1575_);
v___x_1596_ = lean_array_push(v_a_1575_, v___x_1594_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set_tag(v___x_1577_, 1);
lean_ctor_set(v___x_1577_, 1, v___x_1596_);
lean_ctor_set(v___x_1577_, 0, v___x_1595_);
v___x_1598_ = v___x_1577_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v_self_1560_);
v_a_1614_ = lean_ctor_get(v___x_1569_, 0);
v_a_1615_ = lean_ctor_get(v___x_1569_, 1);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1569_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_inc(v_a_1614_);
lean_dec(v___x_1569_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1614_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_1623_, lean_object* v_self_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_1623_, v_self_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
return v_res_1632_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_1636_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v___x_1635_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_1639_, lean_object* v_as_1640_, size_t v_i_1641_, size_t v_stop_1642_, lean_object* v_b_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
uint8_t v___x_1651_; 
v___x_1651_ = lean_usize_dec_eq(v_i_1641_, v_stop_1642_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_array_uget_borrowed(v_as_1640_, v_i_1641_);
lean_inc_ref(v___y_1648_);
lean_inc(v___y_1647_);
lean_inc(v___y_1646_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v___x_1652_);
lean_inc_ref(v___x_1639_);
v___x_1653_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1639_, v___x_1652_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v_a_1655_; lean_object* v___x_1656_; size_t v___x_1657_; size_t v___x_1658_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
v_a_1655_ = lean_ctor_get(v___x_1653_, 1);
lean_inc(v_a_1655_);
lean_dec_ref(v___x_1653_);
v___x_1656_ = lean_array_push(v_b_1643_, v_a_1654_);
v___x_1657_ = ((size_t)1ULL);
v___x_1658_ = lean_usize_add(v_i_1641_, v___x_1657_);
v_i_1641_ = v___x_1658_;
v_b_1643_ = v___x_1656_;
v___y_1649_ = v_a_1655_;
goto _start;
}
else
{
lean_object* v_a_1660_; lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec_ref(v_b_1643_);
lean_dec_ref(v___x_1639_);
v_a_1660_ = lean_ctor_get(v___x_1653_, 0);
v_a_1661_ = lean_ctor_get(v___x_1653_, 1);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1653_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_inc(v_a_1660_);
lean_dec(v___x_1653_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1660_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v___x_1669_; 
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec_ref(v___x_1639_);
v___x_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1669_, 0, v_b_1643_);
lean_ctor_set(v___x_1669_, 1, v___y_1649_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_1670_, lean_object* v_as_1671_, lean_object* v_i_1672_, lean_object* v_stop_1673_, lean_object* v_b_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
size_t v_i_boxed_1682_; size_t v_stop_boxed_1683_; lean_object* v_res_1684_; 
v_i_boxed_1682_ = lean_unbox_usize(v_i_1672_);
lean_dec(v_i_1672_);
v_stop_boxed_1683_ = lean_unbox_usize(v_stop_1673_);
lean_dec(v_stop_1673_);
v_res_1684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_1670_, v_as_1671_, v_i_boxed_1682_, v_stop_boxed_1683_, v_b_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec_ref(v_as_1671_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_toHashSet_1687_; lean_object* v_toArray_1688_; uint8_t v___x_1689_; 
v_toHashSet_1687_ = lean_ctor_get(v_self_1685_, 0);
v_toArray_1688_ = lean_ctor_get(v_self_1685_, 1);
v___x_1689_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_1687_, v_a_1686_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1699_; 
lean_inc_ref(v_toArray_1688_);
lean_inc_ref(v_toHashSet_1687_);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_self_1685_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; lean_object* v_unused_1701_; 
v_unused_1700_ = lean_ctor_get(v_self_1685_, 1);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_self_1685_, 0);
lean_dec(v_unused_1701_);
v___x_1691_ = v_self_1685_;
v_isShared_1692_ = v_isSharedCheck_1699_;
goto v_resetjp_1690_;
}
else
{
lean_dec(v_self_1685_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1699_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1693_ = lean_box(0);
lean_inc_ref(v_a_1686_);
v___x_1694_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_1687_, v_a_1686_, v___x_1693_);
v___x_1695_ = lean_array_push(v_toArray_1688_, v_a_1686_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 1, v___x_1695_);
lean_ctor_set(v___x_1691_, 0, v___x_1694_);
v___x_1697_ = v___x_1691_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
else
{
lean_dec_ref(v_a_1686_);
return v_self_1685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_1702_, size_t v_i_1703_, size_t v_stop_1704_, lean_object* v_b_1705_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = lean_usize_dec_eq(v_i_1703_, v_stop_1704_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; lean_object* v___x_1708_; size_t v___x_1709_; size_t v___x_1710_; 
v___x_1707_ = lean_array_uget_borrowed(v_as_1702_, v_i_1703_);
lean_inc(v___x_1707_);
v___x_1708_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_1705_, v___x_1707_);
v___x_1709_ = ((size_t)1ULL);
v___x_1710_ = lean_usize_add(v_i_1703_, v___x_1709_);
v_i_1703_ = v___x_1710_;
v_b_1705_ = v___x_1708_;
goto _start;
}
else
{
return v_b_1705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_1712_, lean_object* v_i_1713_, lean_object* v_stop_1714_, lean_object* v_b_1715_){
_start:
{
size_t v_i_boxed_1716_; size_t v_stop_boxed_1717_; lean_object* v_res_1718_; 
v_i_boxed_1716_ = lean_unbox_usize(v_i_1713_);
lean_dec(v_i_1713_);
v_stop_boxed_1717_ = lean_unbox_usize(v_stop_1714_);
lean_dec(v_stop_1714_);
v_res_1718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_1712_, v_i_boxed_1716_, v_stop_boxed_1717_, v_b_1715_);
lean_dec_ref(v_as_1712_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_1719_, lean_object* v_arr_1720_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1721_ = lean_unsigned_to_nat(0u);
v___x_1722_ = lean_array_get_size(v_arr_1720_);
v___x_1723_ = lean_nat_dec_lt(v___x_1721_, v___x_1722_);
if (v___x_1723_ == 0)
{
return v_self_1719_;
}
else
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_nat_dec_le(v___x_1722_, v___x_1722_);
if (v___x_1724_ == 0)
{
if (v___x_1723_ == 0)
{
return v_self_1719_;
}
else
{
size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = ((size_t)0ULL);
v___x_1726_ = lean_usize_of_nat(v___x_1722_);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_1720_, v___x_1725_, v___x_1726_, v_self_1719_);
return v___x_1727_;
}
}
else
{
size_t v___x_1728_; size_t v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = ((size_t)0ULL);
v___x_1729_ = lean_usize_of_nat(v___x_1722_);
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_1720_, v___x_1728_, v___x_1729_, v_self_1719_);
return v___x_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object* v_self_1731_, lean_object* v_arr_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_self_1731_, v_arr_1732_);
lean_dec_ref(v_arr_1732_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object* v_as_1734_, size_t v_i_1735_, size_t v_stop_1736_, lean_object* v_b_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_usize_dec_eq(v_i_1735_, v_stop_1736_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v_lib_1747_; lean_object* v_pkg_1748_; lean_object* v_name_1749_; lean_object* v_keyName_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1746_ = lean_array_uget_borrowed(v_as_1734_, v_i_1735_);
v_lib_1747_ = lean_ctor_get(v___x_1746_, 0);
v_pkg_1748_ = lean_ctor_get(v_lib_1747_, 0);
v_name_1749_ = lean_ctor_get(v___x_1746_, 1);
v_keyName_1750_ = lean_ctor_get(v_pkg_1748_, 2);
v___x_1751_ = l_Lake_Module_transImportsFacet;
lean_inc(v_name_1749_);
lean_inc(v_keyName_1750_);
v___x_1752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1752_, 0, v_keyName_1750_);
lean_ctor_set(v___x_1752_, 1, v_name_1749_);
v___x_1753_ = l_Lake_Module_keyword;
lean_inc(v___x_1746_);
v___x_1754_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
lean_ctor_set(v___x_1754_, 2, v___x_1746_);
lean_ctor_set(v___x_1754_, 3, v___x_1751_);
lean_inc_ref(v___y_1738_);
lean_inc_ref(v___y_1742_);
lean_inc(v___y_1741_);
lean_inc(v___y_1740_);
lean_inc(v___y_1739_);
v___x_1755_ = lean_apply_7(v___y_1738_, v___x_1754_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, lean_box(0));
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v_a_1757_; lean_object* v___x_1758_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
v_a_1757_ = lean_ctor_get(v___x_1755_, 1);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1755_);
v___x_1758_ = l_Lake_Job_await___redArg(v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v_a_1760_; lean_object* v___x_1761_; size_t v___x_1762_; size_t v___x_1763_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
v_a_1760_ = lean_ctor_get(v___x_1758_, 1);
lean_inc(v_a_1760_);
lean_dec_ref(v___x_1758_);
v___x_1761_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_b_1737_, v_a_1759_);
lean_dec(v_a_1759_);
v___x_1762_ = ((size_t)1ULL);
v___x_1763_ = lean_usize_add(v_i_1735_, v___x_1762_);
v_i_1735_ = v___x_1763_;
v_b_1737_ = v___x_1761_;
v___y_1743_ = v_a_1760_;
goto _start;
}
else
{
lean_object* v_a_1765_; lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v_b_1737_);
v_a_1765_ = lean_ctor_get(v___x_1758_, 0);
v_a_1766_ = lean_ctor_get(v___x_1758_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1758_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_inc(v_a_1765_);
lean_dec(v___x_1758_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1765_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v_b_1737_);
v_a_1774_ = lean_ctor_get(v___x_1755_, 0);
v_a_1775_ = lean_ctor_get(v___x_1755_, 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1755_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_inc(v_a_1774_);
lean_dec(v___x_1755_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1774_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
else
{
lean_object* v___x_1783_; 
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v_b_1737_);
lean_ctor_set(v___x_1783_, 1, v___y_1743_);
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object* v_as_1784_, lean_object* v_i_1785_, lean_object* v_stop_1786_, lean_object* v_b_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
size_t v_i_boxed_1795_; size_t v_stop_boxed_1796_; lean_object* v_res_1797_; 
v_i_boxed_1795_ = lean_unbox_usize(v_i_1785_);
lean_dec(v_i_1785_);
v_stop_boxed_1796_ = lean_unbox_usize(v_stop_1786_);
lean_dec(v_stop_1786_);
v_res_1797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_1784_, v_i_boxed_1795_, v_stop_boxed_1796_, v_b_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec_ref(v_as_1784_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object* v_as_1798_, size_t v_i_1799_, size_t v_stop_1800_, lean_object* v_b_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
uint8_t v___x_1809_; 
v___x_1809_ = lean_usize_dec_eq(v_i_1799_, v_stop_1800_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v_pkg_1811_; lean_object* v_name_1812_; lean_object* v_keyName_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1810_ = lean_array_uget_borrowed(v_as_1798_, v_i_1799_);
v_pkg_1811_ = lean_ctor_get(v___x_1810_, 0);
v_name_1812_ = lean_ctor_get(v___x_1810_, 1);
v_keyName_1813_ = lean_ctor_get(v_pkg_1811_, 2);
v___x_1814_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_1812_);
lean_inc(v_keyName_1813_);
v___x_1815_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_keyName_1813_);
lean_ctor_set(v___x_1815_, 1, v_name_1812_);
v___x_1816_ = l_Lake_ExternLib_keyword;
lean_inc(v___x_1810_);
v___x_1817_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
lean_ctor_set(v___x_1817_, 2, v___x_1810_);
lean_ctor_set(v___x_1817_, 3, v___x_1814_);
lean_inc_ref(v___y_1802_);
lean_inc_ref(v___y_1806_);
lean_inc(v___y_1805_);
lean_inc(v___y_1804_);
lean_inc(v___y_1803_);
v___x_1818_ = lean_apply_7(v___y_1802_, v___x_1817_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, lean_box(0));
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v_a_1820_; lean_object* v___x_1821_; size_t v___x_1822_; size_t v___x_1823_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
v_a_1820_ = lean_ctor_get(v___x_1818_, 1);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1818_);
v___x_1821_ = lean_array_push(v_b_1801_, v_a_1819_);
v___x_1822_ = ((size_t)1ULL);
v___x_1823_ = lean_usize_add(v_i_1799_, v___x_1822_);
v_i_1799_ = v___x_1823_;
v_b_1801_ = v___x_1821_;
v___y_1807_ = v_a_1820_;
goto _start;
}
else
{
lean_object* v_a_1825_; lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v_b_1801_);
v_a_1825_ = lean_ctor_get(v___x_1818_, 0);
v_a_1826_ = lean_ctor_get(v___x_1818_, 1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1818_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_inc(v_a_1825_);
lean_dec(v___x_1818_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1825_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v___x_1834_; 
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v_b_1801_);
lean_ctor_set(v___x_1834_, 1, v___y_1807_);
return v___x_1834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object* v_as_1835_, lean_object* v_i_1836_, lean_object* v_stop_1837_, lean_object* v_b_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
size_t v_i_boxed_1846_; size_t v_stop_boxed_1847_; lean_object* v_res_1848_; 
v_i_boxed_1846_ = lean_unbox_usize(v_i_1836_);
lean_dec(v_i_1836_);
v_stop_boxed_1847_ = lean_unbox_usize(v_stop_1837_);
lean_dec(v_stop_1837_);
v_res_1848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_1835_, v_i_boxed_1846_, v_stop_boxed_1847_, v_b_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec_ref(v_as_1835_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object* v_as_1849_, size_t v_i_1850_, size_t v_stop_1851_, lean_object* v_b_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_a_1861_; lean_object* v_a_1862_; uint8_t v___x_1866_; 
v___x_1866_ = lean_usize_dec_eq(v_i_1850_, v_stop_1851_);
if (v___x_1866_ == 0)
{
lean_object* v_fst_1867_; lean_object* v_snd_1868_; lean_object* v___x_1869_; lean_object* v_lib_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1907_; 
v_fst_1867_ = lean_ctor_get(v_b_1852_, 0);
v_snd_1868_ = lean_ctor_get(v_b_1852_, 1);
v___x_1869_ = lean_array_uget(v_as_1849_, v_i_1850_);
v_lib_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1907_ == 0)
{
lean_object* v_unused_1908_; 
v_unused_1908_ = lean_ctor_get(v___x_1869_, 1);
lean_dec(v_unused_1908_);
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1907_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_lib_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1907_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_pkg_1874_; lean_object* v_name_1875_; uint8_t v___x_1876_; 
v_pkg_1874_ = lean_ctor_get(v_lib_1870_, 0);
v_name_1875_ = lean_ctor_get(v_lib_1870_, 1);
lean_inc(v_name_1875_);
v___x_1876_ = l_Lean_NameSet_contains(v_fst_1867_, v_name_1875_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1904_; 
lean_inc(v_snd_1868_);
lean_inc(v_fst_1867_);
v_isSharedCheck_1904_ = !lean_is_exclusive(v_b_1852_);
if (v_isSharedCheck_1904_ == 0)
{
lean_object* v_unused_1905_; lean_object* v_unused_1906_; 
v_unused_1905_ = lean_ctor_get(v_b_1852_, 1);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v_b_1852_, 0);
lean_dec(v_unused_1906_);
v___x_1878_ = v_b_1852_;
v_isShared_1879_ = v_isSharedCheck_1904_;
goto v_resetjp_1877_;
}
else
{
lean_dec(v_b_1852_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1904_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v_keyName_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v_keyName_1880_ = lean_ctor_get(v_pkg_1874_, 2);
v___x_1881_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_1875_);
lean_inc(v_keyName_1880_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set_tag(v___x_1872_, 3);
lean_ctor_set(v___x_1872_, 1, v_name_1875_);
lean_ctor_set(v___x_1872_, 0, v_keyName_1880_);
v___x_1883_ = v___x_1872_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_keyName_1880_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_name_1875_);
v___x_1883_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_1885_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1883_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
lean_ctor_set(v___x_1885_, 2, v_lib_1870_);
lean_ctor_set(v___x_1885_, 3, v___x_1881_);
lean_inc_ref(v___y_1853_);
lean_inc_ref(v___y_1857_);
lean_inc(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc(v___y_1854_);
v___x_1886_ = lean_apply_7(v___y_1853_, v___x_1885_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, lean_box(0));
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v_a_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1892_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
v_a_1888_ = lean_ctor_get(v___x_1886_, 1);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1886_);
v___x_1889_ = lean_array_push(v_snd_1868_, v_a_1887_);
v___x_1890_ = l_Lean_NameSet_insert(v_fst_1867_, v_name_1875_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v___x_1889_);
lean_ctor_set(v___x_1878_, 0, v___x_1890_);
v___x_1892_ = v___x_1878_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___x_1889_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
v_a_1861_ = v___x_1892_;
v_a_1862_ = v_a_1888_;
goto v___jp_1860_;
}
}
else
{
lean_object* v_a_1894_; lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_del_object(v___x_1878_);
lean_dec(v_name_1875_);
lean_dec(v_snd_1868_);
lean_dec(v_fst_1867_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
v_a_1894_ = lean_ctor_get(v___x_1886_, 0);
v_a_1895_ = lean_ctor_get(v___x_1886_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1886_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_inc(v_a_1894_);
lean_dec(v___x_1886_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1894_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
}
else
{
lean_dec(v_name_1875_);
lean_del_object(v___x_1872_);
lean_dec_ref(v_lib_1870_);
v_a_1861_ = v_b_1852_;
v_a_1862_ = v___y_1858_;
goto v___jp_1860_;
}
}
}
else
{
lean_object* v___x_1909_; 
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v_b_1852_);
lean_ctor_set(v___x_1909_, 1, v___y_1858_);
return v___x_1909_;
}
v___jp_1860_:
{
size_t v___x_1863_; size_t v___x_1864_; 
v___x_1863_ = ((size_t)1ULL);
v___x_1864_ = lean_usize_add(v_i_1850_, v___x_1863_);
v_i_1850_ = v___x_1864_;
v_b_1852_ = v_a_1861_;
v___y_1858_ = v_a_1862_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object* v_as_1910_, lean_object* v_i_1911_, lean_object* v_stop_1912_, lean_object* v_b_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
size_t v_i_boxed_1921_; size_t v_stop_boxed_1922_; lean_object* v_res_1923_; 
v_i_boxed_1921_ = lean_unbox_usize(v_i_1911_);
lean_dec(v_i_1911_);
v_stop_boxed_1922_ = lean_unbox_usize(v_stop_1912_);
lean_dec(v_stop_1912_);
v_res_1923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_1910_, v_i_boxed_1921_, v_stop_boxed_1922_, v_b_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec_ref(v_as_1910_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object* v___x_1924_, lean_object* v_as_1925_, size_t v_i_1926_, size_t v_stop_1927_, lean_object* v_b_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
uint8_t v___x_1936_; 
v___x_1936_ = lean_usize_dec_eq(v_i_1926_, v_stop_1927_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_array_uget_borrowed(v_as_1925_, v_i_1926_);
lean_inc_ref(v___y_1933_);
lean_inc(v___y_1932_);
lean_inc(v___y_1931_);
lean_inc(v___y_1930_);
lean_inc_ref(v___y_1929_);
lean_inc(v___x_1937_);
lean_inc_ref(v___x_1924_);
v___x_1938_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v___x_1924_, v___x_1937_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v_a_1940_; lean_object* v___x_1941_; size_t v___x_1942_; size_t v___x_1943_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
v_a_1940_ = lean_ctor_get(v___x_1938_, 1);
lean_inc(v_a_1940_);
lean_dec_ref(v___x_1938_);
v___x_1941_ = lean_array_push(v_b_1928_, v_a_1939_);
v___x_1942_ = ((size_t)1ULL);
v___x_1943_ = lean_usize_add(v_i_1926_, v___x_1942_);
v_i_1926_ = v___x_1943_;
v_b_1928_ = v___x_1941_;
v___y_1934_ = v_a_1940_;
goto _start;
}
else
{
lean_object* v_a_1945_; lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec_ref(v_b_1928_);
lean_dec_ref(v___x_1924_);
v_a_1945_ = lean_ctor_get(v___x_1938_, 0);
v_a_1946_ = lean_ctor_get(v___x_1938_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1938_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_inc(v_a_1945_);
lean_dec(v___x_1938_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1945_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
else
{
lean_object* v___x_1954_; 
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec_ref(v___x_1924_);
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v_b_1928_);
lean_ctor_set(v___x_1954_, 1, v___y_1934_);
return v___x_1954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* v___x_1955_, lean_object* v_as_1956_, lean_object* v_i_1957_, lean_object* v_stop_1958_, lean_object* v_b_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
size_t v_i_boxed_1967_; size_t v_stop_boxed_1968_; lean_object* v_res_1969_; 
v_i_boxed_1967_ = lean_unbox_usize(v_i_1957_);
lean_dec(v_i_1957_);
v_stop_boxed_1968_ = lean_unbox_usize(v_stop_1958_);
lean_dec(v_stop_1958_);
v_res_1969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_1955_, v_as_1956_, v_i_boxed_1967_, v_stop_boxed_1968_, v_b_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec_ref(v_as_1956_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object* v___x_1970_, lean_object* v_as_1971_, size_t v_i_1972_, size_t v_stop_1973_, lean_object* v_b_1974_){
_start:
{
lean_object* v___y_1976_; uint8_t v___x_1980_; 
v___x_1980_ = lean_usize_dec_eq(v_i_1972_, v_stop_1973_);
if (v___x_1980_ == 0)
{
lean_object* v_toConfigDecl_1981_; lean_object* v_name_1982_; lean_object* v_kind_1983_; lean_object* v_config_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v_toConfigDecl_1981_ = lean_array_uget_borrowed(v_as_1971_, v_i_1972_);
v_name_1982_ = lean_ctor_get(v_toConfigDecl_1981_, 1);
v_kind_1983_ = lean_ctor_get(v_toConfigDecl_1981_, 2);
v_config_1984_ = lean_ctor_get(v_toConfigDecl_1981_, 3);
v___x_1985_ = l_Lake_ExternLib_keyword;
v___x_1986_ = lean_name_eq(v_kind_1983_, v___x_1985_);
if (v___x_1986_ == 0)
{
v___y_1976_ = v_b_1974_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_inc(v_config_1984_);
lean_inc(v_name_1982_);
lean_inc_ref(v___x_1970_);
v___x_1987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1970_);
lean_ctor_set(v___x_1987_, 1, v_name_1982_);
lean_ctor_set(v___x_1987_, 2, v_config_1984_);
v___x_1988_ = lean_array_push(v_b_1974_, v___x_1987_);
v___y_1976_ = v___x_1988_;
goto v___jp_1975_;
}
}
else
{
lean_dec_ref(v___x_1970_);
return v_b_1974_;
}
v___jp_1975_:
{
size_t v___x_1977_; size_t v___x_1978_; 
v___x_1977_ = ((size_t)1ULL);
v___x_1978_ = lean_usize_add(v_i_1972_, v___x_1977_);
v_i_1972_ = v___x_1978_;
v_b_1974_ = v___y_1976_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object* v___x_1989_, lean_object* v_as_1990_, lean_object* v_i_1991_, lean_object* v_stop_1992_, lean_object* v_b_1993_){
_start:
{
size_t v_i_boxed_1994_; size_t v_stop_boxed_1995_; lean_object* v_res_1996_; 
v_i_boxed_1994_ = lean_unbox_usize(v_i_1991_);
lean_dec(v_i_1991_);
v_stop_boxed_1995_ = lean_unbox_usize(v_stop_1992_);
lean_dec(v_stop_1992_);
v_res_1996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_1989_, v_as_1990_, v_i_boxed_1994_, v_stop_boxed_1995_, v_b_1993_);
lean_dec_ref(v_as_1990_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(lean_object* v_as_1997_, size_t v_i_1998_, size_t v_stop_1999_, lean_object* v_b_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
uint8_t v___x_2008_; 
v___x_2008_ = lean_usize_dec_eq(v_i_1998_, v_stop_1999_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v_lib_2010_; lean_object* v_config_2011_; lean_object* v_nativeFacets_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; size_t v_sz_2016_; size_t v___x_2017_; lean_object* v___x_2018_; 
v___x_2009_ = lean_array_uget_borrowed(v_as_1997_, v_i_1998_);
v_lib_2010_ = lean_ctor_get(v___x_2009_, 0);
v_config_2011_ = lean_ctor_get(v_lib_2010_, 2);
v_nativeFacets_2012_ = lean_ctor_get(v_config_2011_, 8);
v___x_2013_ = 1;
v___x_2014_ = lean_box(v___x_2013_);
lean_inc_ref(v_nativeFacets_2012_);
v___x_2015_ = lean_apply_1(v_nativeFacets_2012_, v___x_2014_);
v_sz_2016_ = lean_array_size(v___x_2015_);
v___x_2017_ = ((size_t)0ULL);
lean_inc_ref(v___y_2005_);
lean_inc(v___y_2004_);
lean_inc(v___y_2003_);
lean_inc(v___y_2002_);
lean_inc_ref(v___y_2001_);
lean_inc(v___x_2009_);
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2009_, v_sz_2016_, v___x_2017_, v___x_2015_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v_a_2020_; lean_object* v___x_2021_; size_t v___x_2022_; size_t v___x_2023_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
v_a_2020_ = lean_ctor_get(v___x_2018_, 1);
lean_inc(v_a_2020_);
lean_dec_ref(v___x_2018_);
v___x_2021_ = l_Array_append___redArg(v_b_2000_, v_a_2019_);
lean_dec(v_a_2019_);
v___x_2022_ = ((size_t)1ULL);
v___x_2023_ = lean_usize_add(v_i_1998_, v___x_2022_);
v_i_1998_ = v___x_2023_;
v_b_2000_ = v___x_2021_;
v___y_2006_ = v_a_2020_;
goto _start;
}
else
{
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec_ref(v_b_2000_);
return v___x_2018_;
}
}
else
{
lean_object* v___x_2025_; 
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
v___x_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2025_, 0, v_b_2000_);
lean_ctor_set(v___x_2025_, 1, v___y_2006_);
return v___x_2025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object* v_as_2026_, lean_object* v_i_2027_, lean_object* v_stop_2028_, lean_object* v_b_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
size_t v_i_boxed_2037_; size_t v_stop_boxed_2038_; lean_object* v_res_2039_; 
v_i_boxed_2037_ = lean_unbox_usize(v_i_2027_);
lean_dec(v_i_2027_);
v_stop_boxed_2038_ = lean_unbox_usize(v_stop_2028_);
lean_dec(v_stop_2028_);
v_res_2039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_2026_, v_i_boxed_2037_, v_stop_boxed_2038_, v_b_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec_ref(v_as_2026_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object* v___x_2040_, lean_object* v___x_2041_, lean_object* v_self_2042_, lean_object* v_dir_2043_, lean_object* v_targetDecls_2044_, lean_object* v_pkg_2045_, lean_object* v_name_2046_, lean_object* v_config_2047_, lean_object* v_config_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v_a_2064_; lean_object* v_a_2065_; lean_object* v_a_2082_; lean_object* v_a_2083_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v_a_2128_; lean_object* v_a_2129_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v_snd_2165_; lean_object* v_a_2166_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v_a_2205_; lean_object* v_a_2206_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___x_2244_; 
lean_inc_ref(v___y_2049_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2041_);
v___x_2244_ = lean_apply_7(v___y_2049_, v___x_2040_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, lean_box(0));
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v_a_2246_; lean_object* v___x_2247_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
v_a_2246_ = lean_ctor_get(v___x_2244_, 1);
lean_inc(v_a_2246_);
lean_dec_ref(v___x_2244_);
v___x_2247_ = l_Lake_Job_await___redArg(v_a_2245_, v_a_2246_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v_a_2249_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v_a_2260_; lean_object* v_a_2261_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v_a_2295_; lean_object* v_a_2296_; lean_object* v___y_2321_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
v_a_2249_ = lean_ctor_get(v___x_2247_, 1);
lean_inc(v_a_2249_);
lean_dec_ref(v___x_2247_);
v___x_2333_ = lean_unsigned_to_nat(0u);
v___x_2334_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___closed__1));
v___x_2335_ = lean_array_get_size(v_a_2248_);
v___x_2336_ = lean_nat_dec_lt(v___x_2333_, v___x_2335_);
if (v___x_2336_ == 0)
{
v_a_2295_ = v___x_2334_;
v_a_2296_ = v_a_2249_;
goto v___jp_2294_;
}
else
{
uint8_t v___x_2337_; 
v___x_2337_ = lean_nat_dec_le(v___x_2335_, v___x_2335_);
if (v___x_2337_ == 0)
{
if (v___x_2336_ == 0)
{
v_a_2295_ = v___x_2334_;
v_a_2296_ = v_a_2249_;
goto v___jp_2294_;
}
else
{
size_t v___x_2338_; size_t v___x_2339_; lean_object* v___x_2340_; 
v___x_2338_ = ((size_t)0ULL);
v___x_2339_ = lean_usize_of_nat(v___x_2335_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2041_);
lean_inc_ref(v___y_2049_);
v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_2248_, v___x_2338_, v___x_2339_, v___x_2334_, v___y_2049_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v_a_2249_);
v___y_2321_ = v___x_2340_;
goto v___jp_2320_;
}
}
else
{
size_t v___x_2341_; size_t v___x_2342_; lean_object* v___x_2343_; 
v___x_2341_ = ((size_t)0ULL);
v___x_2342_ = lean_usize_of_nat(v___x_2335_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2041_);
lean_inc_ref(v___y_2049_);
v___x_2343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_2248_, v___x_2341_, v___x_2342_, v___x_2334_, v___y_2049_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v_a_2249_);
v___y_2321_ = v___x_2343_;
goto v___jp_2320_;
}
}
v___jp_2250_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2262_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_2263_ = lean_array_get_size(v_a_2248_);
v___x_2264_ = lean_nat_dec_lt(v___y_2253_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_dec(v_a_2248_);
v___y_2195_ = v___y_2251_;
v___y_2196_ = v___y_2252_;
v___y_2197_ = v___y_2253_;
v___y_2198_ = v___y_2254_;
v___y_2199_ = v_a_2260_;
v___y_2200_ = v___y_2255_;
v___y_2201_ = v___y_2256_;
v___y_2202_ = v___y_2257_;
v___y_2203_ = v___y_2258_;
v___y_2204_ = v___y_2259_;
v_a_2205_ = v___x_2262_;
v_a_2206_ = v_a_2261_;
goto v___jp_2194_;
}
else
{
uint8_t v___x_2265_; 
v___x_2265_ = lean_nat_dec_le(v___x_2263_, v___x_2263_);
if (v___x_2265_ == 0)
{
if (v___x_2264_ == 0)
{
lean_dec(v_a_2248_);
v___y_2195_ = v___y_2251_;
v___y_2196_ = v___y_2252_;
v___y_2197_ = v___y_2253_;
v___y_2198_ = v___y_2254_;
v___y_2199_ = v_a_2260_;
v___y_2200_ = v___y_2255_;
v___y_2201_ = v___y_2256_;
v___y_2202_ = v___y_2257_;
v___y_2203_ = v___y_2258_;
v___y_2204_ = v___y_2259_;
v_a_2205_ = v___x_2262_;
v_a_2206_ = v_a_2261_;
goto v___jp_2194_;
}
else
{
size_t v___x_2266_; size_t v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = ((size_t)0ULL);
v___x_2267_ = lean_usize_of_nat(v___x_2263_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2041_);
lean_inc_ref(v___y_2049_);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_2248_, v___x_2266_, v___x_2267_, v___x_2262_, v___y_2049_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v_a_2261_);
lean_dec(v_a_2248_);
v___y_2229_ = v___y_2251_;
v___y_2230_ = v___y_2252_;
v___y_2231_ = v___y_2253_;
v___y_2232_ = v___y_2254_;
v___y_2233_ = v_a_2260_;
v___y_2234_ = v___y_2255_;
v___y_2235_ = v___y_2258_;
v___y_2236_ = v___y_2257_;
v___y_2237_ = v___y_2256_;
v___y_2238_ = v___y_2259_;
v___y_2239_ = v___x_2268_;
goto v___jp_2228_;
}
}
else
{
size_t v___x_2269_; size_t v___x_2270_; lean_object* v___x_2271_; 
v___x_2269_ = ((size_t)0ULL);
v___x_2270_ = lean_usize_of_nat(v___x_2263_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2041_);
lean_inc_ref(v___y_2049_);
v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_2248_, v___x_2269_, v___x_2270_, v___x_2262_, v___y_2049_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v_a_2261_);
lean_dec(v_a_2248_);
v___y_2229_ = v___y_2251_;
v___y_2230_ = v___y_2252_;
v___y_2231_ = v___y_2253_;
v___y_2232_ = v___y_2254_;
v___y_2233_ = v_a_2260_;
v___y_2234_ = v___y_2255_;
v___y_2235_ = v___y_2258_;
v___y_2236_ = v___y_2257_;
v___y_2237_ = v___y_2256_;
v___y_2238_ = v___y_2259_;
v___y_2239_ = v___x_2271_;
goto v___jp_2228_;
}
}
}
v___jp_2272_:
{
if (lean_obj_tag(v___y_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v_a_2284_; 
v_a_2283_ = lean_ctor_get(v___y_2282_, 0);
lean_inc(v_a_2283_);
v_a_2284_ = lean_ctor_get(v___y_2282_, 1);
lean_inc(v_a_2284_);
lean_dec_ref(v___y_2282_);
v___y_2251_ = v___y_2273_;
v___y_2252_ = v___y_2274_;
v___y_2253_ = v___y_2275_;
v___y_2254_ = v___y_2276_;
v___y_2255_ = v___y_2277_;
v___y_2256_ = v___y_2280_;
v___y_2257_ = v___y_2279_;
v___y_2258_ = v___y_2278_;
v___y_2259_ = v___y_2281_;
v_a_2260_ = v_a_2283_;
v_a_2261_ = v_a_2284_;
goto v___jp_2250_;
}
else
{
lean_object* v_a_2285_; lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref(v___y_2281_);
lean_dec_ref(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v___y_2276_);
lean_dec_ref(v___y_2273_);
lean_dec(v_a_2248_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2049_);
lean_dec(v_name_2046_);
lean_dec_ref(v_pkg_2045_);
lean_dec_ref(v_dir_2043_);
lean_dec_ref(v_self_2042_);
lean_dec(v___x_2041_);
v_a_2285_ = lean_ctor_get(v___y_2282_, 0);
v_a_2286_ = lean_ctor_get(v___y_2282_, 1);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___y_2282_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___y_2282_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_inc(v_a_2285_);
lean_dec(v___y_2282_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2285_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
v___jp_2294_:
{
lean_object* v_toLeanConfig_2297_; lean_object* v_toLeanConfig_2298_; lean_object* v_buildDir_2299_; lean_object* v_nativeLibDir_2300_; lean_object* v_moreLinkObjs_2301_; lean_object* v_moreLinkLibs_2302_; lean_object* v_moreLinkArgs_2303_; lean_object* v_weakLinkArgs_2304_; lean_object* v_moreLinkObjs_2305_; lean_object* v_moreLinkLibs_2306_; lean_object* v_moreLinkArgs_2307_; lean_object* v_weakLinkArgs_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v_toLeanConfig_2297_ = lean_ctor_get(v_config_2047_, 1);
lean_inc_ref(v_toLeanConfig_2297_);
v_toLeanConfig_2298_ = lean_ctor_get(v_config_2048_, 0);
v_buildDir_2299_ = lean_ctor_get(v_config_2047_, 5);
lean_inc_ref(v_buildDir_2299_);
v_nativeLibDir_2300_ = lean_ctor_get(v_config_2047_, 7);
lean_inc_ref(v_nativeLibDir_2300_);
lean_dec_ref(v_config_2047_);
v_moreLinkObjs_2301_ = lean_ctor_get(v_toLeanConfig_2297_, 6);
lean_inc_ref(v_moreLinkObjs_2301_);
v_moreLinkLibs_2302_ = lean_ctor_get(v_toLeanConfig_2297_, 7);
lean_inc_ref(v_moreLinkLibs_2302_);
v_moreLinkArgs_2303_ = lean_ctor_get(v_toLeanConfig_2297_, 8);
lean_inc_ref(v_moreLinkArgs_2303_);
v_weakLinkArgs_2304_ = lean_ctor_get(v_toLeanConfig_2297_, 9);
lean_inc_ref(v_weakLinkArgs_2304_);
lean_dec_ref(v_toLeanConfig_2297_);
v_moreLinkObjs_2305_ = lean_ctor_get(v_toLeanConfig_2298_, 6);
v_moreLinkLibs_2306_ = lean_ctor_get(v_toLeanConfig_2298_, 7);
v_moreLinkArgs_2307_ = lean_ctor_get(v_toLeanConfig_2298_, 8);
v_weakLinkArgs_2308_ = lean_ctor_get(v_toLeanConfig_2298_, 9);
v___x_2309_ = l_Array_append___redArg(v_moreLinkObjs_2301_, v_moreLinkObjs_2305_);
v___x_2310_ = lean_unsigned_to_nat(0u);
v___x_2311_ = lean_array_get_size(v___x_2309_);
v___x_2312_ = lean_nat_dec_lt(v___x_2310_, v___x_2311_);
if (v___x_2312_ == 0)
{
lean_dec_ref(v___x_2309_);
v___y_2251_ = v_nativeLibDir_2300_;
v___y_2252_ = v_weakLinkArgs_2308_;
v___y_2253_ = v___x_2310_;
v___y_2254_ = v_moreLinkLibs_2302_;
v___y_2255_ = v_moreLinkArgs_2307_;
v___y_2256_ = v_moreLinkLibs_2306_;
v___y_2257_ = v_moreLinkArgs_2303_;
v___y_2258_ = v_weakLinkArgs_2304_;
v___y_2259_ = v_buildDir_2299_;
v_a_2260_ = v_a_2295_;
v_a_2261_ = v_a_2296_;
goto v___jp_2250_;
}
else
{
uint8_t v___x_2313_; 
v___x_2313_ = lean_nat_dec_le(v___x_2311_, v___x_2311_);
if (v___x_2313_ == 0)
{
if (v___x_2312_ == 0)
{
lean_dec_ref(v___x_2309_);
v___y_2251_ = v_nativeLibDir_2300_;
v___y_2252_ = v_weakLinkArgs_2308_;
v___y_2253_ = v___x_2310_;
v___y_2254_ = v_moreLinkLibs_2302_;
v___y_2255_ = v_moreLinkArgs_2307_;
v___y_2256_ = v_moreLinkLibs_2306_;
v___y_2257_ = v_moreLinkArgs_2303_;
v___y_2258_ = v_weakLinkArgs_2304_;
v___y_2259_ = v_buildDir_2299_;
v_a_2260_ = v_a_2295_;
v_a_2261_ = v_a_2296_;
goto v___jp_2250_;
}
else
{
size_t v___x_2314_; size_t v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = ((size_t)0ULL);
v___x_2315_ = lean_usize_of_nat(v___x_2311_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2041_);
lean_inc_ref(v___y_2049_);
lean_inc_ref(v_pkg_2045_);
v___x_2316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2045_, v___x_2309_, v___x_2314_, v___x_2315_, v_a_2295_, v___y_2049_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v_a_2296_);
lean_dec_ref(v___x_2309_);
v___y_2273_ = v_nativeLibDir_2300_;
v___y_2274_ = v_weakLinkArgs_2308_;
v___y_2275_ = v___x_2310_;
v___y_2276_ = v_moreLinkLibs_2302_;
v___y_2277_ = v_moreLinkArgs_2307_;
v___y_2278_ = v_weakLinkArgs_2304_;
v___y_2279_ = v_moreLinkArgs_2303_;
v___y_2280_ = v_moreLinkLibs_2306_;
v___y_2281_ = v_buildDir_2299_;
v___y_2282_ = v___x_2316_;
goto v___jp_2272_;
}
}
else
{
size_t v___x_2317_; size_t v___x_2318_; lean_object* v___x_2319_; 
v___x_2317_ = ((size_t)0ULL);
v___x_2318_ = lean_usize_of_nat(v___x_2311_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2041_);
lean_inc_ref(v___y_2049_);
lean_inc_ref(v_pkg_2045_);
v___x_2319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2045_, v___x_2309_, v___x_2317_, v___x_2318_, v_a_2295_, v___y_2049_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v_a_2296_);
lean_dec_ref(v___x_2309_);
v___y_2273_ = v_nativeLibDir_2300_;
v___y_2274_ = v_weakLinkArgs_2308_;
v___y_2275_ = v___x_2310_;
v___y_2276_ = v_moreLinkLibs_2302_;
v___y_2277_ = v_moreLinkArgs_2307_;
v___y_2278_ = v_weakLinkArgs_2304_;
v___y_2279_ = v_moreLinkArgs_2303_;
v___y_2280_ = v_moreLinkLibs_2306_;
v___y_2281_ = v_buildDir_2299_;
v___y_2282_ = v___x_2319_;
goto v___jp_2272_;
}
}
}
v___jp_2320_:
{
if (lean_obj_tag(v___y_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v_a_2323_; 
v_a_2322_ = lean_ctor_get(v___y_2321_, 0);
lean_inc(v_a_2322_);
v_a_2323_ = lean_ctor_get(v___y_2321_, 1);
lean_inc(v_a_2323_);
lean_dec_ref(v___y_2321_);
v_a_2295_ = v_a_2322_;
v_a_2296_ = v_a_2323_;
goto v___jp_2294_;
}
else
{
lean_object* v_a_2324_; lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_a_2248_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_config_2047_);
lean_dec(v_name_2046_);
lean_dec_ref(v_pkg_2045_);
lean_dec_ref(v_dir_2043_);
lean_dec_ref(v_self_2042_);
lean_dec(v___x_2041_);
v_a_2324_ = lean_ctor_get(v___y_2321_, 0);
v_a_2325_ = lean_ctor_get(v___y_2321_, 1);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___y_2321_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___y_2321_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_inc(v_a_2324_);
lean_dec(v___y_2321_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2324_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_config_2047_);
lean_dec(v_name_2046_);
lean_dec_ref(v_pkg_2045_);
lean_dec_ref(v_dir_2043_);
lean_dec_ref(v_self_2042_);
lean_dec(v___x_2041_);
v_a_2344_ = lean_ctor_get(v___x_2247_, 0);
v_a_2345_ = lean_ctor_get(v___x_2247_, 1);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2247_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_inc(v_a_2344_);
lean_dec(v___x_2247_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2344_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_config_2047_);
lean_dec(v_name_2046_);
lean_dec_ref(v_pkg_2045_);
lean_dec_ref(v_dir_2043_);
lean_dec_ref(v_self_2042_);
lean_dec(v___x_2041_);
v_a_2353_ = lean_ctor_get(v___x_2244_, 0);
v_a_2354_ = lean_ctor_get(v___x_2244_, 1);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2244_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_inc(v_a_2353_);
lean_dec(v___x_2244_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2353_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
v___jp_2056_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_inc_ref(v_self_2042_);
v___x_2066_ = l_Lake_LeanLib_libName(v_self_2042_);
v___x_2067_ = l_System_FilePath_normalize(v___y_2063_);
v___x_2068_ = l_Lake_joinRelative(v_dir_2043_, v___x_2067_);
v___x_2069_ = l_System_FilePath_normalize(v___y_2057_);
v___x_2070_ = l_Lake_joinRelative(v___x_2068_, v___x_2069_);
v___x_2071_ = 0;
v___x_2072_ = l_Lake_nameToSharedLib(v___x_2066_, v___x_2071_);
v___x_2073_ = l_Lake_joinRelative(v___x_2070_, v___x_2072_);
v___x_2074_ = l_Array_append___redArg(v___y_2062_, v___y_2058_);
v___x_2075_ = l_Array_append___redArg(v___y_2061_, v___y_2060_);
v___x_2076_ = l_Lake_LeanLib_isPlugin(v_self_2042_);
v___x_2077_ = l_System_Platform_isWindows;
v___x_2078_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2079_ = l_Lake_buildLeanSharedLib(v___x_2066_, v___x_2073_, v___y_2059_, v_a_2064_, v___x_2074_, v___x_2075_, v___x_2076_, v___x_2077_, v___y_2049_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v___x_2078_);
lean_dec_ref(v___y_2059_);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v_a_2065_);
return v___x_2080_;
}
v___jp_2081_:
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2084_, 0, v_a_2082_);
lean_ctor_set(v___x_2084_, 1, v_a_2083_);
return v___x_2084_;
}
v___jp_2085_:
{
if (lean_obj_tag(v___y_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v_a_2095_; 
v_a_2094_ = lean_ctor_get(v___y_2093_, 0);
lean_inc(v_a_2094_);
v_a_2095_ = lean_ctor_get(v___y_2093_, 1);
lean_inc(v_a_2095_);
lean_dec_ref(v___y_2093_);
v___y_2057_ = v___y_2086_;
v___y_2058_ = v___y_2087_;
v___y_2059_ = v___y_2088_;
v___y_2060_ = v___y_2089_;
v___y_2061_ = v___y_2091_;
v___y_2062_ = v___y_2090_;
v___y_2063_ = v___y_2092_;
v_a_2064_ = v_a_2094_;
v_a_2065_ = v_a_2095_;
goto v___jp_2056_;
}
else
{
lean_object* v_a_2096_; lean_object* v_a_2097_; 
lean_dec_ref(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec_ref(v___y_2088_);
lean_dec_ref(v___y_2086_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_dir_2043_);
lean_dec_ref(v_self_2042_);
lean_dec(v___x_2041_);
v_a_2096_ = lean_ctor_get(v___y_2093_, 0);
lean_inc(v_a_2096_);
v_a_2097_ = lean_ctor_get(v___y_2093_, 1);
lean_inc(v_a_2097_);
lean_dec_ref(v___y_2093_);
v_a_2082_ = v_a_2096_;
v_a_2083_ = v_a_2097_;
goto v___jp_2081_;
}
}
v___jp_2098_:
{
lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = lean_array_get_size(v___y_2109_);
v___x_2111_ = lean_nat_dec_lt(v___y_2102_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_dec_ref(v___y_2109_);
v___y_2057_ = v___y_2100_;
v___y_2058_ = v___y_2101_;
v___y_2059_ = v___y_2103_;
v___y_2060_ = v___y_2104_;
v___y_2061_ = v___y_2106_;
v___y_2062_ = v___y_2105_;
v___y_2063_ = v___y_2108_;
v_a_2064_ = v___y_2107_;
v_a_2065_ = v___y_2099_;
goto v___jp_2056_;
}
else
{
uint8_t v___x_2112_; 
v___x_2112_ = lean_nat_dec_le(v___x_2110_, v___x_2110_);
if (v___x_2112_ == 0)
{
if (v___x_2111_ == 0)
{
lean_dec_ref(v___y_2109_);
v___y_2057_ = v___y_2100_;
v___y_2058_ = v___y_2101_;
v___y_2059_ = v___y_2103_;
v___y_2060_ = v___y_2104_;
v___y_2061_ = v___y_2106_;
v___y_2062_ = v___y_2105_;
v___y_2063_ = v___y_2108_;
v_a_2064_ = v___y_2107_;
v_a_2065_ = v___y_2099_;
goto v___jp_2056_;
}
else
{
size_t v___x_2113_; size_t v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = ((size_t)0ULL);
v___x_2114_ = lean_usize_of_nat(v___x_2110_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2041_);
lean_inc_ref(v___y_2049_);
v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2109_, v___x_2113_, v___x_2114_, v___y_2107_, v___y_2049_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2099_);
lean_dec_ref(v___y_2109_);
v___y_2086_ = v___y_2100_;
v___y_2087_ = v___y_2101_;
v___y_2088_ = v___y_2103_;
v___y_2089_ = v___y_2104_;
v___y_2090_ = v___y_2105_;
v___y_2091_ = v___y_2106_;
v___y_2092_ = v___y_2108_;
v___y_2093_ = v___x_2115_;
goto v___jp_2085_;
}
}
else
{
size_t v___x_2116_; size_t v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = ((size_t)0ULL);
v___x_2117_ = lean_usize_of_nat(v___x_2110_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2041_);
lean_inc_ref(v___y_2049_);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2109_, v___x_2116_, v___x_2117_, v___y_2107_, v___y_2049_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2099_);
lean_dec_ref(v___y_2109_);
v___y_2086_ = v___y_2100_;
v___y_2087_ = v___y_2101_;
v___y_2088_ = v___y_2103_;
v___y_2089_ = v___y_2104_;
v___y_2090_ = v___y_2105_;
v___y_2091_ = v___y_2106_;
v___y_2092_ = v___y_2108_;
v___y_2093_ = v___x_2118_;
goto v___jp_2085_;
}
}
}
v___jp_2119_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2130_ = lean_mk_empty_array_with_capacity(v___y_2122_);
v___x_2131_ = lean_array_get_size(v_targetDecls_2044_);
v___x_2132_ = lean_nat_dec_lt(v___y_2122_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_dec_ref(v_pkg_2045_);
v___y_2099_ = v_a_2129_;
v___y_2100_ = v___y_2120_;
v___y_2101_ = v___y_2121_;
v___y_2102_ = v___y_2122_;
v___y_2103_ = v___y_2123_;
v___y_2104_ = v___y_2124_;
v___y_2105_ = v___y_2126_;
v___y_2106_ = v___y_2125_;
v___y_2107_ = v_a_2128_;
v___y_2108_ = v___y_2127_;
v___y_2109_ = v___x_2130_;
goto v___jp_2098_;
}
else
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_nat_dec_le(v___x_2131_, v___x_2131_);
if (v___x_2133_ == 0)
{
if (v___x_2132_ == 0)
{
lean_dec_ref(v_pkg_2045_);
v___y_2099_ = v_a_2129_;
v___y_2100_ = v___y_2120_;
v___y_2101_ = v___y_2121_;
v___y_2102_ = v___y_2122_;
v___y_2103_ = v___y_2123_;
v___y_2104_ = v___y_2124_;
v___y_2105_ = v___y_2126_;
v___y_2106_ = v___y_2125_;
v___y_2107_ = v_a_2128_;
v___y_2108_ = v___y_2127_;
v___y_2109_ = v___x_2130_;
goto v___jp_2098_;
}
else
{
size_t v___x_2134_; size_t v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = ((size_t)0ULL);
v___x_2135_ = lean_usize_of_nat(v___x_2131_);
v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2045_, v_targetDecls_2044_, v___x_2134_, v___x_2135_, v___x_2130_);
v___y_2099_ = v_a_2129_;
v___y_2100_ = v___y_2120_;
v___y_2101_ = v___y_2121_;
v___y_2102_ = v___y_2122_;
v___y_2103_ = v___y_2123_;
v___y_2104_ = v___y_2124_;
v___y_2105_ = v___y_2126_;
v___y_2106_ = v___y_2125_;
v___y_2107_ = v_a_2128_;
v___y_2108_ = v___y_2127_;
v___y_2109_ = v___x_2136_;
goto v___jp_2098_;
}
}
else
{
size_t v___x_2137_; size_t v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = ((size_t)0ULL);
v___x_2138_ = lean_usize_of_nat(v___x_2131_);
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2045_, v_targetDecls_2044_, v___x_2137_, v___x_2138_, v___x_2130_);
v___y_2099_ = v_a_2129_;
v___y_2100_ = v___y_2120_;
v___y_2101_ = v___y_2121_;
v___y_2102_ = v___y_2122_;
v___y_2103_ = v___y_2123_;
v___y_2104_ = v___y_2124_;
v___y_2105_ = v___y_2126_;
v___y_2106_ = v___y_2125_;
v___y_2107_ = v_a_2128_;
v___y_2108_ = v___y_2127_;
v___y_2109_ = v___x_2139_;
goto v___jp_2098_;
}
}
}
v___jp_2140_:
{
if (lean_obj_tag(v___y_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v_a_2151_; 
v_a_2150_ = lean_ctor_get(v___y_2149_, 0);
lean_inc(v_a_2150_);
v_a_2151_ = lean_ctor_get(v___y_2149_, 1);
lean_inc(v_a_2151_);
lean_dec_ref(v___y_2149_);
v___y_2120_ = v___y_2141_;
v___y_2121_ = v___y_2142_;
v___y_2122_ = v___y_2143_;
v___y_2123_ = v___y_2144_;
v___y_2124_ = v___y_2145_;
v___y_2125_ = v___y_2147_;
v___y_2126_ = v___y_2146_;
v___y_2127_ = v___y_2148_;
v_a_2128_ = v_a_2150_;
v_a_2129_ = v_a_2151_;
goto v___jp_2119_;
}
else
{
lean_object* v_a_2152_; lean_object* v_a_2153_; 
lean_dec_ref(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec_ref(v___y_2144_);
lean_dec_ref(v___y_2141_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_pkg_2045_);
lean_dec_ref(v_dir_2043_);
lean_dec_ref(v_self_2042_);
lean_dec(v___x_2041_);
v_a_2152_ = lean_ctor_get(v___y_2149_, 0);
lean_inc(v_a_2152_);
v_a_2153_ = lean_ctor_get(v___y_2149_, 1);
lean_inc(v_a_2153_);
lean_dec_ref(v___y_2149_);
v_a_2082_ = v_a_2152_;
v_a_2083_ = v_a_2153_;
goto v___jp_2081_;
}
}
v___jp_2154_:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2167_ = l_Array_append___redArg(v___y_2158_, v___y_2163_);
v___x_2168_ = lean_array_get_size(v___x_2167_);
v___x_2169_ = lean_nat_dec_lt(v___y_2157_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_dec_ref(v___x_2167_);
v___y_2120_ = v___y_2155_;
v___y_2121_ = v___y_2156_;
v___y_2122_ = v___y_2157_;
v___y_2123_ = v___y_2159_;
v___y_2124_ = v___y_2160_;
v___y_2125_ = v___y_2162_;
v___y_2126_ = v___y_2161_;
v___y_2127_ = v___y_2164_;
v_a_2128_ = v_snd_2165_;
v_a_2129_ = v_a_2166_;
goto v___jp_2119_;
}
else
{
uint8_t v___x_2170_; 
v___x_2170_ = lean_nat_dec_le(v___x_2168_, v___x_2168_);
if (v___x_2170_ == 0)
{
if (v___x_2169_ == 0)
{
lean_dec_ref(v___x_2167_);
v___y_2120_ = v___y_2155_;
v___y_2121_ = v___y_2156_;
v___y_2122_ = v___y_2157_;
v___y_2123_ = v___y_2159_;
v___y_2124_ = v___y_2160_;
v___y_2125_ = v___y_2162_;
v___y_2126_ = v___y_2161_;
v___y_2127_ = v___y_2164_;
v_a_2128_ = v_snd_2165_;
v_a_2129_ = v_a_2166_;
goto v___jp_2119_;
}
else
{
size_t v___x_2171_; size_t v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = ((size_t)0ULL);
v___x_2172_ = lean_usize_of_nat(v___x_2168_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2041_);
lean_inc_ref(v___y_2049_);
lean_inc_ref(v_pkg_2045_);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2045_, v___x_2167_, v___x_2171_, v___x_2172_, v_snd_2165_, v___y_2049_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v_a_2166_);
lean_dec_ref(v___x_2167_);
v___y_2141_ = v___y_2155_;
v___y_2142_ = v___y_2156_;
v___y_2143_ = v___y_2157_;
v___y_2144_ = v___y_2159_;
v___y_2145_ = v___y_2160_;
v___y_2146_ = v___y_2161_;
v___y_2147_ = v___y_2162_;
v___y_2148_ = v___y_2164_;
v___y_2149_ = v___x_2173_;
goto v___jp_2140_;
}
}
else
{
size_t v___x_2174_; size_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = ((size_t)0ULL);
v___x_2175_ = lean_usize_of_nat(v___x_2168_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2041_);
lean_inc_ref(v___y_2049_);
lean_inc_ref(v_pkg_2045_);
v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2045_, v___x_2167_, v___x_2174_, v___x_2175_, v_snd_2165_, v___y_2049_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v_a_2166_);
lean_dec_ref(v___x_2167_);
v___y_2141_ = v___y_2155_;
v___y_2142_ = v___y_2156_;
v___y_2143_ = v___y_2157_;
v___y_2144_ = v___y_2159_;
v___y_2145_ = v___y_2160_;
v___y_2146_ = v___y_2161_;
v___y_2147_ = v___y_2162_;
v___y_2148_ = v___y_2164_;
v___y_2149_ = v___x_2176_;
goto v___jp_2140_;
}
}
}
v___jp_2177_:
{
if (lean_obj_tag(v___y_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v_a_2190_; lean_object* v_snd_2191_; 
v_a_2189_ = lean_ctor_get(v___y_2188_, 0);
lean_inc(v_a_2189_);
v_a_2190_ = lean_ctor_get(v___y_2188_, 1);
lean_inc(v_a_2190_);
lean_dec_ref(v___y_2188_);
v_snd_2191_ = lean_ctor_get(v_a_2189_, 1);
lean_inc(v_snd_2191_);
lean_dec(v_a_2189_);
v___y_2155_ = v___y_2178_;
v___y_2156_ = v___y_2179_;
v___y_2157_ = v___y_2180_;
v___y_2158_ = v___y_2181_;
v___y_2159_ = v___y_2182_;
v___y_2160_ = v___y_2183_;
v___y_2161_ = v___y_2186_;
v___y_2162_ = v___y_2185_;
v___y_2163_ = v___y_2184_;
v___y_2164_ = v___y_2187_;
v_snd_2165_ = v_snd_2191_;
v_a_2166_ = v_a_2190_;
goto v___jp_2154_;
}
else
{
lean_object* v_a_2192_; lean_object* v_a_2193_; 
lean_dec_ref(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec_ref(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec_ref(v___y_2178_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_pkg_2045_);
lean_dec_ref(v_dir_2043_);
lean_dec_ref(v_self_2042_);
lean_dec(v___x_2041_);
v_a_2192_ = lean_ctor_get(v___y_2188_, 0);
lean_inc(v_a_2192_);
v_a_2193_ = lean_ctor_get(v___y_2188_, 1);
lean_inc(v_a_2193_);
lean_dec_ref(v___y_2188_);
v_a_2082_ = v_a_2192_;
v_a_2083_ = v_a_2193_;
goto v___jp_2081_;
}
}
v___jp_2194_:
{
lean_object* v_toArray_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2226_; 
v_toArray_2207_ = lean_ctor_get(v_a_2205_, 1);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_a_2205_);
if (v_isSharedCheck_2226_ == 0)
{
lean_object* v_unused_2227_; 
v_unused_2227_ = lean_ctor_get(v_a_2205_, 0);
lean_dec(v_unused_2227_);
v___x_2209_ = v_a_2205_;
v_isShared_2210_ = v_isSharedCheck_2226_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_toArray_2207_);
lean_dec(v_a_2205_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2226_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v___x_2211_ = lean_mk_empty_array_with_capacity(v___y_2197_);
v___x_2212_ = lean_array_get_size(v_toArray_2207_);
v___x_2213_ = lean_nat_dec_lt(v___y_2197_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_del_object(v___x_2209_);
lean_dec_ref(v_toArray_2207_);
lean_dec(v_name_2046_);
v___y_2155_ = v___y_2195_;
v___y_2156_ = v___y_2196_;
v___y_2157_ = v___y_2197_;
v___y_2158_ = v___y_2198_;
v___y_2159_ = v___y_2199_;
v___y_2160_ = v___y_2200_;
v___y_2161_ = v___y_2203_;
v___y_2162_ = v___y_2202_;
v___y_2163_ = v___y_2201_;
v___y_2164_ = v___y_2204_;
v_snd_2165_ = v___x_2211_;
v_a_2166_ = v_a_2206_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2214_ = l_Lean_NameSet_empty;
v___x_2215_ = l_Lean_NameSet_insert(v___x_2214_, v_name_2046_);
lean_inc_ref(v___x_2211_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 1, v___x_2211_);
lean_ctor_set(v___x_2209_, 0, v___x_2215_);
v___x_2217_ = v___x_2209_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2215_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v___x_2211_);
v___x_2217_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
uint8_t v___x_2218_; 
v___x_2218_ = lean_nat_dec_le(v___x_2212_, v___x_2212_);
if (v___x_2218_ == 0)
{
if (v___x_2213_ == 0)
{
lean_dec_ref(v___x_2217_);
lean_dec_ref(v_toArray_2207_);
v___y_2155_ = v___y_2195_;
v___y_2156_ = v___y_2196_;
v___y_2157_ = v___y_2197_;
v___y_2158_ = v___y_2198_;
v___y_2159_ = v___y_2199_;
v___y_2160_ = v___y_2200_;
v___y_2161_ = v___y_2203_;
v___y_2162_ = v___y_2202_;
v___y_2163_ = v___y_2201_;
v___y_2164_ = v___y_2204_;
v_snd_2165_ = v___x_2211_;
v_a_2166_ = v_a_2206_;
goto v___jp_2154_;
}
else
{
size_t v___x_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
lean_dec_ref(v___x_2211_);
v___x_2219_ = ((size_t)0ULL);
v___x_2220_ = lean_usize_of_nat(v___x_2212_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2041_);
lean_inc_ref(v___y_2049_);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_2207_, v___x_2219_, v___x_2220_, v___x_2217_, v___y_2049_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v_a_2206_);
lean_dec_ref(v_toArray_2207_);
v___y_2178_ = v___y_2195_;
v___y_2179_ = v___y_2196_;
v___y_2180_ = v___y_2197_;
v___y_2181_ = v___y_2198_;
v___y_2182_ = v___y_2199_;
v___y_2183_ = v___y_2200_;
v___y_2184_ = v___y_2201_;
v___y_2185_ = v___y_2202_;
v___y_2186_ = v___y_2203_;
v___y_2187_ = v___y_2204_;
v___y_2188_ = v___x_2221_;
goto v___jp_2177_;
}
}
else
{
size_t v___x_2222_; size_t v___x_2223_; lean_object* v___x_2224_; 
lean_dec_ref(v___x_2211_);
v___x_2222_ = ((size_t)0ULL);
v___x_2223_ = lean_usize_of_nat(v___x_2212_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2041_);
lean_inc_ref(v___y_2049_);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_2207_, v___x_2222_, v___x_2223_, v___x_2217_, v___y_2049_, v___x_2041_, v___y_2051_, v___y_2052_, v___y_2053_, v_a_2206_);
lean_dec_ref(v_toArray_2207_);
v___y_2178_ = v___y_2195_;
v___y_2179_ = v___y_2196_;
v___y_2180_ = v___y_2197_;
v___y_2181_ = v___y_2198_;
v___y_2182_ = v___y_2199_;
v___y_2183_ = v___y_2200_;
v___y_2184_ = v___y_2201_;
v___y_2185_ = v___y_2202_;
v___y_2186_ = v___y_2203_;
v___y_2187_ = v___y_2204_;
v___y_2188_ = v___x_2224_;
goto v___jp_2177_;
}
}
}
}
}
v___jp_2228_:
{
if (lean_obj_tag(v___y_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v_a_2241_; 
v_a_2240_ = lean_ctor_get(v___y_2239_, 0);
lean_inc(v_a_2240_);
v_a_2241_ = lean_ctor_get(v___y_2239_, 1);
lean_inc(v_a_2241_);
lean_dec_ref(v___y_2239_);
v___y_2195_ = v___y_2229_;
v___y_2196_ = v___y_2230_;
v___y_2197_ = v___y_2231_;
v___y_2198_ = v___y_2232_;
v___y_2199_ = v___y_2233_;
v___y_2200_ = v___y_2234_;
v___y_2201_ = v___y_2237_;
v___y_2202_ = v___y_2236_;
v___y_2203_ = v___y_2235_;
v___y_2204_ = v___y_2238_;
v_a_2205_ = v_a_2240_;
v_a_2206_ = v_a_2241_;
goto v___jp_2194_;
}
else
{
lean_object* v_a_2242_; lean_object* v_a_2243_; 
lean_dec_ref(v___y_2238_);
lean_dec_ref(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec_ref(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec_ref(v___y_2229_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2049_);
lean_dec(v_name_2046_);
lean_dec_ref(v_pkg_2045_);
lean_dec_ref(v_dir_2043_);
lean_dec_ref(v_self_2042_);
lean_dec(v___x_2041_);
v_a_2242_ = lean_ctor_get(v___y_2239_, 0);
lean_inc(v_a_2242_);
v_a_2243_ = lean_ctor_get(v___y_2239_, 1);
lean_inc(v_a_2243_);
lean_dec_ref(v___y_2239_);
v_a_2082_ = v_a_2242_;
v_a_2083_ = v_a_2243_;
goto v___jp_2081_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v___x_2362_, lean_object* v___x_2363_, lean_object* v_self_2364_, lean_object* v_dir_2365_, lean_object* v_targetDecls_2366_, lean_object* v_pkg_2367_, lean_object* v_name_2368_, lean_object* v_config_2369_, lean_object* v_config_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v___x_2362_, v___x_2363_, v_self_2364_, v_dir_2365_, v_targetDecls_2366_, v_pkg_2367_, v_name_2368_, v_config_2369_, v_config_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2372_);
lean_dec(v_config_2370_);
lean_dec_ref(v_targetDecls_2366_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v_pkg_2388_; lean_object* v_name_2389_; lean_object* v_config_2390_; lean_object* v_keyName_2391_; lean_object* v_dir_2392_; lean_object* v_config_2393_; lean_object* v_targetDecls_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___f_2401_; lean_object* v___x_2402_; 
v_pkg_2388_ = lean_ctor_get(v_self_2380_, 0);
lean_inc_ref(v_pkg_2388_);
v_name_2389_ = lean_ctor_get(v_self_2380_, 1);
lean_inc(v_name_2389_);
v_config_2390_ = lean_ctor_get(v_self_2380_, 2);
lean_inc(v_config_2390_);
v_keyName_2391_ = lean_ctor_get(v_pkg_2388_, 2);
v_dir_2392_ = lean_ctor_get(v_pkg_2388_, 4);
lean_inc_ref(v_dir_2392_);
v_config_2393_ = lean_ctor_get(v_pkg_2388_, 6);
lean_inc_ref(v_config_2393_);
v_targetDecls_2394_ = lean_ctor_get(v_pkg_2388_, 13);
lean_inc_ref(v_targetDecls_2394_);
v___x_2395_ = l_Lake_instDataKindDynlib;
v___x_2396_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_2389_);
lean_inc(v_keyName_2391_);
v___x_2397_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2397_, 0, v_keyName_2391_);
lean_ctor_set(v___x_2397_, 1, v_name_2389_);
v___x_2398_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2380_);
v___x_2399_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
lean_ctor_set(v___x_2399_, 2, v_self_2380_);
lean_ctor_set(v___x_2399_, 3, v___x_2396_);
lean_inc_ref(v_pkg_2388_);
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v_pkg_2388_);
lean_inc(v_name_2389_);
v___f_2401_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2401_, 0, v___x_2399_);
lean_closure_set(v___f_2401_, 1, v___x_2400_);
lean_closure_set(v___f_2401_, 2, v_self_2380_);
lean_closure_set(v___f_2401_, 3, v_dir_2392_);
lean_closure_set(v___f_2401_, 4, v_targetDecls_2394_);
lean_closure_set(v___f_2401_, 5, v_pkg_2388_);
lean_closure_set(v___f_2401_, 6, v_name_2389_);
lean_closure_set(v___f_2401_, 7, v_config_2393_);
lean_closure_set(v___f_2401_, 8, v_config_2390_);
lean_inc_ref(v_a_2385_);
v___x_2402_ = l_Lake_ensureJob___redArg(v___x_2395_, v___f_2401_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2432_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_a_2404_ = lean_ctor_get(v___x_2402_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2406_ = v___x_2402_;
v_isShared_2407_ = v_isSharedCheck_2432_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2432_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v_task_2408_; lean_object* v_kind_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2430_; 
v_task_2408_ = lean_ctor_get(v_a_2403_, 0);
v_kind_2409_ = lean_ctor_get(v_a_2403_, 1);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_a_2403_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; 
v_unused_2431_ = lean_ctor_get(v_a_2403_, 2);
lean_dec(v_unused_2431_);
v___x_2411_ = v_a_2403_;
v_isShared_2412_ = v_isSharedCheck_2430_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_kind_2409_);
lean_inc(v_task_2408_);
lean_dec(v_a_2403_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2430_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v_registeredJobs_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; lean_object* v_job_2421_; 
v_registeredJobs_2413_ = lean_ctor_get(v_a_2385_, 3);
lean_inc(v_registeredJobs_2413_);
lean_dec_ref(v_a_2385_);
v___x_2414_ = lean_st_ref_take(v_registeredJobs_2413_);
v___x_2415_ = 1;
v___x_2416_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2389_, v___x_2415_);
v___x_2417_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_2418_ = lean_string_append(v___x_2416_, v___x_2417_);
v___x_2419_ = 0;
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 2, v___x_2418_);
v_job_2421_ = v___x_2411_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_task_2408_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v_kind_2409_);
lean_ctor_set(v_reuseFailAlloc_2429_, 2, v___x_2418_);
v_job_2421_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
lean_ctor_set_uint8(v_job_2421_, sizeof(void*)*3, v___x_2419_);
lean_inc_ref(v_job_2421_);
v___x_2422_ = l_Lake_Job_toOpaque___redArg(v_job_2421_);
v___x_2423_ = lean_array_push(v___x_2414_, v___x_2422_);
v___x_2424_ = lean_st_ref_set(v_registeredJobs_2413_, v___x_2423_);
lean_dec(v_registeredJobs_2413_);
v___x_2425_ = l_Lake_Job_renew___redArg(v_job_2421_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2425_);
v___x_2427_ = v___x_2406_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_a_2404_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
else
{
lean_dec(v_name_2389_);
lean_dec_ref(v_a_2385_);
return v___x_2402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_2442_, lean_object* v_a_2443_){
_start:
{
if (v_fmt_2442_ == 0)
{
lean_object* v_path_2444_; 
v_path_2444_ = lean_ctor_get(v_a_2443_, 0);
lean_inc_ref(v_path_2444_);
return v_path_2444_;
}
else
{
lean_object* v_path_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_path_2445_ = lean_ctor_get(v_a_2443_, 0);
lean_inc_ref(v_path_2445_);
v___x_2446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2446_, 0, v_path_2445_);
v___x_2447_ = l_Lean_Json_compress(v___x_2446_);
return v___x_2447_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_2448_, lean_object* v_a_2449_){
_start:
{
uint8_t v_fmt_boxed_2450_; lean_object* v_res_2451_; 
v_fmt_boxed_2450_ = lean_unbox(v_fmt_2448_);
v_res_2451_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_2450_, v_a_2449_);
lean_dec_ref(v_a_2449_);
return v_res_2451_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___f_2454_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_2455_ = 1;
v___x_2456_ = l_Lake_instDataKindDynlib;
v___x_2457_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
v___x_2458_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2459_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
lean_ctor_set(v___x_2459_, 1, v___x_2457_);
lean_ctor_set(v___x_2459_, 2, v___x_2456_);
lean_ctor_set(v___x_2459_, 3, v___f_2454_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*4, v___x_2455_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*4 + 1, v___x_2455_);
return v___x_2459_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_2461_, lean_object* v_as_2462_, size_t v_sz_2463_, size_t v_i_2464_, lean_object* v_b_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
uint8_t v___x_2473_; 
v___x_2473_ = lean_usize_dec_lt(v_i_2464_, v_sz_2463_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; 
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec_ref(v___x_2461_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v_b_2465_);
lean_ctor_set(v___x_2474_, 1, v___y_2471_);
return v___x_2474_;
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2476_; 
v_a_2475_ = lean_array_uget_borrowed(v_as_2462_, v_i_2464_);
lean_inc_ref(v___y_2470_);
lean_inc(v___y_2469_);
lean_inc(v___y_2468_);
lean_inc(v___y_2467_);
lean_inc_ref(v___y_2466_);
lean_inc_n(v_a_2475_, 2);
lean_inc_ref(v___x_2461_);
v___x_2476_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_2461_, v_a_2475_, v_a_2475_, v___x_2473_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v_a_2478_; lean_object* v_snd_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; size_t v___x_2482_; size_t v___x_2483_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
v_a_2478_ = lean_ctor_get(v___x_2476_, 1);
lean_inc(v_a_2478_);
lean_dec_ref(v___x_2476_);
v_snd_2479_ = lean_ctor_get(v_a_2477_, 1);
lean_inc(v_snd_2479_);
lean_dec(v_a_2477_);
v___x_2480_ = l_Lake_Job_toOpaque___redArg(v_snd_2479_);
v___x_2481_ = l_Lake_Job_mix___redArg(v_b_2465_, v___x_2480_);
v___x_2482_ = ((size_t)1ULL);
v___x_2483_ = lean_usize_add(v_i_2464_, v___x_2482_);
v_i_2464_ = v___x_2483_;
v_b_2465_ = v___x_2481_;
v___y_2471_ = v_a_2478_;
goto _start;
}
else
{
lean_object* v_a_2485_; lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec_ref(v_b_2465_);
lean_dec_ref(v___x_2461_);
v_a_2485_ = lean_ctor_get(v___x_2476_, 0);
v_a_2486_ = lean_ctor_get(v___x_2476_, 1);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2476_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_inc(v_a_2485_);
lean_dec(v___x_2476_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2485_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_2494_, lean_object* v_as_2495_, lean_object* v_sz_2496_, lean_object* v_i_2497_, lean_object* v_b_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
size_t v_sz_boxed_2506_; size_t v_i_boxed_2507_; lean_object* v_res_2508_; 
v_sz_boxed_2506_ = lean_unbox_usize(v_sz_2496_);
lean_dec(v_sz_2496_);
v_i_boxed_2507_ = lean_unbox_usize(v_i_2497_);
lean_dec(v_i_2497_);
v_res_2508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_2494_, v_as_2495_, v_sz_boxed_2506_, v_i_boxed_2507_, v_b_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec_ref(v_as_2495_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_2509_, lean_object* v_as_2510_, size_t v_sz_2511_, size_t v_i_2512_, lean_object* v_b_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_usize_dec_lt(v_i_2512_, v_sz_2511_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; 
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v___x_2509_);
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v_b_2513_);
lean_ctor_set(v___x_2522_, 1, v___y_2519_);
return v___x_2522_;
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2524_; 
v_a_2523_ = lean_array_uget_borrowed(v_as_2510_, v_i_2512_);
lean_inc_ref(v___y_2518_);
lean_inc(v___y_2517_);
lean_inc(v___y_2516_);
lean_inc(v___y_2515_);
lean_inc_ref(v___y_2514_);
lean_inc(v_a_2523_);
lean_inc_ref(v___x_2509_);
v___x_2524_ = l_Lake_Package_fetchTargetJob(v___x_2509_, v_a_2523_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v_a_2526_; lean_object* v___x_2527_; size_t v___x_2528_; size_t v___x_2529_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
v_a_2526_ = lean_ctor_get(v___x_2524_, 1);
lean_inc(v_a_2526_);
lean_dec_ref(v___x_2524_);
v___x_2527_ = l_Lake_Job_mix___redArg(v_b_2513_, v_a_2525_);
v___x_2528_ = ((size_t)1ULL);
v___x_2529_ = lean_usize_add(v_i_2512_, v___x_2528_);
v_i_2512_ = v___x_2529_;
v_b_2513_ = v___x_2527_;
v___y_2519_ = v_a_2526_;
goto _start;
}
else
{
lean_object* v_a_2531_; lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v_b_2513_);
lean_dec_ref(v___x_2509_);
v_a_2531_ = lean_ctor_get(v___x_2524_, 0);
v_a_2532_ = lean_ctor_get(v___x_2524_, 1);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2524_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_inc(v_a_2531_);
lean_dec(v___x_2524_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2531_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_2540_, lean_object* v_as_2541_, lean_object* v_sz_2542_, lean_object* v_i_2543_, lean_object* v_b_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
size_t v_sz_boxed_2552_; size_t v_i_boxed_2553_; lean_object* v_res_2554_; 
v_sz_boxed_2552_ = lean_unbox_usize(v_sz_2542_);
lean_dec(v_sz_2542_);
v_i_boxed_2553_ = lean_unbox_usize(v_i_2543_);
lean_dec(v_i_2543_);
v_res_2554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_2540_, v_as_2541_, v_sz_boxed_2552_, v_i_boxed_2553_, v_b_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec_ref(v_as_2541_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v_pkg_2565_; lean_object* v_name_2566_; lean_object* v_config_2567_; lean_object* v_baseName_2568_; lean_object* v_keyName_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v_pkg_2565_ = lean_ctor_get(v_self_2557_, 0);
lean_inc_ref(v_pkg_2565_);
v_name_2566_ = lean_ctor_get(v_self_2557_, 1);
lean_inc(v_name_2566_);
v_config_2567_ = lean_ctor_get(v_self_2557_, 2);
lean_inc(v_config_2567_);
lean_dec_ref(v_self_2557_);
v_baseName_2568_ = lean_ctor_get(v_pkg_2565_, 1);
v_keyName_2569_ = lean_ctor_get(v_pkg_2565_, 2);
v___x_2570_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_2569_);
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_keyName_2569_);
v___x_2572_ = l_Lake_Package_keyword;
lean_inc_ref(v_pkg_2565_);
v___x_2573_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
lean_ctor_set(v___x_2573_, 2, v_pkg_2565_);
lean_ctor_set(v___x_2573_, 3, v___x_2570_);
lean_inc_ref(v_a_2558_);
lean_inc_ref(v_a_2562_);
lean_inc(v_a_2561_);
lean_inc(v_a_2560_);
lean_inc(v_a_2559_);
v___x_2574_ = lean_apply_7(v_a_2558_, v___x_2573_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, lean_box(0));
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2612_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_a_2576_ = lean_ctor_get(v___x_2574_, 1);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2578_ = v___x_2574_;
v_isShared_2579_ = v_isSharedCheck_2612_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2612_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
uint8_t v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v_needs_2584_; lean_object* v_extraDepTargets_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2580_ = 1;
lean_inc(v_baseName_2568_);
v___x_2581_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2568_, v___x_2580_);
v___x_2582_ = lean_unsigned_to_nat(0u);
v___x_2583_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v_needs_2584_ = lean_ctor_get(v_config_2567_, 5);
lean_inc_ref(v_needs_2584_);
v_extraDepTargets_2585_ = lean_ctor_get(v_config_2567_, 6);
lean_inc_ref(v_extraDepTargets_2585_);
lean_dec(v_config_2567_);
v___x_2586_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_2587_ = lean_string_append(v___x_2581_, v___x_2586_);
v___x_2588_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2566_, v___x_2580_);
v___x_2589_ = lean_string_append(v___x_2587_, v___x_2588_);
lean_dec_ref(v___x_2588_);
v___x_2590_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_2591_ = lean_string_append(v___x_2589_, v___x_2590_);
v___x_2592_ = 0;
v___x_2593_ = 0;
v___x_2594_ = l_Lake_BuildTrace_nil(v___x_2591_);
v___x_2595_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2595_, 0, v___x_2583_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
lean_ctor_set(v___x_2595_, 2, v___x_2582_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*3, v___x_2592_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*3 + 1, v___x_2593_);
v___x_2596_ = lean_box(0);
v___x_2597_ = lean_box(0);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 1, v___x_2595_);
lean_ctor_set(v___x_2578_, 0, v___x_2597_);
v___x_2599_ = v___x_2578_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v___x_2595_);
v___x_2599_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v_job_2602_; lean_object* v___x_2603_; size_t v_sz_2604_; size_t v___x_2605_; lean_object* v___x_2606_; 
v___x_2600_ = lean_task_pure(v___x_2599_);
v___x_2601_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_2602_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_2602_, 0, v___x_2600_);
lean_ctor_set(v_job_2602_, 1, v___x_2596_);
lean_ctor_set(v_job_2602_, 2, v___x_2601_);
lean_ctor_set_uint8(v_job_2602_, sizeof(void*)*3, v___x_2593_);
v___x_2603_ = l_Lake_Job_mix___redArg(v_job_2602_, v_a_2575_);
v_sz_2604_ = lean_array_size(v_extraDepTargets_2585_);
v___x_2605_ = ((size_t)0ULL);
lean_inc_ref(v_a_2562_);
lean_inc(v_a_2561_);
lean_inc(v_a_2560_);
lean_inc(v_a_2559_);
lean_inc_ref(v_a_2558_);
lean_inc_ref(v_pkg_2565_);
v___x_2606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_2565_, v_extraDepTargets_2585_, v_sz_2604_, v___x_2605_, v___x_2603_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2576_);
lean_dec_ref(v_extraDepTargets_2585_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v_a_2608_; size_t v_sz_2609_; lean_object* v___x_2610_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
v_a_2608_ = lean_ctor_get(v___x_2606_, 1);
lean_inc(v_a_2608_);
lean_dec_ref(v___x_2606_);
v_sz_2609_ = lean_array_size(v_needs_2584_);
v___x_2610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_2565_, v_needs_2584_, v_sz_2609_, v___x_2605_, v_a_2607_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2608_);
lean_dec_ref(v_needs_2584_);
return v___x_2610_;
}
else
{
lean_dec_ref(v_needs_2584_);
lean_dec_ref(v_pkg_2565_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
return v___x_2606_;
}
}
}
}
else
{
lean_dec(v_config_2567_);
lean_dec(v_name_2566_);
lean_dec_ref(v_pkg_2565_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
return v___x_2574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_);
return v_res_2621_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2623_; uint8_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___f_2623_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_2624_ = 1;
v___x_2625_ = l_Lake_instDataKindUnit;
v___x_2626_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_2627_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2628_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
lean_ctor_set(v___x_2628_, 1, v___x_2626_);
lean_ctor_set(v___x_2628_, 2, v___x_2625_);
lean_ctor_set(v___x_2628_, 3, v___f_2623_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*4, v___x_2624_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*4 + 1, v___x_2624_);
return v___x_2628_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_2630_, size_t v_sz_2631_, size_t v_i_2632_, lean_object* v_bs_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
uint8_t v___x_2641_; 
v___x_2641_ = lean_usize_dec_lt(v_i_2632_, v_sz_2631_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; 
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec_ref(v_self_2630_);
v___x_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2642_, 0, v_bs_2633_);
lean_ctor_set(v___x_2642_, 1, v___y_2639_);
return v___x_2642_;
}
else
{
lean_object* v_pkg_2643_; lean_object* v_name_2644_; lean_object* v_keyName_2645_; lean_object* v_v_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_pkg_2643_ = lean_ctor_get(v_self_2630_, 0);
v_name_2644_ = lean_ctor_get(v_self_2630_, 1);
v_keyName_2645_ = lean_ctor_get(v_pkg_2643_, 2);
v_v_2646_ = lean_array_uget_borrowed(v_bs_2633_, v_i_2632_);
lean_inc(v_name_2644_);
lean_inc(v_keyName_2645_);
v___x_2647_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2647_, 0, v_keyName_2645_);
lean_ctor_set(v___x_2647_, 1, v_name_2644_);
v___x_2648_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc(v_v_2646_);
lean_inc_ref(v_self_2630_);
v___x_2649_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2647_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
lean_ctor_set(v___x_2649_, 2, v_self_2630_);
lean_ctor_set(v___x_2649_, 3, v_v_2646_);
lean_inc_ref(v___y_2634_);
lean_inc_ref(v___y_2638_);
lean_inc(v___y_2637_);
lean_inc(v___y_2636_);
lean_inc(v___y_2635_);
v___x_2650_ = lean_apply_7(v___y_2634_, v___x_2649_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, lean_box(0));
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v_a_2652_; lean_object* v___x_2653_; lean_object* v_bs_x27_2654_; lean_object* v___x_2655_; size_t v___x_2656_; size_t v___x_2657_; lean_object* v___x_2658_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
v_a_2652_ = lean_ctor_get(v___x_2650_, 1);
lean_inc(v_a_2652_);
lean_dec_ref(v___x_2650_);
v___x_2653_ = lean_unsigned_to_nat(0u);
v_bs_x27_2654_ = lean_array_uset(v_bs_2633_, v_i_2632_, v___x_2653_);
v___x_2655_ = l_Lake_Job_toOpaque___redArg(v_a_2651_);
v___x_2656_ = ((size_t)1ULL);
v___x_2657_ = lean_usize_add(v_i_2632_, v___x_2656_);
v___x_2658_ = lean_array_uset(v_bs_x27_2654_, v_i_2632_, v___x_2655_);
v_i_2632_ = v___x_2657_;
v_bs_2633_ = v___x_2658_;
v___y_2639_ = v_a_2652_;
goto _start;
}
else
{
lean_object* v_a_2660_; lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec_ref(v_bs_2633_);
lean_dec_ref(v_self_2630_);
v_a_2660_ = lean_ctor_get(v___x_2650_, 0);
v_a_2661_ = lean_ctor_get(v___x_2650_, 1);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2650_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_inc(v_a_2660_);
lean_dec(v___x_2650_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2660_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_2669_, lean_object* v_sz_2670_, lean_object* v_i_2671_, lean_object* v_bs_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
size_t v_sz_boxed_2680_; size_t v_i_boxed_2681_; lean_object* v_res_2682_; 
v_sz_boxed_2680_ = lean_unbox_usize(v_sz_2670_);
lean_dec(v_sz_2670_);
v_i_boxed_2681_ = lean_unbox_usize(v_i_2671_);
lean_dec(v_i_2671_);
v_res_2682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_2669_, v_sz_boxed_2680_, v_i_boxed_2681_, v_bs_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v_config_2692_; lean_object* v_defaultFacets_2693_; size_t v_sz_2694_; size_t v___x_2695_; lean_object* v___x_2696_; 
v_config_2692_ = lean_ctor_get(v_self_2684_, 2);
v_defaultFacets_2693_ = lean_ctor_get(v_config_2692_, 7);
lean_inc_ref(v_defaultFacets_2693_);
v_sz_2694_ = lean_array_size(v_defaultFacets_2693_);
v___x_2695_ = ((size_t)0ULL);
v___x_2696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_2684_, v_sz_2694_, v___x_2695_, v_defaultFacets_2693_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2707_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
v_a_2698_ = lean_ctor_get(v___x_2696_, 1);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2700_ = v___x_2696_;
v_isShared_2701_ = v_isSharedCheck_2707_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_inc(v_a_2697_);
lean_dec(v___x_2696_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2707_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2702_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_2703_ = l_Lake_Job_mixArray___redArg(v_a_2697_, v___x_2702_);
lean_dec(v_a_2697_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2703_);
v___x_2705_ = v___x_2700_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_a_2698_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
v_a_2708_ = lean_ctor_get(v___x_2696_, 0);
v_a_2709_ = lean_ctor_get(v___x_2696_, 1);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2696_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_inc(v_a_2708_);
lean_dec(v___x_2696_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2708_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
return v_res_2725_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2727_; uint8_t v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___f_2727_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_2728_ = 1;
v___x_2729_ = l_Lake_instDataKindUnit;
v___x_2730_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_2731_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2732_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
lean_ctor_set(v___x_2732_, 1, v___x_2730_);
lean_ctor_set(v___x_2732_, 2, v___x_2729_);
lean_ctor_set(v___x_2732_, 3, v___f_2727_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*4, v___x_2728_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*4 + 1, v___x_2728_);
return v___x_2732_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_2734_, lean_object* v_v_2735_, lean_object* v_t_2736_){
_start:
{
if (lean_obj_tag(v_t_2736_) == 0)
{
lean_object* v_size_2737_; lean_object* v_k_2738_; lean_object* v_v_2739_; lean_object* v_l_2740_; lean_object* v_r_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_3021_; 
v_size_2737_ = lean_ctor_get(v_t_2736_, 0);
v_k_2738_ = lean_ctor_get(v_t_2736_, 1);
v_v_2739_ = lean_ctor_get(v_t_2736_, 2);
v_l_2740_ = lean_ctor_get(v_t_2736_, 3);
v_r_2741_ = lean_ctor_get(v_t_2736_, 4);
v_isSharedCheck_3021_ = !lean_is_exclusive(v_t_2736_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2743_ = v_t_2736_;
v_isShared_2744_ = v_isSharedCheck_3021_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_r_2741_);
lean_inc(v_l_2740_);
lean_inc(v_v_2739_);
lean_inc(v_k_2738_);
lean_inc(v_size_2737_);
lean_dec(v_t_2736_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_3021_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
uint8_t v___x_2745_; 
v___x_2745_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2734_, v_k_2738_);
switch(v___x_2745_)
{
case 0:
{
lean_object* v_impl_2746_; lean_object* v___x_2747_; 
lean_dec(v_size_2737_);
v_impl_2746_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_2734_, v_v_2735_, v_l_2740_);
v___x_2747_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2741_) == 0)
{
lean_object* v_size_2748_; lean_object* v_size_2749_; lean_object* v_k_2750_; lean_object* v_v_2751_; lean_object* v_l_2752_; lean_object* v_r_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v_size_2748_ = lean_ctor_get(v_r_2741_, 0);
v_size_2749_ = lean_ctor_get(v_impl_2746_, 0);
lean_inc(v_size_2749_);
v_k_2750_ = lean_ctor_get(v_impl_2746_, 1);
lean_inc(v_k_2750_);
v_v_2751_ = lean_ctor_get(v_impl_2746_, 2);
lean_inc(v_v_2751_);
v_l_2752_ = lean_ctor_get(v_impl_2746_, 3);
lean_inc(v_l_2752_);
v_r_2753_ = lean_ctor_get(v_impl_2746_, 4);
lean_inc(v_r_2753_);
v___x_2754_ = lean_unsigned_to_nat(3u);
v___x_2755_ = lean_nat_mul(v___x_2754_, v_size_2748_);
v___x_2756_ = lean_nat_dec_lt(v___x_2755_, v_size_2749_);
lean_dec(v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; 
lean_dec(v_r_2753_);
lean_dec(v_l_2752_);
lean_dec(v_v_2751_);
lean_dec(v_k_2750_);
v___x_2757_ = lean_nat_add(v___x_2747_, v_size_2749_);
lean_dec(v_size_2749_);
v___x_2758_ = lean_nat_add(v___x_2757_, v_size_2748_);
lean_dec(v___x_2757_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 3, v_impl_2746_);
lean_ctor_set(v___x_2743_, 0, v___x_2758_);
v___x_2760_ = v___x_2743_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2758_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_2761_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_2761_, 3, v_impl_2746_);
lean_ctor_set(v_reuseFailAlloc_2761_, 4, v_r_2741_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
else
{
lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2827_; 
v_isSharedCheck_2827_ = !lean_is_exclusive(v_impl_2746_);
if (v_isSharedCheck_2827_ == 0)
{
lean_object* v_unused_2828_; lean_object* v_unused_2829_; lean_object* v_unused_2830_; lean_object* v_unused_2831_; lean_object* v_unused_2832_; 
v_unused_2828_ = lean_ctor_get(v_impl_2746_, 4);
lean_dec(v_unused_2828_);
v_unused_2829_ = lean_ctor_get(v_impl_2746_, 3);
lean_dec(v_unused_2829_);
v_unused_2830_ = lean_ctor_get(v_impl_2746_, 2);
lean_dec(v_unused_2830_);
v_unused_2831_ = lean_ctor_get(v_impl_2746_, 1);
lean_dec(v_unused_2831_);
v_unused_2832_ = lean_ctor_get(v_impl_2746_, 0);
lean_dec(v_unused_2832_);
v___x_2763_ = v_impl_2746_;
v_isShared_2764_ = v_isSharedCheck_2827_;
goto v_resetjp_2762_;
}
else
{
lean_dec(v_impl_2746_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2827_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v_size_2765_; lean_object* v_size_2766_; lean_object* v_k_2767_; lean_object* v_v_2768_; lean_object* v_l_2769_; lean_object* v_r_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v_size_2765_ = lean_ctor_get(v_l_2752_, 0);
v_size_2766_ = lean_ctor_get(v_r_2753_, 0);
v_k_2767_ = lean_ctor_get(v_r_2753_, 1);
v_v_2768_ = lean_ctor_get(v_r_2753_, 2);
v_l_2769_ = lean_ctor_get(v_r_2753_, 3);
v_r_2770_ = lean_ctor_get(v_r_2753_, 4);
v___x_2771_ = lean_unsigned_to_nat(2u);
v___x_2772_ = lean_nat_mul(v___x_2771_, v_size_2765_);
v___x_2773_ = lean_nat_dec_lt(v_size_2766_, v___x_2772_);
lean_dec(v___x_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2802_; 
lean_inc(v_r_2770_);
lean_inc(v_l_2769_);
lean_inc(v_v_2768_);
lean_inc(v_k_2767_);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_r_2753_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; lean_object* v_unused_2804_; lean_object* v_unused_2805_; lean_object* v_unused_2806_; lean_object* v_unused_2807_; 
v_unused_2803_ = lean_ctor_get(v_r_2753_, 4);
lean_dec(v_unused_2803_);
v_unused_2804_ = lean_ctor_get(v_r_2753_, 3);
lean_dec(v_unused_2804_);
v_unused_2805_ = lean_ctor_get(v_r_2753_, 2);
lean_dec(v_unused_2805_);
v_unused_2806_ = lean_ctor_get(v_r_2753_, 1);
lean_dec(v_unused_2806_);
v_unused_2807_ = lean_ctor_get(v_r_2753_, 0);
lean_dec(v_unused_2807_);
v___x_2775_ = v_r_2753_;
v_isShared_2776_ = v_isSharedCheck_2802_;
goto v_resetjp_2774_;
}
else
{
lean_dec(v_r_2753_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2802_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___x_2790_; lean_object* v___y_2792_; 
v___x_2777_ = lean_nat_add(v___x_2747_, v_size_2749_);
lean_dec(v_size_2749_);
v___x_2778_ = lean_nat_add(v___x_2777_, v_size_2748_);
lean_dec(v___x_2777_);
v___x_2790_ = lean_nat_add(v___x_2747_, v_size_2765_);
if (lean_obj_tag(v_l_2769_) == 0)
{
lean_object* v_size_2800_; 
v_size_2800_ = lean_ctor_get(v_l_2769_, 0);
lean_inc(v_size_2800_);
v___y_2792_ = v_size_2800_;
goto v___jp_2791_;
}
else
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_unsigned_to_nat(0u);
v___y_2792_ = v___x_2801_;
goto v___jp_2791_;
}
v___jp_2779_:
{
lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2783_ = lean_nat_add(v___y_2780_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec(v___y_2780_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 4, v_r_2741_);
lean_ctor_set(v___x_2775_, 3, v_r_2770_);
lean_ctor_set(v___x_2775_, 2, v_v_2739_);
lean_ctor_set(v___x_2775_, 1, v_k_2738_);
lean_ctor_set(v___x_2775_, 0, v___x_2783_);
v___x_2785_ = v___x_2775_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_2789_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_2789_, 3, v_r_2770_);
lean_ctor_set(v_reuseFailAlloc_2789_, 4, v_r_2741_);
v___x_2785_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2787_; 
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 4, v___x_2785_);
lean_ctor_set(v___x_2763_, 3, v___y_2781_);
lean_ctor_set(v___x_2763_, 2, v_v_2768_);
lean_ctor_set(v___x_2763_, 1, v_k_2767_);
lean_ctor_set(v___x_2763_, 0, v___x_2778_);
v___x_2787_ = v___x_2763_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_k_2767_);
lean_ctor_set(v_reuseFailAlloc_2788_, 2, v_v_2768_);
lean_ctor_set(v_reuseFailAlloc_2788_, 3, v___y_2781_);
lean_ctor_set(v_reuseFailAlloc_2788_, 4, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
v___jp_2791_:
{
lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2793_ = lean_nat_add(v___x_2790_, v___y_2792_);
lean_dec(v___y_2792_);
lean_dec(v___x_2790_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v_l_2769_);
lean_ctor_set(v___x_2743_, 3, v_l_2752_);
lean_ctor_set(v___x_2743_, 2, v_v_2751_);
lean_ctor_set(v___x_2743_, 1, v_k_2750_);
lean_ctor_set(v___x_2743_, 0, v___x_2793_);
v___x_2795_ = v___x_2743_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_k_2750_);
lean_ctor_set(v_reuseFailAlloc_2799_, 2, v_v_2751_);
lean_ctor_set(v_reuseFailAlloc_2799_, 3, v_l_2752_);
lean_ctor_set(v_reuseFailAlloc_2799_, 4, v_l_2769_);
v___x_2795_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; 
v___x_2796_ = lean_nat_add(v___x_2747_, v_size_2748_);
if (lean_obj_tag(v_r_2770_) == 0)
{
lean_object* v_size_2797_; 
v_size_2797_ = lean_ctor_get(v_r_2770_, 0);
lean_inc(v_size_2797_);
v___y_2780_ = v___x_2796_;
v___y_2781_ = v___x_2795_;
v___y_2782_ = v_size_2797_;
goto v___jp_2779_;
}
else
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_unsigned_to_nat(0u);
v___y_2780_ = v___x_2796_;
v___y_2781_ = v___x_2795_;
v___y_2782_ = v___x_2798_;
goto v___jp_2779_;
}
}
}
}
}
else
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
lean_del_object(v___x_2743_);
v___x_2808_ = lean_nat_add(v___x_2747_, v_size_2749_);
lean_dec(v_size_2749_);
v___x_2809_ = lean_nat_add(v___x_2808_, v_size_2748_);
lean_dec(v___x_2808_);
v___x_2810_ = lean_nat_add(v___x_2747_, v_size_2748_);
v___x_2811_ = lean_nat_add(v___x_2810_, v_size_2766_);
lean_dec(v___x_2810_);
lean_inc_ref(v_r_2741_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 4, v_r_2741_);
lean_ctor_set(v___x_2763_, 3, v_r_2753_);
lean_ctor_set(v___x_2763_, 2, v_v_2739_);
lean_ctor_set(v___x_2763_, 1, v_k_2738_);
lean_ctor_set(v___x_2763_, 0, v___x_2811_);
v___x_2813_ = v___x_2763_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_r_2753_);
lean_ctor_set(v_reuseFailAlloc_2826_, 4, v_r_2741_);
v___x_2813_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v_isSharedCheck_2820_ = !lean_is_exclusive(v_r_2741_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; lean_object* v_unused_2822_; lean_object* v_unused_2823_; lean_object* v_unused_2824_; lean_object* v_unused_2825_; 
v_unused_2821_ = lean_ctor_get(v_r_2741_, 4);
lean_dec(v_unused_2821_);
v_unused_2822_ = lean_ctor_get(v_r_2741_, 3);
lean_dec(v_unused_2822_);
v_unused_2823_ = lean_ctor_get(v_r_2741_, 2);
lean_dec(v_unused_2823_);
v_unused_2824_ = lean_ctor_get(v_r_2741_, 1);
lean_dec(v_unused_2824_);
v_unused_2825_ = lean_ctor_get(v_r_2741_, 0);
lean_dec(v_unused_2825_);
v___x_2815_ = v_r_2741_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_dec(v_r_2741_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 4, v___x_2813_);
lean_ctor_set(v___x_2815_, 3, v_l_2752_);
lean_ctor_set(v___x_2815_, 2, v_v_2751_);
lean_ctor_set(v___x_2815_, 1, v_k_2750_);
lean_ctor_set(v___x_2815_, 0, v___x_2809_);
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2809_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_k_2750_);
lean_ctor_set(v_reuseFailAlloc_2819_, 2, v_v_2751_);
lean_ctor_set(v_reuseFailAlloc_2819_, 3, v_l_2752_);
lean_ctor_set(v_reuseFailAlloc_2819_, 4, v___x_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2833_; 
v_l_2833_ = lean_ctor_get(v_impl_2746_, 3);
lean_inc(v_l_2833_);
if (lean_obj_tag(v_l_2833_) == 0)
{
lean_object* v_r_2834_; lean_object* v_k_2835_; lean_object* v_v_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2847_; 
v_r_2834_ = lean_ctor_get(v_impl_2746_, 4);
v_k_2835_ = lean_ctor_get(v_impl_2746_, 1);
v_v_2836_ = lean_ctor_get(v_impl_2746_, 2);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_impl_2746_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; lean_object* v_unused_2849_; 
v_unused_2848_ = lean_ctor_get(v_impl_2746_, 3);
lean_dec(v_unused_2848_);
v_unused_2849_ = lean_ctor_get(v_impl_2746_, 0);
lean_dec(v_unused_2849_);
v___x_2838_ = v_impl_2746_;
v_isShared_2839_ = v_isSharedCheck_2847_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_r_2834_);
lean_inc(v_v_2836_);
lean_inc(v_k_2835_);
lean_dec(v_impl_2746_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2847_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2840_; lean_object* v___x_2842_; 
v___x_2840_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2834_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 3, v_r_2834_);
lean_ctor_set(v___x_2838_, 2, v_v_2739_);
lean_ctor_set(v___x_2838_, 1, v_k_2738_);
lean_ctor_set(v___x_2838_, 0, v___x_2747_);
v___x_2842_ = v___x_2838_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_2846_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_2846_, 3, v_r_2834_);
lean_ctor_set(v_reuseFailAlloc_2846_, 4, v_r_2834_);
v___x_2842_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2844_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v___x_2842_);
lean_ctor_set(v___x_2743_, 3, v_l_2833_);
lean_ctor_set(v___x_2743_, 2, v_v_2836_);
lean_ctor_set(v___x_2743_, 1, v_k_2835_);
lean_ctor_set(v___x_2743_, 0, v___x_2840_);
v___x_2844_ = v___x_2743_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2840_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_k_2835_);
lean_ctor_set(v_reuseFailAlloc_2845_, 2, v_v_2836_);
lean_ctor_set(v_reuseFailAlloc_2845_, 3, v_l_2833_);
lean_ctor_set(v_reuseFailAlloc_2845_, 4, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
else
{
lean_object* v_r_2850_; 
v_r_2850_ = lean_ctor_get(v_impl_2746_, 4);
lean_inc(v_r_2850_);
if (lean_obj_tag(v_r_2850_) == 0)
{
lean_object* v_k_2851_; lean_object* v_v_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2875_; 
v_k_2851_ = lean_ctor_get(v_impl_2746_, 1);
v_v_2852_ = lean_ctor_get(v_impl_2746_, 2);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_impl_2746_);
if (v_isSharedCheck_2875_ == 0)
{
lean_object* v_unused_2876_; lean_object* v_unused_2877_; lean_object* v_unused_2878_; 
v_unused_2876_ = lean_ctor_get(v_impl_2746_, 4);
lean_dec(v_unused_2876_);
v_unused_2877_ = lean_ctor_get(v_impl_2746_, 3);
lean_dec(v_unused_2877_);
v_unused_2878_ = lean_ctor_get(v_impl_2746_, 0);
lean_dec(v_unused_2878_);
v___x_2854_ = v_impl_2746_;
v_isShared_2855_ = v_isSharedCheck_2875_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_v_2852_);
lean_inc(v_k_2851_);
lean_dec(v_impl_2746_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2875_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v_k_2856_; lean_object* v_v_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2871_; 
v_k_2856_ = lean_ctor_get(v_r_2850_, 1);
v_v_2857_ = lean_ctor_get(v_r_2850_, 2);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_r_2850_);
if (v_isSharedCheck_2871_ == 0)
{
lean_object* v_unused_2872_; lean_object* v_unused_2873_; lean_object* v_unused_2874_; 
v_unused_2872_ = lean_ctor_get(v_r_2850_, 4);
lean_dec(v_unused_2872_);
v_unused_2873_ = lean_ctor_get(v_r_2850_, 3);
lean_dec(v_unused_2873_);
v_unused_2874_ = lean_ctor_get(v_r_2850_, 0);
lean_dec(v_unused_2874_);
v___x_2859_ = v_r_2850_;
v_isShared_2860_ = v_isSharedCheck_2871_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_v_2857_);
lean_inc(v_k_2856_);
lean_dec(v_r_2850_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2871_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2861_ = lean_unsigned_to_nat(3u);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 4, v_l_2833_);
lean_ctor_set(v___x_2859_, 3, v_l_2833_);
lean_ctor_set(v___x_2859_, 2, v_v_2852_);
lean_ctor_set(v___x_2859_, 1, v_k_2851_);
lean_ctor_set(v___x_2859_, 0, v___x_2747_);
v___x_2863_ = v___x_2859_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_k_2851_);
lean_ctor_set(v_reuseFailAlloc_2870_, 2, v_v_2852_);
lean_ctor_set(v_reuseFailAlloc_2870_, 3, v_l_2833_);
lean_ctor_set(v_reuseFailAlloc_2870_, 4, v_l_2833_);
v___x_2863_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2865_; 
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 4, v_l_2833_);
lean_ctor_set(v___x_2854_, 2, v_v_2739_);
lean_ctor_set(v___x_2854_, 1, v_k_2738_);
lean_ctor_set(v___x_2854_, 0, v___x_2747_);
v___x_2865_ = v___x_2854_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_2869_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_2869_, 3, v_l_2833_);
lean_ctor_set(v_reuseFailAlloc_2869_, 4, v_l_2833_);
v___x_2865_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2867_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v___x_2865_);
lean_ctor_set(v___x_2743_, 3, v___x_2863_);
lean_ctor_set(v___x_2743_, 2, v_v_2857_);
lean_ctor_set(v___x_2743_, 1, v_k_2856_);
lean_ctor_set(v___x_2743_, 0, v___x_2861_);
v___x_2867_ = v___x_2743_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_k_2856_);
lean_ctor_set(v_reuseFailAlloc_2868_, 2, v_v_2857_);
lean_ctor_set(v_reuseFailAlloc_2868_, 3, v___x_2863_);
lean_ctor_set(v_reuseFailAlloc_2868_, 4, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2879_ = lean_unsigned_to_nat(2u);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v_r_2850_);
lean_ctor_set(v___x_2743_, 3, v_impl_2746_);
lean_ctor_set(v___x_2743_, 0, v___x_2879_);
v___x_2881_ = v___x_2743_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_2882_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_2882_, 3, v_impl_2746_);
lean_ctor_set(v_reuseFailAlloc_2882_, 4, v_r_2850_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2884_; 
lean_dec(v_v_2739_);
lean_dec(v_k_2738_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 2, v_v_2735_);
lean_ctor_set(v___x_2743_, 1, v_k_2734_);
v___x_2884_ = v___x_2743_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_size_2737_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_k_2734_);
lean_ctor_set(v_reuseFailAlloc_2885_, 2, v_v_2735_);
lean_ctor_set(v_reuseFailAlloc_2885_, 3, v_l_2740_);
lean_ctor_set(v_reuseFailAlloc_2885_, 4, v_r_2741_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
default: 
{
lean_object* v_impl_2886_; lean_object* v___x_2887_; 
lean_dec(v_size_2737_);
v_impl_2886_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_2734_, v_v_2735_, v_r_2741_);
v___x_2887_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2740_) == 0)
{
lean_object* v_size_2888_; lean_object* v_size_2889_; lean_object* v_k_2890_; lean_object* v_v_2891_; lean_object* v_l_2892_; lean_object* v_r_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; 
v_size_2888_ = lean_ctor_get(v_l_2740_, 0);
v_size_2889_ = lean_ctor_get(v_impl_2886_, 0);
lean_inc(v_size_2889_);
v_k_2890_ = lean_ctor_get(v_impl_2886_, 1);
lean_inc(v_k_2890_);
v_v_2891_ = lean_ctor_get(v_impl_2886_, 2);
lean_inc(v_v_2891_);
v_l_2892_ = lean_ctor_get(v_impl_2886_, 3);
lean_inc(v_l_2892_);
v_r_2893_ = lean_ctor_get(v_impl_2886_, 4);
lean_inc(v_r_2893_);
v___x_2894_ = lean_unsigned_to_nat(3u);
v___x_2895_ = lean_nat_mul(v___x_2894_, v_size_2888_);
v___x_2896_ = lean_nat_dec_lt(v___x_2895_, v_size_2889_);
lean_dec(v___x_2895_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
lean_dec(v_r_2893_);
lean_dec(v_l_2892_);
lean_dec(v_v_2891_);
lean_dec(v_k_2890_);
v___x_2897_ = lean_nat_add(v___x_2887_, v_size_2888_);
v___x_2898_ = lean_nat_add(v___x_2897_, v_size_2889_);
lean_dec(v_size_2889_);
lean_dec(v___x_2897_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v_impl_2886_);
lean_ctor_set(v___x_2743_, 0, v___x_2898_);
v___x_2900_ = v___x_2743_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_2901_, 3, v_l_2740_);
lean_ctor_set(v_reuseFailAlloc_2901_, 4, v_impl_2886_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
else
{
lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2965_; 
v_isSharedCheck_2965_ = !lean_is_exclusive(v_impl_2886_);
if (v_isSharedCheck_2965_ == 0)
{
lean_object* v_unused_2966_; lean_object* v_unused_2967_; lean_object* v_unused_2968_; lean_object* v_unused_2969_; lean_object* v_unused_2970_; 
v_unused_2966_ = lean_ctor_get(v_impl_2886_, 4);
lean_dec(v_unused_2966_);
v_unused_2967_ = lean_ctor_get(v_impl_2886_, 3);
lean_dec(v_unused_2967_);
v_unused_2968_ = lean_ctor_get(v_impl_2886_, 2);
lean_dec(v_unused_2968_);
v_unused_2969_ = lean_ctor_get(v_impl_2886_, 1);
lean_dec(v_unused_2969_);
v_unused_2970_ = lean_ctor_get(v_impl_2886_, 0);
lean_dec(v_unused_2970_);
v___x_2903_ = v_impl_2886_;
v_isShared_2904_ = v_isSharedCheck_2965_;
goto v_resetjp_2902_;
}
else
{
lean_dec(v_impl_2886_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2965_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v_size_2905_; lean_object* v_k_2906_; lean_object* v_v_2907_; lean_object* v_l_2908_; lean_object* v_r_2909_; lean_object* v_size_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; uint8_t v___x_2913_; 
v_size_2905_ = lean_ctor_get(v_l_2892_, 0);
v_k_2906_ = lean_ctor_get(v_l_2892_, 1);
v_v_2907_ = lean_ctor_get(v_l_2892_, 2);
v_l_2908_ = lean_ctor_get(v_l_2892_, 3);
v_r_2909_ = lean_ctor_get(v_l_2892_, 4);
v_size_2910_ = lean_ctor_get(v_r_2893_, 0);
v___x_2911_ = lean_unsigned_to_nat(2u);
v___x_2912_ = lean_nat_mul(v___x_2911_, v_size_2910_);
v___x_2913_ = lean_nat_dec_lt(v_size_2905_, v___x_2912_);
lean_dec(v___x_2912_);
if (v___x_2913_ == 0)
{
lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2941_; 
lean_inc(v_r_2909_);
lean_inc(v_l_2908_);
lean_inc(v_v_2907_);
lean_inc(v_k_2906_);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_l_2892_);
if (v_isSharedCheck_2941_ == 0)
{
lean_object* v_unused_2942_; lean_object* v_unused_2943_; lean_object* v_unused_2944_; lean_object* v_unused_2945_; lean_object* v_unused_2946_; 
v_unused_2942_ = lean_ctor_get(v_l_2892_, 4);
lean_dec(v_unused_2942_);
v_unused_2943_ = lean_ctor_get(v_l_2892_, 3);
lean_dec(v_unused_2943_);
v_unused_2944_ = lean_ctor_get(v_l_2892_, 2);
lean_dec(v_unused_2944_);
v_unused_2945_ = lean_ctor_get(v_l_2892_, 1);
lean_dec(v_unused_2945_);
v_unused_2946_ = lean_ctor_get(v_l_2892_, 0);
lean_dec(v_unused_2946_);
v___x_2915_ = v_l_2892_;
v_isShared_2916_ = v_isSharedCheck_2941_;
goto v_resetjp_2914_;
}
else
{
lean_dec(v_l_2892_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2941_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2931_; 
v___x_2917_ = lean_nat_add(v___x_2887_, v_size_2888_);
v___x_2918_ = lean_nat_add(v___x_2917_, v_size_2889_);
lean_dec(v_size_2889_);
if (lean_obj_tag(v_l_2908_) == 0)
{
lean_object* v_size_2939_; 
v_size_2939_ = lean_ctor_get(v_l_2908_, 0);
lean_inc(v_size_2939_);
v___y_2931_ = v_size_2939_;
goto v___jp_2930_;
}
else
{
lean_object* v___x_2940_; 
v___x_2940_ = lean_unsigned_to_nat(0u);
v___y_2931_ = v___x_2940_;
goto v___jp_2930_;
}
v___jp_2919_:
{
lean_object* v___x_2923_; lean_object* v___x_2925_; 
v___x_2923_ = lean_nat_add(v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec(v___y_2921_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 4, v_r_2893_);
lean_ctor_set(v___x_2915_, 3, v_r_2909_);
lean_ctor_set(v___x_2915_, 2, v_v_2891_);
lean_ctor_set(v___x_2915_, 1, v_k_2890_);
lean_ctor_set(v___x_2915_, 0, v___x_2923_);
v___x_2925_ = v___x_2915_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2923_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_k_2890_);
lean_ctor_set(v_reuseFailAlloc_2929_, 2, v_v_2891_);
lean_ctor_set(v_reuseFailAlloc_2929_, 3, v_r_2909_);
lean_ctor_set(v_reuseFailAlloc_2929_, 4, v_r_2893_);
v___x_2925_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2927_; 
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 4, v___x_2925_);
lean_ctor_set(v___x_2903_, 3, v___y_2920_);
lean_ctor_set(v___x_2903_, 2, v_v_2907_);
lean_ctor_set(v___x_2903_, 1, v_k_2906_);
lean_ctor_set(v___x_2903_, 0, v___x_2918_);
v___x_2927_ = v___x_2903_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_k_2906_);
lean_ctor_set(v_reuseFailAlloc_2928_, 2, v_v_2907_);
lean_ctor_set(v_reuseFailAlloc_2928_, 3, v___y_2920_);
lean_ctor_set(v_reuseFailAlloc_2928_, 4, v___x_2925_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
v___jp_2930_:
{
lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2932_ = lean_nat_add(v___x_2917_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec(v___x_2917_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v_l_2908_);
lean_ctor_set(v___x_2743_, 0, v___x_2932_);
v___x_2934_ = v___x_2743_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_2938_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_2938_, 3, v_l_2740_);
lean_ctor_set(v_reuseFailAlloc_2938_, 4, v_l_2908_);
v___x_2934_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_nat_add(v___x_2887_, v_size_2910_);
if (lean_obj_tag(v_r_2909_) == 0)
{
lean_object* v_size_2936_; 
v_size_2936_ = lean_ctor_get(v_r_2909_, 0);
lean_inc(v_size_2936_);
v___y_2920_ = v___x_2934_;
v___y_2921_ = v___x_2935_;
v___y_2922_ = v_size_2936_;
goto v___jp_2919_;
}
else
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_unsigned_to_nat(0u);
v___y_2920_ = v___x_2934_;
v___y_2921_ = v___x_2935_;
v___y_2922_ = v___x_2937_;
goto v___jp_2919_;
}
}
}
}
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2951_; 
lean_del_object(v___x_2743_);
v___x_2947_ = lean_nat_add(v___x_2887_, v_size_2888_);
v___x_2948_ = lean_nat_add(v___x_2947_, v_size_2889_);
lean_dec(v_size_2889_);
v___x_2949_ = lean_nat_add(v___x_2947_, v_size_2905_);
lean_dec(v___x_2947_);
lean_inc_ref(v_l_2740_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 4, v_l_2892_);
lean_ctor_set(v___x_2903_, 3, v_l_2740_);
lean_ctor_set(v___x_2903_, 2, v_v_2739_);
lean_ctor_set(v___x_2903_, 1, v_k_2738_);
lean_ctor_set(v___x_2903_, 0, v___x_2949_);
v___x_2951_ = v___x_2903_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2949_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_2964_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_2964_, 3, v_l_2740_);
lean_ctor_set(v_reuseFailAlloc_2964_, 4, v_l_2892_);
v___x_2951_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
v_isSharedCheck_2958_ = !lean_is_exclusive(v_l_2740_);
if (v_isSharedCheck_2958_ == 0)
{
lean_object* v_unused_2959_; lean_object* v_unused_2960_; lean_object* v_unused_2961_; lean_object* v_unused_2962_; lean_object* v_unused_2963_; 
v_unused_2959_ = lean_ctor_get(v_l_2740_, 4);
lean_dec(v_unused_2959_);
v_unused_2960_ = lean_ctor_get(v_l_2740_, 3);
lean_dec(v_unused_2960_);
v_unused_2961_ = lean_ctor_get(v_l_2740_, 2);
lean_dec(v_unused_2961_);
v_unused_2962_ = lean_ctor_get(v_l_2740_, 1);
lean_dec(v_unused_2962_);
v_unused_2963_ = lean_ctor_get(v_l_2740_, 0);
lean_dec(v_unused_2963_);
v___x_2953_ = v_l_2740_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_dec(v_l_2740_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 4, v_r_2893_);
lean_ctor_set(v___x_2953_, 3, v___x_2951_);
lean_ctor_set(v___x_2953_, 2, v_v_2891_);
lean_ctor_set(v___x_2953_, 1, v_k_2890_);
lean_ctor_set(v___x_2953_, 0, v___x_2948_);
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_k_2890_);
lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_v_2891_);
lean_ctor_set(v_reuseFailAlloc_2957_, 3, v___x_2951_);
lean_ctor_set(v_reuseFailAlloc_2957_, 4, v_r_2893_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2971_; 
v_l_2971_ = lean_ctor_get(v_impl_2886_, 3);
lean_inc(v_l_2971_);
if (lean_obj_tag(v_l_2971_) == 0)
{
lean_object* v_r_2972_; lean_object* v_k_2973_; lean_object* v_v_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2997_; 
v_r_2972_ = lean_ctor_get(v_impl_2886_, 4);
v_k_2973_ = lean_ctor_get(v_impl_2886_, 1);
v_v_2974_ = lean_ctor_get(v_impl_2886_, 2);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_impl_2886_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; lean_object* v_unused_2999_; 
v_unused_2998_ = lean_ctor_get(v_impl_2886_, 3);
lean_dec(v_unused_2998_);
v_unused_2999_ = lean_ctor_get(v_impl_2886_, 0);
lean_dec(v_unused_2999_);
v___x_2976_ = v_impl_2886_;
v_isShared_2977_ = v_isSharedCheck_2997_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_r_2972_);
lean_inc(v_v_2974_);
lean_inc(v_k_2973_);
lean_dec(v_impl_2886_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2997_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v_k_2978_; lean_object* v_v_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2993_; 
v_k_2978_ = lean_ctor_get(v_l_2971_, 1);
v_v_2979_ = lean_ctor_get(v_l_2971_, 2);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_l_2971_);
if (v_isSharedCheck_2993_ == 0)
{
lean_object* v_unused_2994_; lean_object* v_unused_2995_; lean_object* v_unused_2996_; 
v_unused_2994_ = lean_ctor_get(v_l_2971_, 4);
lean_dec(v_unused_2994_);
v_unused_2995_ = lean_ctor_get(v_l_2971_, 3);
lean_dec(v_unused_2995_);
v_unused_2996_ = lean_ctor_get(v_l_2971_, 0);
lean_dec(v_unused_2996_);
v___x_2981_ = v_l_2971_;
v_isShared_2982_ = v_isSharedCheck_2993_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_v_2979_);
lean_inc(v_k_2978_);
lean_dec(v_l_2971_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2993_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2983_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2972_, 2);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 4, v_r_2972_);
lean_ctor_set(v___x_2981_, 3, v_r_2972_);
lean_ctor_set(v___x_2981_, 2, v_v_2739_);
lean_ctor_set(v___x_2981_, 1, v_k_2738_);
lean_ctor_set(v___x_2981_, 0, v___x_2887_);
v___x_2985_ = v___x_2981_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_2992_, 3, v_r_2972_);
lean_ctor_set(v_reuseFailAlloc_2992_, 4, v_r_2972_);
v___x_2985_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2987_; 
lean_inc(v_r_2972_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 3, v_r_2972_);
lean_ctor_set(v___x_2976_, 0, v___x_2887_);
v___x_2987_ = v___x_2976_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_k_2973_);
lean_ctor_set(v_reuseFailAlloc_2991_, 2, v_v_2974_);
lean_ctor_set(v_reuseFailAlloc_2991_, 3, v_r_2972_);
lean_ctor_set(v_reuseFailAlloc_2991_, 4, v_r_2972_);
v___x_2987_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2989_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v___x_2987_);
lean_ctor_set(v___x_2743_, 3, v___x_2985_);
lean_ctor_set(v___x_2743_, 2, v_v_2979_);
lean_ctor_set(v___x_2743_, 1, v_k_2978_);
lean_ctor_set(v___x_2743_, 0, v___x_2983_);
v___x_2989_ = v___x_2743_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_k_2978_);
lean_ctor_set(v_reuseFailAlloc_2990_, 2, v_v_2979_);
lean_ctor_set(v_reuseFailAlloc_2990_, 3, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2990_, 4, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
}
}
else
{
lean_object* v_r_3000_; 
v_r_3000_ = lean_ctor_get(v_impl_2886_, 4);
lean_inc(v_r_3000_);
if (lean_obj_tag(v_r_3000_) == 0)
{
lean_object* v_k_3001_; lean_object* v_v_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3013_; 
v_k_3001_ = lean_ctor_get(v_impl_2886_, 1);
v_v_3002_ = lean_ctor_get(v_impl_2886_, 2);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_impl_2886_);
if (v_isSharedCheck_3013_ == 0)
{
lean_object* v_unused_3014_; lean_object* v_unused_3015_; lean_object* v_unused_3016_; 
v_unused_3014_ = lean_ctor_get(v_impl_2886_, 4);
lean_dec(v_unused_3014_);
v_unused_3015_ = lean_ctor_get(v_impl_2886_, 3);
lean_dec(v_unused_3015_);
v_unused_3016_ = lean_ctor_get(v_impl_2886_, 0);
lean_dec(v_unused_3016_);
v___x_3004_ = v_impl_2886_;
v_isShared_3005_ = v_isSharedCheck_3013_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_v_3002_);
lean_inc(v_k_3001_);
lean_dec(v_impl_2886_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3013_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3006_; lean_object* v___x_3008_; 
v___x_3006_ = lean_unsigned_to_nat(3u);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 4, v_l_2971_);
lean_ctor_set(v___x_3004_, 2, v_v_2739_);
lean_ctor_set(v___x_3004_, 1, v_k_2738_);
lean_ctor_set(v___x_3004_, 0, v___x_2887_);
v___x_3008_ = v___x_3004_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_l_2971_);
lean_ctor_set(v_reuseFailAlloc_3012_, 4, v_l_2971_);
v___x_3008_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3010_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v_r_3000_);
lean_ctor_set(v___x_2743_, 3, v___x_3008_);
lean_ctor_set(v___x_2743_, 2, v_v_3002_);
lean_ctor_set(v___x_2743_, 1, v_k_3001_);
lean_ctor_set(v___x_2743_, 0, v___x_3006_);
v___x_3010_ = v___x_2743_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3006_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_k_3001_);
lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_v_3002_);
lean_ctor_set(v_reuseFailAlloc_3011_, 3, v___x_3008_);
lean_ctor_set(v_reuseFailAlloc_3011_, 4, v_r_3000_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3017_ = lean_unsigned_to_nat(2u);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v_impl_2886_);
lean_ctor_set(v___x_2743_, 3, v_r_3000_);
lean_ctor_set(v___x_2743_, 0, v___x_3017_);
v___x_3019_ = v___x_2743_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3017_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_3020_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_3020_, 3, v_r_3000_);
lean_ctor_set(v_reuseFailAlloc_3020_, 4, v_impl_2886_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
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
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_unsigned_to_nat(1u);
v___x_3023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
lean_ctor_set(v___x_3023_, 1, v_k_2734_);
lean_ctor_set(v___x_3023_, 2, v_v_2735_);
lean_ctor_set(v___x_3023_, 3, v_t_2736_);
lean_ctor_set(v___x_3023_, 4, v_t_2736_);
return v___x_3023_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3024_ = lean_box(1);
v___x_3025_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_3026_ = l_Lake_LeanLib_defaultFacet;
v___x_3027_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3026_, v___x_3025_, v___x_3024_);
return v___x_3027_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3028_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_3029_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_3030_ = l_Lake_LeanLib_modulesFacet;
v___x_3031_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3030_, v___x_3029_, v___x_3028_);
return v___x_3031_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3032_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_3033_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_3034_ = l_Lake_LeanLib_leanArtsFacet;
v___x_3035_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3034_, v___x_3033_, v___x_3032_);
return v___x_3035_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3036_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_3037_ = l_Lake_LeanLib_staticFacetConfig;
v___x_3038_ = l_Lake_LeanLib_staticFacet;
v___x_3039_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3038_, v___x_3037_, v___x_3036_);
return v___x_3039_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3040_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_3041_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_3042_ = l_Lake_LeanLib_staticExportFacet;
v___x_3043_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3042_, v___x_3041_, v___x_3040_);
return v___x_3043_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3044_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_3045_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_3046_ = l_Lake_LeanLib_sharedFacet;
v___x_3047_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3046_, v___x_3045_, v___x_3044_);
return v___x_3047_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3048_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_3049_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_3050_ = l_Lake_LeanLib_extraDepFacet;
v___x_3051_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3050_, v___x_3049_, v___x_3048_);
return v___x_3051_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3053_, lean_object* v_k_3054_, lean_object* v_v_3055_, lean_object* v_t_3056_, lean_object* v_hl_3057_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3054_, v_v_3055_, v_t_3056_);
return v___x_3058_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_3059_;
}
}
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Targets(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Target_Fetch(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Library(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Common(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Targets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Register(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Target_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_LeanLib_leanArtsFacetConfig = _init_l_Lake_LeanLib_leanArtsFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig);
l_Lake_LeanLib_staticFacetConfig = _init_l_Lake_LeanLib_staticFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig);
l_Lake_LeanLib_staticExportFacetConfig = _init_l_Lake_LeanLib_staticExportFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_staticExportFacetConfig);
l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5 = _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5);
l_Lake_LeanLib_sharedFacetConfig = _init_l_Lake_LeanLib_sharedFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig);
l_Lake_LeanLib_extraDepFacetConfig = _init_l_Lake_LeanLib_extraDepFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_extraDepFacetConfig);
l_Lake_LeanLib_defaultFacetConfig = _init_l_Lake_LeanLib_defaultFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_defaultFacetConfig);
l_Lake_LeanLib_initFacetConfigs = _init_l_Lake_LeanLib_initFacetConfigs();
lean_mark_persistent(l_Lake_LeanLib_initFacetConfigs);
l_Lake_initLibraryFacetConfigs = _init_l_Lake_initLibraryFacetConfigs();
lean_mark_persistent(l_Lake_initLibraryFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Library(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* initialize_Lake_Build_Common(uint8_t builtin);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* initialize_Lake_Build_Target_Fetch(uint8_t builtin);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Library(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Common(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Targets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Register(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Target_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Library(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Library(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Library(builtin);
}
#ifdef __cplusplus
}
#endif
