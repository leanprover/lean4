// Lean compiler output
// Module: Lake.Build.Library
// Imports: public import Lake.Config.FacetConfig import Lake.Build.Common import Lake.Build.Targets import Lake.Build.Job.Register import Lake.Build.Target.Fetch import Lake.Build.Infos import Lake.Util.Proc
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
extern lean_object* l_Lake_instDataKindFilePath;
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
extern lean_object* l_Lake_LeanLib_modulesFacet;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
extern uint8_t l_System_Platform_isOSX;
extern uint8_t l_System_Platform_isWindows;
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_LeanLib_libName(lean_object*);
lean_object* l_Lake_nameToStaticLib(lean_object*, uint8_t);
lean_object* l_Lake_Job_await___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_ModuleFacet_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
extern lean_object* l_Lake_instDataKindDynlib;
lean_object* l_Lake_nameToSharedLib(lean_object*, uint8_t);
uint8_t l_Lake_LeanLib_isPlugin(lean_object*);
lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_dynlibFacet;
extern lean_object* l_Lake_ExternLib_keyword;
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
lean_object* l_Lake_EquipT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_instMonadST(lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "filelist"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0_value;
static const lean_ctor_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1_value;
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "libtool"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2_value;
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "-static"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3_value;
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-o"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4_value;
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "-filelist"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5_value;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7;
static const lean_array_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "objs"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0_value;
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1_value;
static const lean_array_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t, lean_object*, uint8_t, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_lib_736_; lean_object* v_config_737_; lean_object* v_nativeFacets_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_741_; size_t v_sz_742_; size_t v___x_743_; lean_object* v___x_211959__overap_744_; lean_object* v___x_745_; 
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
v___x_211959__overap_744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_726_, v___f_739_, v_sz_742_, v___x_743_, v___x_741_);
v___x_745_ = lean_apply_7(v___x_211959__overap_744_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object* v_a_791_, lean_object* v_x_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_log_801_; uint8_t v_action_802_; uint8_t v_wantsRebuild_803_; lean_object* v_trace_804_; lean_object* v_buildTime_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_log_801_ = lean_ctor_get(v___y_799_, 0);
v_action_802_ = lean_ctor_get_uint8(v___y_799_, sizeof(void*)*3);
v_wantsRebuild_803_ = lean_ctor_get_uint8(v___y_799_, sizeof(void*)*3 + 1);
v_trace_804_ = lean_ctor_get(v___y_799_, 1);
v_buildTime_805_ = lean_ctor_get(v___y_799_, 2);
v___x_806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_807_ = lean_string_append(v___y_793_, v___x_806_);
v___x_808_ = lean_io_prim_handle_put_str(v_a_791_, v___x_807_);
lean_dec_ref(v___x_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_810_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref(v___x_808_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v_a_809_);
lean_ctor_set(v___x_810_, 1, v___y_799_);
return v___x_810_;
}
else
{
lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_824_; 
lean_inc(v_buildTime_805_);
lean_inc_ref(v_trace_804_);
lean_inc_ref(v_log_801_);
v_isSharedCheck_824_ = !lean_is_exclusive(v___y_799_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; lean_object* v_unused_826_; lean_object* v_unused_827_; 
v_unused_825_ = lean_ctor_get(v___y_799_, 2);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v___y_799_, 1);
lean_dec(v_unused_826_);
v_unused_827_ = lean_ctor_get(v___y_799_, 0);
lean_dec(v_unused_827_);
v___x_812_ = v___y_799_;
v_isShared_813_ = v_isSharedCheck_824_;
goto v_resetjp_811_;
}
else
{
lean_dec(v___y_799_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_824_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v_a_814_; lean_object* v___x_815_; uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v_a_814_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_814_);
lean_dec_ref(v___x_808_);
v___x_815_ = lean_io_error_to_string(v_a_814_);
v___x_816_ = 3;
v___x_817_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set_uint8(v___x_817_, sizeof(void*)*1, v___x_816_);
v___x_818_ = lean_array_get_size(v_log_801_);
v___x_819_ = lean_array_push(v_log_801_, v___x_817_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_819_);
v___x_821_ = v___x_812_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_trace_804_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_buildTime_805_);
lean_ctor_set_uint8(v_reuseFailAlloc_823_, sizeof(void*)*3, v_action_802_);
lean_ctor_set_uint8(v_reuseFailAlloc_823_, sizeof(void*)*3 + 1, v_wantsRebuild_803_);
v___x_821_ = v_reuseFailAlloc_823_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_818_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object* v_a_828_, lean_object* v_x_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v_a_828_, v_x_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v_a_828_);
return v_res_838_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_846_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3));
v___x_847_ = lean_unsigned_to_nat(5u);
v___x_848_ = lean_mk_empty_array_with_capacity(v___x_847_);
v___x_849_ = lean_array_push(v___x_848_, v___x_846_);
return v___x_849_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_850_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4));
v___x_851_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6);
v___x_852_ = lean_array_push(v___x_851_, v___x_850_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(uint8_t v_bootstrap_855_, lean_object* v___y_856_, lean_object* v_oFiles_857_, uint8_t v_shouldExport_858_, uint8_t v___x_859_, lean_object* v___x_860_, size_t v___x_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
if (v_bootstrap_855_ == 0)
{
lean_object* v_toContext_869_; lean_object* v_lakeEnv_870_; lean_object* v_lean_871_; lean_object* v_log_872_; uint8_t v_action_873_; uint8_t v_wantsRebuild_874_; lean_object* v_trace_875_; lean_object* v_buildTime_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_906_; 
lean_dec(v___y_865_);
lean_dec(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v___x_860_);
v_toContext_869_ = lean_ctor_get(v___y_866_, 1);
lean_inc(v_toContext_869_);
lean_dec_ref(v___y_866_);
v_lakeEnv_870_ = lean_ctor_get(v_toContext_869_, 1);
lean_inc_ref(v_lakeEnv_870_);
lean_dec(v_toContext_869_);
v_lean_871_ = lean_ctor_get(v_lakeEnv_870_, 1);
lean_inc_ref(v_lean_871_);
lean_dec_ref(v_lakeEnv_870_);
v_log_872_ = lean_ctor_get(v___y_867_, 0);
v_action_873_ = lean_ctor_get_uint8(v___y_867_, sizeof(void*)*3);
v_wantsRebuild_874_ = lean_ctor_get_uint8(v___y_867_, sizeof(void*)*3 + 1);
v_trace_875_ = lean_ctor_get(v___y_867_, 1);
v_buildTime_876_ = lean_ctor_get(v___y_867_, 2);
v_isSharedCheck_906_ = !lean_is_exclusive(v___y_867_);
if (v_isSharedCheck_906_ == 0)
{
v___x_878_ = v___y_867_;
v_isShared_879_ = v_isSharedCheck_906_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_buildTime_876_);
lean_inc(v_trace_875_);
lean_inc(v_log_872_);
lean_dec(v___y_867_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_906_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_ar_880_; lean_object* v___x_881_; 
v_ar_880_ = lean_ctor_get(v_lean_871_, 12);
lean_inc_ref(v_ar_880_);
lean_dec_ref(v_lean_871_);
v___x_881_ = l_Lake_compileStaticLib(v___y_856_, v_oFiles_857_, v_ar_880_, v_bootstrap_855_, v_log_872_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_893_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_a_883_ = lean_ctor_get(v___x_881_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_893_ == 0)
{
v___x_885_ = v___x_881_;
v_isShared_886_ = v_isSharedCheck_893_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_893_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v_a_883_);
v___x_888_ = v___x_878_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_883_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_trace_875_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_buildTime_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_892_, sizeof(void*)*3, v_action_873_);
lean_ctor_set_uint8(v_reuseFailAlloc_892_, sizeof(void*)*3 + 1, v_wantsRebuild_874_);
v___x_888_ = v_reuseFailAlloc_892_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v___x_888_);
v___x_890_ = v___x_885_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_882_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_905_; 
v_a_894_ = lean_ctor_get(v___x_881_, 0);
v_a_895_ = lean_ctor_get(v___x_881_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_905_ == 0)
{
v___x_897_ = v___x_881_;
v_isShared_898_ = v_isSharedCheck_905_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_inc(v_a_894_);
lean_dec(v___x_881_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_905_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v_a_895_);
v___x_900_ = v___x_878_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_895_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_trace_875_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_buildTime_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_904_, sizeof(void*)*3, v_action_873_);
lean_ctor_set_uint8(v_reuseFailAlloc_904_, sizeof(void*)*3 + 1, v_wantsRebuild_874_);
v___x_900_ = v_reuseFailAlloc_904_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___x_900_);
v___x_902_ = v___x_897_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_894_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
else
{
uint8_t v___x_907_; 
v___x_907_ = l_System_Platform_isOSX;
if (v___x_907_ == 0)
{
uint8_t v___x_908_; 
lean_dec(v___y_865_);
lean_dec(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v___x_860_);
v___x_908_ = l_System_Platform_isWindows;
if (v___x_908_ == 0)
{
lean_object* v_toContext_909_; lean_object* v_lakeEnv_910_; lean_object* v_lean_911_; lean_object* v_log_912_; uint8_t v_action_913_; uint8_t v_wantsRebuild_914_; lean_object* v_trace_915_; lean_object* v_buildTime_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_946_; 
v_toContext_909_ = lean_ctor_get(v___y_866_, 1);
lean_inc(v_toContext_909_);
lean_dec_ref(v___y_866_);
v_lakeEnv_910_ = lean_ctor_get(v_toContext_909_, 1);
lean_inc_ref(v_lakeEnv_910_);
lean_dec(v_toContext_909_);
v_lean_911_ = lean_ctor_get(v_lakeEnv_910_, 1);
lean_inc_ref(v_lean_911_);
lean_dec_ref(v_lakeEnv_910_);
v_log_912_ = lean_ctor_get(v___y_867_, 0);
v_action_913_ = lean_ctor_get_uint8(v___y_867_, sizeof(void*)*3);
v_wantsRebuild_914_ = lean_ctor_get_uint8(v___y_867_, sizeof(void*)*3 + 1);
v_trace_915_ = lean_ctor_get(v___y_867_, 1);
v_buildTime_916_ = lean_ctor_get(v___y_867_, 2);
v_isSharedCheck_946_ = !lean_is_exclusive(v___y_867_);
if (v_isSharedCheck_946_ == 0)
{
v___x_918_ = v___y_867_;
v_isShared_919_ = v_isSharedCheck_946_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_buildTime_916_);
lean_inc(v_trace_915_);
lean_inc(v_log_912_);
lean_dec(v___y_867_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_946_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_ar_920_; lean_object* v___x_921_; 
v_ar_920_ = lean_ctor_get(v_lean_911_, 12);
lean_inc_ref(v_ar_920_);
lean_dec_ref(v_lean_911_);
v___x_921_ = l_Lake_compileStaticLib(v___y_856_, v_oFiles_857_, v_ar_920_, v___x_908_, v_log_912_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_933_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_a_923_ = lean_ctor_get(v___x_921_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_933_ == 0)
{
v___x_925_ = v___x_921_;
v_isShared_926_ = v_isSharedCheck_933_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_933_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v_a_923_);
v___x_928_ = v___x_918_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_923_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_trace_915_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_buildTime_916_);
lean_ctor_set_uint8(v_reuseFailAlloc_932_, sizeof(void*)*3, v_action_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_932_, sizeof(void*)*3 + 1, v_wantsRebuild_914_);
v___x_928_ = v_reuseFailAlloc_932_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_930_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 1, v___x_928_);
v___x_930_ = v___x_925_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_922_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_945_; 
v_a_934_ = lean_ctor_get(v___x_921_, 0);
v_a_935_ = lean_ctor_get(v___x_921_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_945_ == 0)
{
v___x_937_ = v___x_921_;
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_inc(v_a_934_);
lean_dec(v___x_921_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v_a_935_);
v___x_940_ = v___x_918_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_935_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_trace_915_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_buildTime_916_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3, v_action_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3 + 1, v_wantsRebuild_914_);
v___x_940_ = v_reuseFailAlloc_944_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 1, v___x_940_);
v___x_942_ = v___x_937_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_934_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_947_; lean_object* v_lakeEnv_948_; lean_object* v_lean_949_; lean_object* v_log_950_; uint8_t v_action_951_; uint8_t v_wantsRebuild_952_; lean_object* v_trace_953_; lean_object* v_buildTime_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_984_; 
v_toContext_947_ = lean_ctor_get(v___y_866_, 1);
lean_inc(v_toContext_947_);
lean_dec_ref(v___y_866_);
v_lakeEnv_948_ = lean_ctor_get(v_toContext_947_, 1);
lean_inc_ref(v_lakeEnv_948_);
lean_dec(v_toContext_947_);
v_lean_949_ = lean_ctor_get(v_lakeEnv_948_, 1);
lean_inc_ref(v_lean_949_);
lean_dec_ref(v_lakeEnv_948_);
v_log_950_ = lean_ctor_get(v___y_867_, 0);
v_action_951_ = lean_ctor_get_uint8(v___y_867_, sizeof(void*)*3);
v_wantsRebuild_952_ = lean_ctor_get_uint8(v___y_867_, sizeof(void*)*3 + 1);
v_trace_953_ = lean_ctor_get(v___y_867_, 1);
v_buildTime_954_ = lean_ctor_get(v___y_867_, 2);
v_isSharedCheck_984_ = !lean_is_exclusive(v___y_867_);
if (v_isSharedCheck_984_ == 0)
{
v___x_956_ = v___y_867_;
v_isShared_957_ = v_isSharedCheck_984_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_buildTime_954_);
lean_inc(v_trace_953_);
lean_inc(v_log_950_);
lean_dec(v___y_867_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_984_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_ar_958_; lean_object* v___x_959_; 
v_ar_958_ = lean_ctor_get(v_lean_949_, 12);
lean_inc_ref(v_ar_958_);
lean_dec_ref(v_lean_949_);
v___x_959_ = l_Lake_compileStaticLib(v___y_856_, v_oFiles_857_, v_ar_958_, v_shouldExport_858_, v_log_950_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_971_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_a_961_ = lean_ctor_get(v___x_959_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_971_ == 0)
{
v___x_963_ = v___x_959_;
v_isShared_964_ = v_isSharedCheck_971_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_971_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v_a_961_);
v___x_966_ = v___x_956_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_961_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_trace_953_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_buildTime_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*3, v_action_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*3 + 1, v_wantsRebuild_952_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v___x_966_);
v___x_968_ = v___x_963_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_960_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v_a_972_; lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_983_; 
v_a_972_ = lean_ctor_get(v___x_959_, 0);
v_a_973_ = lean_ctor_get(v___x_959_, 1);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_983_ == 0)
{
v___x_975_ = v___x_959_;
v_isShared_976_ = v_isSharedCheck_983_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_inc(v_a_972_);
lean_dec(v___x_959_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_983_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v_a_973_);
v___x_978_ = v___x_956_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_973_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_trace_953_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_buildTime_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_982_, sizeof(void*)*3, v_action_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_982_, sizeof(void*)*3 + 1, v_wantsRebuild_952_);
v___x_978_ = v_reuseFailAlloc_982_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 1, v___x_978_);
v___x_980_ = v___x_975_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_972_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_985_; uint8_t v_action_986_; uint8_t v_wantsRebuild_987_; lean_object* v_trace_988_; lean_object* v_buildTime_989_; lean_object* v___x_990_; 
v_log_985_ = lean_ctor_get(v___y_867_, 0);
v_action_986_ = lean_ctor_get_uint8(v___y_867_, sizeof(void*)*3);
v_wantsRebuild_987_ = lean_ctor_get_uint8(v___y_867_, sizeof(void*)*3 + 1);
v_trace_988_ = lean_ctor_get(v___y_867_, 1);
v_buildTime_989_ = lean_ctor_get(v___y_867_, 2);
lean_inc_ref(v___y_856_);
v___x_990_ = l_Lake_createParentDirs(v___y_856_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v_a_994_; lean_object* v___y_1041_; uint8_t v___x_1043_; lean_object* v___x_1044_; 
lean_dec_ref(v___x_990_);
v___x_991_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_856_);
v___x_992_ = l_System_FilePath_addExtension(v___y_856_, v___x_991_);
v___x_1043_ = 1;
v___x_1044_ = lean_io_prim_handle_mk(v___x_992_, v___x_1043_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = l_Lake_EquipT_instMonad___redArg(v___x_860_);
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = lean_array_get_size(v_oFiles_857_);
v___x_1049_ = lean_nat_dec_lt(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_dec_ref(v___x_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v_oFiles_857_);
v_a_994_ = v___y_867_;
goto v___jp_993_;
}
else
{
lean_object* v___f_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___f_1050_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1050_, 0, v_a_1045_);
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_nat_dec_le(v___x_1048_, v___x_1048_);
if (v___x_1052_ == 0)
{
if (v___x_1049_ == 0)
{
lean_dec_ref(v___f_1050_);
lean_dec_ref(v___x_1046_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v_oFiles_857_);
v_a_994_ = v___y_867_;
goto v___jp_993_;
}
else
{
size_t v___x_1053_; lean_object* v___x_212117__overap_1054_; lean_object* v___x_1055_; 
v___x_1053_ = lean_usize_of_nat(v___x_1048_);
v___x_212117__overap_1054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1046_, v___f_1050_, v_oFiles_857_, v___x_861_, v___x_1053_, v___x_1051_);
v___x_1055_ = lean_apply_7(v___x_212117__overap_1054_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
v___y_1041_ = v___x_1055_;
goto v___jp_1040_;
}
}
else
{
size_t v___x_1056_; lean_object* v___x_212119__overap_1057_; lean_object* v___x_1058_; 
v___x_1056_ = lean_usize_of_nat(v___x_1048_);
v___x_212119__overap_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1046_, v___f_1050_, v_oFiles_857_, v___x_861_, v___x_1056_, v___x_1051_);
v___x_1058_ = lean_apply_7(v___x_212119__overap_1057_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
v___y_1041_ = v___x_1058_;
goto v___jp_1040_;
}
}
}
else
{
lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1072_; 
lean_inc(v_buildTime_989_);
lean_inc_ref(v_trace_988_);
lean_inc_ref(v_log_985_);
lean_dec_ref(v___x_992_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v___x_860_);
lean_dec_ref(v_oFiles_857_);
lean_dec_ref(v___y_856_);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___y_867_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; lean_object* v_unused_1074_; lean_object* v_unused_1075_; 
v_unused_1073_ = lean_ctor_get(v___y_867_, 2);
lean_dec(v_unused_1073_);
v_unused_1074_ = lean_ctor_get(v___y_867_, 1);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v___y_867_, 0);
lean_dec(v_unused_1075_);
v___x_1060_ = v___y_867_;
v_isShared_1061_ = v_isSharedCheck_1072_;
goto v_resetjp_1059_;
}
else
{
lean_dec(v___y_867_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1072_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v_a_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v_a_1062_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1062_);
lean_dec_ref(v___x_1044_);
v___x_1063_ = lean_io_error_to_string(v_a_1062_);
v___x_1064_ = 3;
v___x_1065_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*1, v___x_1064_);
v___x_1066_ = lean_array_get_size(v_log_985_);
v___x_1067_ = lean_array_push(v_log_985_, v___x_1065_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1067_);
v___x_1069_ = v___x_1060_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_trace_988_);
lean_ctor_set(v_reuseFailAlloc_1071_, 2, v_buildTime_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_1071_, sizeof(void*)*3, v_action_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_1071_, sizeof(void*)*3 + 1, v_wantsRebuild_987_);
v___x_1069_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1066_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
return v___x_1070_;
}
}
}
v___jp_993_:
{
lean_object* v___x_995_; lean_object* v_log_996_; uint8_t v_action_997_; uint8_t v_wantsRebuild_998_; lean_object* v_trace_999_; lean_object* v_buildTime_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1039_; 
v___x_995_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_996_ = lean_ctor_get(v_a_994_, 0);
v_action_997_ = lean_ctor_get_uint8(v_a_994_, sizeof(void*)*3);
v_wantsRebuild_998_ = lean_ctor_get_uint8(v_a_994_, sizeof(void*)*3 + 1);
v_trace_999_ = lean_ctor_get(v_a_994_, 1);
v_buildTime_1000_ = lean_ctor_get(v_a_994_, 2);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_a_994_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1002_ = v_a_994_;
v_isShared_1003_ = v_isSharedCheck_1039_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_buildTime_1000_);
lean_inc(v_trace_999_);
lean_inc(v_log_996_);
lean_dec(v_a_994_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1039_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1004_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1005_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1006_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1007_ = lean_array_push(v___x_1006_, v___y_856_);
v___x_1008_ = lean_array_push(v___x_1007_, v___x_1005_);
v___x_1009_ = lean_array_push(v___x_1008_, v___x_992_);
v___x_1010_ = lean_box(0);
v___x_1011_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1012_ = 0;
v___x_1013_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1013_, 0, v___x_995_);
lean_ctor_set(v___x_1013_, 1, v___x_1004_);
lean_ctor_set(v___x_1013_, 2, v___x_1009_);
lean_ctor_set(v___x_1013_, 3, v___x_1010_);
lean_ctor_set(v___x_1013_, 4, v___x_1011_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*5, v___x_859_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*5 + 1, v___x_1012_);
v___x_1014_ = l_Lake_proc(v___x_1013_, v___x_1012_, v_log_996_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1026_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_a_1016_ = lean_ctor_get(v___x_1014_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1018_ = v___x_1014_;
v_isShared_1019_ = v_isSharedCheck_1026_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1026_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v_a_1016_);
v___x_1021_ = v___x_1002_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1016_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_trace_999_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_buildTime_1000_);
lean_ctor_set_uint8(v_reuseFailAlloc_1025_, sizeof(void*)*3, v_action_997_);
lean_ctor_set_uint8(v_reuseFailAlloc_1025_, sizeof(void*)*3 + 1, v_wantsRebuild_998_);
v___x_1021_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v___x_1021_);
v___x_1023_ = v___x_1018_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1015_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1038_; 
v_a_1027_ = lean_ctor_get(v___x_1014_, 0);
v_a_1028_ = lean_ctor_get(v___x_1014_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1030_ = v___x_1014_;
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_inc(v_a_1027_);
lean_dec(v___x_1014_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v_a_1028_);
v___x_1033_ = v___x_1002_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1028_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_trace_999_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_buildTime_1000_);
lean_ctor_set_uint8(v_reuseFailAlloc_1037_, sizeof(void*)*3, v_action_997_);
lean_ctor_set_uint8(v_reuseFailAlloc_1037_, sizeof(void*)*3 + 1, v_wantsRebuild_998_);
v___x_1033_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1035_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v___x_1033_);
v___x_1035_ = v___x_1030_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1027_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
}
v___jp_1040_:
{
if (lean_obj_tag(v___y_1041_) == 0)
{
lean_object* v_a_1042_; 
v_a_1042_ = lean_ctor_get(v___y_1041_, 1);
lean_inc(v_a_1042_);
lean_dec_ref(v___y_1041_);
v_a_994_ = v_a_1042_;
goto v___jp_993_;
}
else
{
lean_dec_ref(v___x_992_);
lean_dec_ref(v___y_856_);
return v___y_1041_;
}
}
}
else
{
lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1089_; 
lean_inc(v_buildTime_989_);
lean_inc_ref(v_trace_988_);
lean_inc_ref(v_log_985_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v___x_860_);
lean_dec_ref(v_oFiles_857_);
lean_dec_ref(v___y_856_);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___y_867_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; lean_object* v_unused_1091_; lean_object* v_unused_1092_; 
v_unused_1090_ = lean_ctor_get(v___y_867_, 2);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v___y_867_, 1);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v___y_867_, 0);
lean_dec(v_unused_1092_);
v___x_1077_ = v___y_867_;
v_isShared_1078_ = v_isSharedCheck_1089_;
goto v_resetjp_1076_;
}
else
{
lean_dec(v___y_867_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1089_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_a_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v_a_1079_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_1079_);
lean_dec_ref(v___x_990_);
v___x_1080_ = lean_io_error_to_string(v_a_1079_);
v___x_1081_ = 3;
v___x_1082_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*1, v___x_1081_);
v___x_1083_ = lean_array_get_size(v_log_985_);
v___x_1084_ = lean_array_push(v_log_985_, v___x_1082_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1084_);
v___x_1086_ = v___x_1077_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_trace_988_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_buildTime_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*3, v_action_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*3 + 1, v_wantsRebuild_987_);
v___x_1086_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1083_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
return v___x_1087_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* v_bootstrap_1093_, lean_object* v___y_1094_, lean_object* v_oFiles_1095_, lean_object* v_shouldExport_1096_, lean_object* v___x_1097_, lean_object* v___x_1098_, lean_object* v___x_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
uint8_t v_bootstrap_boxed_1107_; uint8_t v_shouldExport_boxed_1108_; uint8_t v___x_212491__boxed_1109_; size_t v___x_212493__boxed_1110_; lean_object* v_res_1111_; 
v_bootstrap_boxed_1107_ = lean_unbox(v_bootstrap_1093_);
v_shouldExport_boxed_1108_ = lean_unbox(v_shouldExport_1096_);
v___x_212491__boxed_1109_ = lean_unbox(v___x_1097_);
v___x_212493__boxed_1110_ = lean_unbox_usize(v___x_1099_);
lean_dec(v___x_1099_);
v_res_1111_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_boxed_1107_, v___y_1094_, v_oFiles_1095_, v_shouldExport_boxed_1108_, v___x_212491__boxed_1109_, v___x_1098_, v___x_212493__boxed_1110_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(uint8_t v_bootstrap_1113_, lean_object* v___y_1114_, uint8_t v_shouldExport_1115_, uint8_t v___x_1116_, lean_object* v___x_1117_, size_t v___x_1118_, lean_object* v_oFiles_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___y_1131_; uint8_t v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1127_ = lean_box(v_bootstrap_1113_);
v___x_1128_ = lean_box(v_shouldExport_1115_);
v___x_1129_ = lean_box(v___x_1116_);
v___x_1130_ = lean_box_usize(v___x_1118_);
lean_inc_ref(v___y_1114_);
v___y_1131_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed), 14, 7);
lean_closure_set(v___y_1131_, 0, v___x_1127_);
lean_closure_set(v___y_1131_, 1, v___y_1114_);
lean_closure_set(v___y_1131_, 2, v_oFiles_1119_);
lean_closure_set(v___y_1131_, 3, v___x_1128_);
lean_closure_set(v___y_1131_, 4, v___x_1129_);
lean_closure_set(v___y_1131_, 5, v___x_1117_);
lean_closure_set(v___y_1131_, 6, v___x_1130_);
v___x_1132_ = 0;
v___x_1133_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1134_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1114_, v___y_1131_, v___x_1132_, v___x_1133_, v___x_1116_, v___x_1132_, v___x_1132_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1144_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_a_1136_ = lean_ctor_get(v___x_1134_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1138_ = v___x_1134_;
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v_path_1140_; lean_object* v___x_1142_; 
v_path_1140_ = lean_ctor_get(v_a_1135_, 1);
lean_inc_ref(v_path_1140_);
lean_dec(v_a_1135_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v_path_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_path_1140_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_a_1136_);
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
lean_object* v_a_1145_; lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_a_1145_ = lean_ctor_get(v___x_1134_, 0);
v_a_1146_ = lean_ctor_get(v___x_1134_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1134_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_inc(v_a_1145_);
lean_dec(v___x_1134_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1145_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object* v_bootstrap_1154_, lean_object* v___y_1155_, lean_object* v_shouldExport_1156_, lean_object* v___x_1157_, lean_object* v___x_1158_, lean_object* v___x_1159_, lean_object* v_oFiles_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
uint8_t v_bootstrap_boxed_1168_; uint8_t v_shouldExport_boxed_1169_; uint8_t v___x_212916__boxed_1170_; size_t v___x_212918__boxed_1171_; lean_object* v_res_1172_; 
v_bootstrap_boxed_1168_ = lean_unbox(v_bootstrap_1154_);
v_shouldExport_boxed_1169_ = lean_unbox(v_shouldExport_1156_);
v___x_212916__boxed_1170_ = lean_unbox(v___x_1157_);
v___x_212918__boxed_1171_ = lean_unbox_usize(v___x_1159_);
lean_dec(v___x_1159_);
v_res_1172_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_boxed_1168_, v___y_1155_, v_shouldExport_boxed_1169_, v___x_212916__boxed_1170_, v___x_1158_, v___x_212918__boxed_1171_, v_oFiles_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object* v___x_1177_, lean_object* v___x_1178_, lean_object* v_config_1179_, lean_object* v_config_1180_, lean_object* v___x_1181_, lean_object* v___f_1182_, uint8_t v_shouldExport_1183_, uint8_t v___x_1184_, lean_object* v___x_1185_, lean_object* v___x_1186_, lean_object* v_dir_1187_, lean_object* v_self_1188_, lean_object* v___f_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___y_1198_; uint8_t v___y_1199_; size_t v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v_a_1218_; lean_object* v_a_1219_; lean_object* v___y_1263_; lean_object* v___x_1275_; 
lean_inc_ref(v___y_1190_);
lean_inc_ref(v___y_1194_);
lean_inc(v___y_1193_);
lean_inc(v___y_1192_);
lean_inc(v___x_1178_);
v___x_1275_ = lean_apply_7(v___y_1190_, v___x_1177_, v___x_1178_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, lean_box(0));
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v_a_1277_; lean_object* v___x_1278_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
v_a_1277_ = lean_ctor_get(v___x_1275_, 1);
lean_inc(v_a_1277_);
lean_dec_ref(v___x_1275_);
v___x_1278_ = l_Lake_Job_await___redArg(v_a_1276_, v_a_1277_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
v_a_1280_ = lean_ctor_get(v___x_1278_, 1);
lean_inc(v_a_1280_);
lean_dec_ref(v___x_1278_);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_1283_ = lean_array_get_size(v_a_1279_);
v___x_1284_ = lean_nat_dec_lt(v___x_1281_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_dec(v_a_1279_);
lean_dec_ref(v___f_1189_);
v_a_1218_ = v___x_1282_;
v_a_1219_ = v_a_1280_;
goto v___jp_1217_;
}
else
{
uint8_t v___x_1285_; 
v___x_1285_ = lean_nat_dec_le(v___x_1283_, v___x_1283_);
if (v___x_1285_ == 0)
{
if (v___x_1284_ == 0)
{
lean_dec(v_a_1279_);
lean_dec_ref(v___f_1189_);
v_a_1218_ = v___x_1282_;
v_a_1219_ = v_a_1280_;
goto v___jp_1217_;
}
else
{
size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_212256__overap_1288_; lean_object* v___x_1289_; 
v___x_1286_ = ((size_t)0ULL);
v___x_1287_ = lean_usize_of_nat(v___x_1283_);
lean_inc_ref(v___x_1181_);
v___x_212256__overap_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1181_, v___f_1189_, v_a_1279_, v___x_1286_, v___x_1287_, v___x_1282_);
lean_inc_ref(v___y_1194_);
lean_inc(v___y_1193_);
lean_inc(v___y_1192_);
lean_inc(v___x_1178_);
lean_inc_ref(v___y_1190_);
v___x_1289_ = lean_apply_7(v___x_212256__overap_1288_, v___y_1190_, v___x_1178_, v___y_1192_, v___y_1193_, v___y_1194_, v_a_1280_, lean_box(0));
v___y_1263_ = v___x_1289_;
goto v___jp_1262_;
}
}
else
{
size_t v___x_1290_; size_t v___x_1291_; lean_object* v___x_212259__overap_1292_; lean_object* v___x_1293_; 
v___x_1290_ = ((size_t)0ULL);
v___x_1291_ = lean_usize_of_nat(v___x_1283_);
lean_inc_ref(v___x_1181_);
v___x_212259__overap_1292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1181_, v___f_1189_, v_a_1279_, v___x_1290_, v___x_1291_, v___x_1282_);
lean_inc_ref(v___y_1194_);
lean_inc(v___y_1193_);
lean_inc(v___y_1192_);
lean_inc(v___x_1178_);
lean_inc_ref(v___y_1190_);
v___x_1293_ = lean_apply_7(v___x_212259__overap_1292_, v___y_1190_, v___x_1178_, v___y_1192_, v___y_1193_, v___y_1194_, v_a_1280_, lean_box(0));
v___y_1263_ = v___x_1293_;
goto v___jp_1262_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1190_);
lean_dec_ref(v___f_1189_);
lean_dec_ref(v_self_1188_);
lean_dec_ref(v_dir_1187_);
lean_dec(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___f_1182_);
lean_dec_ref(v___x_1181_);
lean_dec_ref(v_config_1179_);
lean_dec(v___x_1178_);
v_a_1294_ = lean_ctor_get(v___x_1278_, 0);
v_a_1295_ = lean_ctor_get(v___x_1278_, 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1278_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_inc(v_a_1294_);
lean_dec(v___x_1278_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1294_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1190_);
lean_dec_ref(v___f_1189_);
lean_dec_ref(v_self_1188_);
lean_dec_ref(v_dir_1187_);
lean_dec(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___f_1182_);
lean_dec_ref(v___x_1181_);
lean_dec_ref(v_config_1179_);
lean_dec(v___x_1178_);
v_a_1303_ = lean_ctor_get(v___x_1275_, 0);
v_a_1304_ = lean_ctor_get(v___x_1275_, 1);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1275_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_inc(v_a_1303_);
lean_dec(v___x_1275_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1303_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
v___jp_1197_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1204_ = lean_box(v___y_1199_);
v___x_1205_ = lean_box(v_shouldExport_1183_);
v___x_1206_ = lean_box(v___x_1184_);
v___x_1207_ = lean_box_usize(v___y_1200_);
v___f_1208_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed), 14, 6);
lean_closure_set(v___f_1208_, 0, v___x_1204_);
lean_closure_set(v___f_1208_, 1, v___y_1203_);
lean_closure_set(v___f_1208_, 2, v___x_1205_);
lean_closure_set(v___f_1208_, 3, v___x_1206_);
lean_closure_set(v___f_1208_, 4, v___x_1185_);
lean_closure_set(v___f_1208_, 5, v___x_1207_);
v___x_1209_ = l_Array_append___redArg(v___y_1202_, v___y_1198_);
lean_dec_ref(v___y_1198_);
v___x_1210_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_1211_ = l_Lake_Job_collectArray___redArg(v___x_1209_, v___x_1210_);
lean_dec_ref(v___x_1209_);
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = 0;
v___x_1214_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_1215_ = l_Lake_Job_mapM___redArg(v___x_1186_, v___x_1211_, v___f_1208_, v___x_1212_, v___x_1213_, v___y_1190_, v___x_1178_, v___y_1192_, v___y_1193_, v___y_1194_, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___y_1201_);
return v___x_1216_;
}
v___jp_1217_:
{
lean_object* v_toLeanConfig_1220_; lean_object* v_toLeanConfig_1221_; uint8_t v_bootstrap_1222_; lean_object* v_buildDir_1223_; lean_object* v_nativeLibDir_1224_; lean_object* v_moreLinkObjs_1225_; lean_object* v_moreLinkObjs_1226_; lean_object* v___x_1227_; size_t v_sz_1228_; size_t v___x_1229_; lean_object* v___x_212196__overap_1230_; lean_object* v___x_1231_; 
v_toLeanConfig_1220_ = lean_ctor_get(v_config_1179_, 1);
lean_inc_ref(v_toLeanConfig_1220_);
v_toLeanConfig_1221_ = lean_ctor_get(v_config_1180_, 0);
v_bootstrap_1222_ = lean_ctor_get_uint8(v_config_1179_, sizeof(void*)*26);
v_buildDir_1223_ = lean_ctor_get(v_config_1179_, 5);
lean_inc_ref(v_buildDir_1223_);
v_nativeLibDir_1224_ = lean_ctor_get(v_config_1179_, 7);
lean_inc_ref(v_nativeLibDir_1224_);
lean_dec_ref(v_config_1179_);
v_moreLinkObjs_1225_ = lean_ctor_get(v_toLeanConfig_1220_, 6);
lean_inc_ref(v_moreLinkObjs_1225_);
lean_dec_ref(v_toLeanConfig_1220_);
v_moreLinkObjs_1226_ = lean_ctor_get(v_toLeanConfig_1221_, 6);
v___x_1227_ = l_Array_append___redArg(v_moreLinkObjs_1225_, v_moreLinkObjs_1226_);
v_sz_1228_ = lean_array_size(v___x_1227_);
v___x_1229_ = ((size_t)0ULL);
v___x_212196__overap_1230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1181_, v___f_1182_, v_sz_1228_, v___x_1229_, v___x_1227_);
lean_inc_ref(v___y_1194_);
lean_inc(v___y_1193_);
lean_inc(v___y_1192_);
lean_inc(v___x_1178_);
lean_inc_ref(v___y_1190_);
v___x_1231_ = lean_apply_7(v___x_212196__overap_1230_, v___y_1190_, v___x_1178_, v___y_1192_, v___y_1193_, v___y_1194_, v_a_1219_, lean_box(0));
if (lean_obj_tag(v___x_1231_) == 0)
{
if (v_shouldExport_1183_ == 0)
{
lean_object* v_a_1232_; lean_object* v_a_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
v_a_1233_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_a_1233_);
lean_dec_ref(v___x_1231_);
v___x_1234_ = l_System_FilePath_normalize(v_buildDir_1223_);
v___x_1235_ = l_Lake_joinRelative(v_dir_1187_, v___x_1234_);
v___x_1236_ = l_System_FilePath_normalize(v_nativeLibDir_1224_);
v___x_1237_ = l_Lake_joinRelative(v___x_1235_, v___x_1236_);
v___x_1238_ = l_Lake_LeanLib_libName(v_self_1188_);
v___x_1239_ = l_Lake_nameToStaticLib(v___x_1238_, v_shouldExport_1183_);
v___x_1240_ = l_Lake_joinRelative(v___x_1237_, v___x_1239_);
v___y_1198_ = v_a_1232_;
v___y_1199_ = v_bootstrap_1222_;
v___y_1200_ = v___x_1229_;
v___y_1201_ = v_a_1233_;
v___y_1202_ = v_a_1218_;
v___y_1203_ = v___x_1240_;
goto v___jp_1197_;
}
else
{
lean_object* v_a_1241_; lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_a_1241_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1241_);
v_a_1242_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_a_1242_);
lean_dec_ref(v___x_1231_);
v___x_1243_ = l_System_FilePath_normalize(v_buildDir_1223_);
v___x_1244_ = l_Lake_joinRelative(v_dir_1187_, v___x_1243_);
v___x_1245_ = l_System_FilePath_normalize(v_nativeLibDir_1224_);
v___x_1246_ = l_Lake_joinRelative(v___x_1244_, v___x_1245_);
v___x_1247_ = l_Lake_LeanLib_libName(v_self_1188_);
v___x_1248_ = 0;
v___x_1249_ = l_Lake_nameToStaticLib(v___x_1247_, v___x_1248_);
v___x_1250_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_1251_ = l_System_FilePath_addExtension(v___x_1249_, v___x_1250_);
v___x_1252_ = l_Lake_joinRelative(v___x_1246_, v___x_1251_);
v___y_1198_ = v_a_1241_;
v___y_1199_ = v_bootstrap_1222_;
v___y_1200_ = v___x_1229_;
v___y_1201_ = v_a_1242_;
v___y_1202_ = v_a_1218_;
v___y_1203_ = v___x_1252_;
goto v___jp_1197_;
}
}
else
{
lean_object* v_a_1253_; lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v_nativeLibDir_1224_);
lean_dec_ref(v_buildDir_1223_);
lean_dec_ref(v_a_1218_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1190_);
lean_dec_ref(v_self_1188_);
lean_dec_ref(v_dir_1187_);
lean_dec(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec(v___x_1178_);
v_a_1253_ = lean_ctor_get(v___x_1231_, 0);
v_a_1254_ = lean_ctor_get(v___x_1231_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1231_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_inc(v_a_1253_);
lean_dec(v___x_1231_);
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
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1253_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_a_1254_);
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
v___jp_1262_:
{
if (lean_obj_tag(v___y_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v_a_1265_; 
v_a_1264_ = lean_ctor_get(v___y_1263_, 0);
lean_inc(v_a_1264_);
v_a_1265_ = lean_ctor_get(v___y_1263_, 1);
lean_inc(v_a_1265_);
lean_dec_ref(v___y_1263_);
v_a_1218_ = v_a_1264_;
v_a_1219_ = v_a_1265_;
goto v___jp_1217_;
}
else
{
lean_object* v_a_1266_; lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1190_);
lean_dec_ref(v_self_1188_);
lean_dec_ref(v_dir_1187_);
lean_dec(v___x_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___f_1182_);
lean_dec_ref(v___x_1181_);
lean_dec_ref(v_config_1179_);
lean_dec(v___x_1178_);
v_a_1266_ = lean_ctor_get(v___y_1263_, 0);
v_a_1267_ = lean_ctor_get(v___y_1263_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___y_1263_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___y_1263_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_inc(v_a_1266_);
lean_dec(v___y_1263_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1266_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(lean_object** _args){
lean_object* v___x_1312_ = _args[0];
lean_object* v___x_1313_ = _args[1];
lean_object* v_config_1314_ = _args[2];
lean_object* v_config_1315_ = _args[3];
lean_object* v___x_1316_ = _args[4];
lean_object* v___f_1317_ = _args[5];
lean_object* v_shouldExport_1318_ = _args[6];
lean_object* v___x_1319_ = _args[7];
lean_object* v___x_1320_ = _args[8];
lean_object* v___x_1321_ = _args[9];
lean_object* v_dir_1322_ = _args[10];
lean_object* v_self_1323_ = _args[11];
lean_object* v___f_1324_ = _args[12];
lean_object* v___y_1325_ = _args[13];
lean_object* v___y_1326_ = _args[14];
lean_object* v___y_1327_ = _args[15];
lean_object* v___y_1328_ = _args[16];
lean_object* v___y_1329_ = _args[17];
lean_object* v___y_1330_ = _args[18];
lean_object* v___y_1331_ = _args[19];
_start:
{
uint8_t v_shouldExport_boxed_1332_; uint8_t v___x_213020__boxed_1333_; lean_object* v_res_1334_; 
v_shouldExport_boxed_1332_ = lean_unbox(v_shouldExport_1318_);
v___x_213020__boxed_1333_ = lean_unbox(v___x_1319_);
v_res_1334_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v___x_1312_, v___x_1313_, v_config_1314_, v_config_1315_, v___x_1316_, v___f_1317_, v_shouldExport_boxed_1332_, v___x_213020__boxed_1333_, v___x_1320_, v___x_1321_, v_dir_1322_, v_self_1323_, v___f_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1326_);
lean_dec(v_config_1315_);
return v_res_1334_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0(void){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_instMonadST(lean_box(0));
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_1339_, uint8_t v_shouldExport_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v___x_1348_; lean_object* v_toApplicative_1349_; lean_object* v_toBind_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1439_; 
v___x_1348_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0);
v_toApplicative_1349_ = lean_ctor_get(v___x_1348_, 0);
v_toBind_1350_ = lean_ctor_get(v___x_1348_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1352_ = v___x_1348_;
v_isShared_1353_ = v_isSharedCheck_1439_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_toBind_1350_);
lean_inc(v_toApplicative_1349_);
lean_dec(v___x_1348_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1439_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v_toFunctor_1354_; lean_object* v_toPure_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1435_; 
v_toFunctor_1354_ = lean_ctor_get(v_toApplicative_1349_, 0);
v_toPure_1355_ = lean_ctor_get(v_toApplicative_1349_, 1);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_toApplicative_1349_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; 
v_unused_1436_ = lean_ctor_get(v_toApplicative_1349_, 4);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_toApplicative_1349_, 3);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_toApplicative_1349_, 2);
lean_dec(v_unused_1438_);
v___x_1357_ = v_toApplicative_1349_;
v_isShared_1358_ = v_isSharedCheck_1435_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_toPure_1355_);
lean_inc(v_toFunctor_1354_);
lean_dec(v_toApplicative_1349_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1435_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___f_1359_; lean_object* v___f_1360_; lean_object* v___f_1361_; lean_object* v___f_1362_; lean_object* v___x_1363_; lean_object* v___f_1364_; lean_object* v___x_1366_; 
lean_inc(v_toBind_1350_);
lean_inc(v_toPure_1355_);
v___f_1359_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1359_, 0, v_toPure_1355_);
lean_closure_set(v___f_1359_, 1, v_toBind_1350_);
lean_inc(v_toBind_1350_);
lean_inc(v_toPure_1355_);
v___f_1360_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1360_, 0, v_toPure_1355_);
lean_closure_set(v___f_1360_, 1, v_toBind_1350_);
lean_inc_ref(v___f_1359_);
lean_inc(v_toPure_1355_);
v___f_1361_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1361_, 0, v_toPure_1355_);
lean_closure_set(v___f_1361_, 1, v___f_1359_);
lean_inc(v_toPure_1355_);
lean_inc_ref(v_toFunctor_1354_);
v___f_1362_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1362_, 0, v_toFunctor_1354_);
lean_closure_set(v___f_1362_, 1, v_toPure_1355_);
lean_closure_set(v___f_1362_, 2, v_toBind_1350_);
v___x_1363_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1354_);
v___f_1364_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1364_, 0, v_toPure_1355_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v___f_1360_);
lean_ctor_set(v___x_1357_, 3, v___f_1361_);
lean_ctor_set(v___x_1357_, 2, v___f_1362_);
lean_ctor_set(v___x_1357_, 1, v___f_1364_);
lean_ctor_set(v___x_1357_, 0, v___x_1363_);
v___x_1366_ = v___x_1357_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v___f_1364_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v___f_1362_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v___f_1361_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v___f_1360_);
v___x_1366_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1368_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 1, v___f_1359_);
lean_ctor_set(v___x_1352_, 0, v___x_1366_);
v___x_1368_ = v___x_1352_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v___f_1359_);
v___x_1368_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_toBuildConfig_1374_; lean_object* v_registeredJobs_1375_; uint8_t v_verbosity_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___f_1379_; uint8_t v___x_1380_; uint8_t v___x_1381_; uint8_t v___x_1382_; lean_object* v___y_1384_; 
v___x_1369_ = l_ReaderT_instMonad___redArg(v___x_1368_);
v___x_1370_ = l_ReaderT_instMonad___redArg(v___x_1369_);
v___x_1371_ = l_ReaderT_instMonad___redArg(v___x_1370_);
v___x_1372_ = l_ReaderT_instMonad___redArg(v___x_1371_);
lean_inc_ref(v___x_1372_);
v___x_1373_ = l_Lake_EquipT_instMonad___redArg(v___x_1372_);
v_toBuildConfig_1374_ = lean_ctor_get(v_a_1345_, 0);
v_registeredJobs_1375_ = lean_ctor_get(v_a_1345_, 3);
lean_inc(v_registeredJobs_1375_);
v_verbosity_1376_ = lean_ctor_get_uint8(v_toBuildConfig_1374_, sizeof(void*)*2 + 3);
v___x_1377_ = l_Lake_instDataKindFilePath;
v___x_1378_ = lean_box(v_shouldExport_1340_);
lean_inc_ref(v___x_1373_);
v___f_1379_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1379_, 0, v___x_1378_);
lean_closure_set(v___f_1379_, 1, v___x_1373_);
v___x_1380_ = 2;
v___x_1381_ = l_Lake_instDecidableEqVerbosity(v_verbosity_1376_, v___x_1380_);
v___x_1382_ = 1;
if (v___x_1381_ == 0)
{
lean_object* v___x_1430_; 
v___x_1430_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1384_ = v___x_1430_;
goto v___jp_1383_;
}
else
{
if (v_shouldExport_1340_ == 0)
{
lean_object* v___x_1431_; 
v___x_1431_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1384_ = v___x_1431_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1432_; 
v___x_1432_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_1384_ = v___x_1432_;
goto v___jp_1383_;
}
}
v___jp_1383_:
{
lean_object* v_pkg_1385_; lean_object* v_name_1386_; lean_object* v_config_1387_; lean_object* v_keyName_1388_; lean_object* v_dir_1389_; lean_object* v_config_1390_; lean_object* v___f_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___f_1399_; lean_object* v___x_1400_; 
v_pkg_1385_ = lean_ctor_get(v_self_1339_, 0);
v_name_1386_ = lean_ctor_get(v_self_1339_, 1);
lean_inc(v_name_1386_);
v_config_1387_ = lean_ctor_get(v_self_1339_, 2);
lean_inc(v_config_1387_);
v_keyName_1388_ = lean_ctor_get(v_pkg_1385_, 2);
v_dir_1389_ = lean_ctor_get(v_pkg_1385_, 4);
lean_inc_ref(v_dir_1389_);
v_config_1390_ = lean_ctor_get(v_pkg_1385_, 6);
lean_inc_ref(v_config_1390_);
lean_inc_ref(v_pkg_1385_);
v___f_1391_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_1391_, 0, v___x_1377_);
lean_closure_set(v___f_1391_, 1, v_pkg_1385_);
v___x_1392_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_1386_);
lean_inc(v_keyName_1388_);
v___x_1393_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1393_, 0, v_keyName_1388_);
lean_ctor_set(v___x_1393_, 1, v_name_1386_);
v___x_1394_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1339_);
v___x_1395_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1393_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
lean_ctor_set(v___x_1395_, 2, v_self_1339_);
lean_ctor_set(v___x_1395_, 3, v___x_1392_);
lean_inc_ref(v_pkg_1385_);
v___x_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_pkg_1385_);
v___x_1397_ = lean_box(v_shouldExport_1340_);
v___x_1398_ = lean_box(v___x_1382_);
v___f_1399_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed), 20, 13);
lean_closure_set(v___f_1399_, 0, v___x_1395_);
lean_closure_set(v___f_1399_, 1, v___x_1396_);
lean_closure_set(v___f_1399_, 2, v_config_1390_);
lean_closure_set(v___f_1399_, 3, v_config_1387_);
lean_closure_set(v___f_1399_, 4, v___x_1373_);
lean_closure_set(v___f_1399_, 5, v___f_1391_);
lean_closure_set(v___f_1399_, 6, v___x_1397_);
lean_closure_set(v___f_1399_, 7, v___x_1398_);
lean_closure_set(v___f_1399_, 8, v___x_1372_);
lean_closure_set(v___f_1399_, 9, v___x_1377_);
lean_closure_set(v___f_1399_, 10, v_dir_1389_);
lean_closure_set(v___f_1399_, 11, v_self_1339_);
lean_closure_set(v___f_1399_, 12, v___f_1379_);
v___x_1400_ = l_Lake_ensureJob___redArg(v___x_1377_, v___f_1399_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1429_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_a_1402_ = lean_ctor_get(v___x_1400_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1404_ = v___x_1400_;
v_isShared_1405_ = v_isSharedCheck_1429_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1429_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v_task_1406_; lean_object* v_kind_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1427_; 
v_task_1406_ = lean_ctor_get(v_a_1401_, 0);
v_kind_1407_ = lean_ctor_get(v_a_1401_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_a_1401_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v_a_1401_, 2);
lean_dec(v_unused_1428_);
v___x_1409_ = v_a_1401_;
v_isShared_1410_ = v_isSharedCheck_1427_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_kind_1407_);
lean_inc(v_task_1406_);
lean_dec(v_a_1401_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1427_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; lean_object* v_job_1418_; 
v___x_1411_ = lean_st_ref_take(v_registeredJobs_1375_);
v___x_1412_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1386_, v___x_1382_);
v___x_1413_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_1414_ = lean_string_append(v___x_1412_, v___x_1413_);
v___x_1415_ = lean_string_append(v___x_1414_, v___y_1384_);
lean_dec_ref(v___y_1384_);
v___x_1416_ = 0;
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 2, v___x_1415_);
v_job_1418_ = v___x_1409_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_task_1406_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_kind_1407_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v___x_1415_);
v_job_1418_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_ctor_set_uint8(v_job_1418_, sizeof(void*)*3, v___x_1416_);
lean_inc_ref(v_job_1418_);
v___x_1419_ = l_Lake_Job_toOpaque___redArg(v_job_1418_);
v___x_1420_ = lean_array_push(v___x_1411_, v___x_1419_);
v___x_1421_ = lean_st_ref_set(v_registeredJobs_1375_, v___x_1420_);
lean_dec(v_registeredJobs_1375_);
v___x_1422_ = l_Lake_Job_renew___redArg(v_job_1418_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1422_);
v___x_1424_ = v___x_1404_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_a_1402_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
else
{
lean_dec(v_name_1386_);
lean_dec_ref(v___y_1384_);
lean_dec(v_registeredJobs_1375_);
return v___x_1400_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1440_, lean_object* v_shouldExport_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
uint8_t v_shouldExport_boxed_1449_; lean_object* v_res_1450_; 
v_shouldExport_boxed_1449_ = lean_unbox(v_shouldExport_1441_);
v_res_1450_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1440_, v_shouldExport_boxed_1449_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1451_, lean_object* v_a_1452_){
_start:
{
if (v_fmt_1451_ == 0)
{
return v_a_1452_;
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = l_Lake_mkRelPathString(v_a_1452_);
v___x_1454_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
v___x_1455_ = l_Lean_Json_compress(v___x_1454_);
return v___x_1455_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1456_, lean_object* v_a_1457_){
_start:
{
uint8_t v_fmt_boxed_1458_; lean_object* v_res_1459_; 
v_fmt_boxed_1458_ = lean_unbox(v_fmt_1456_);
v_res_1459_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1458_, v_a_1457_);
return v_res_1459_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1462_; lean_object* v_name_1463_; lean_object* v___x_1464_; 
v___x_1462_ = 1;
v_name_1463_ = l_Lake_instDataKindFilePath;
v___x_1464_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1463_, v___x_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1468_, lean_object* v_self_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
uint8_t v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = 1;
lean_inc_ref_n(v_self_1469_, 2);
v___x_1478_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1468_, v_self_1469_, v_self_1469_, v___x_1477_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v_snd_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1521_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
v_snd_1480_ = lean_ctor_get(v_a_1479_, 1);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_a_1479_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; 
v_unused_1522_ = lean_ctor_get(v_a_1479_, 0);
lean_dec(v_unused_1522_);
v___x_1482_ = v_a_1479_;
v_isShared_1483_ = v_isSharedCheck_1521_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_snd_1480_);
lean_dec(v_a_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1521_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1519_; 
v_a_1484_ = lean_ctor_get(v___x_1478_, 1);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v___x_1478_, 0);
lean_dec(v_unused_1520_);
v___x_1486_ = v___x_1478_;
v_isShared_1487_ = v_isSharedCheck_1519_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1478_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1519_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_kind_1488_; lean_object* v_name_1489_; lean_object* v___y_1491_; uint8_t v___x_1509_; 
v_kind_1488_ = lean_ctor_get(v_snd_1480_, 1);
v_name_1489_ = l_Lake_instDataKindFilePath;
v___x_1509_ = lean_name_eq(v_kind_1488_, v_name_1489_);
if (v___x_1509_ == 0)
{
uint8_t v___x_1510_; 
lean_inc(v_kind_1488_);
lean_del_object(v___x_1482_);
lean_dec(v_snd_1480_);
v___x_1510_ = l_Lean_Name_isAnonymous(v_kind_1488_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1511_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1512_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1488_, v___x_1477_);
v___x_1513_ = lean_string_append(v___x_1511_, v___x_1512_);
lean_dec_ref(v___x_1512_);
v___x_1514_ = lean_string_append(v___x_1513_, v___x_1511_);
v___y_1491_ = v___x_1514_;
goto v___jp_1490_;
}
else
{
lean_object* v___x_1515_; 
lean_dec(v_kind_1488_);
v___x_1515_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1491_ = v___x_1515_;
goto v___jp_1490_;
}
}
else
{
lean_object* v___x_1517_; 
lean_del_object(v___x_1486_);
lean_dec_ref(v_self_1469_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v_a_1484_);
lean_ctor_set(v___x_1482_, 0, v_snd_1480_);
v___x_1517_ = v___x_1482_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_snd_1480_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_a_1484_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
v___jp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1492_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1493_ = l_Lake_PartialBuildKey_toString(v_self_1469_);
v___x_1494_ = lean_string_append(v___x_1492_, v___x_1493_);
lean_dec_ref(v___x_1493_);
v___x_1495_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1496_ = lean_string_append(v___x_1494_, v___x_1495_);
v___x_1497_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1498_ = lean_string_append(v___x_1496_, v___x_1497_);
v___x_1499_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1500_ = lean_string_append(v___x_1498_, v___x_1499_);
v___x_1501_ = lean_string_append(v___x_1500_, v___y_1491_);
lean_dec_ref(v___y_1491_);
v___x_1502_ = 3;
v___x_1503_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*1, v___x_1502_);
v___x_1504_ = lean_array_get_size(v_a_1484_);
v___x_1505_ = lean_array_push(v_a_1484_, v___x_1503_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set_tag(v___x_1486_, 1);
lean_ctor_set(v___x_1486_, 1, v___x_1505_);
lean_ctor_set(v___x_1486_, 0, v___x_1504_);
v___x_1507_ = v___x_1486_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec_ref(v_self_1469_);
v_a_1523_ = lean_ctor_get(v___x_1478_, 0);
v_a_1524_ = lean_ctor_get(v___x_1478_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1478_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_inc(v_a_1523_);
lean_dec(v___x_1478_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1523_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1532_, lean_object* v_self_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1532_, v_self_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1542_, size_t v_sz_1543_, size_t v_i_1544_, lean_object* v_bs_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
uint8_t v___x_1553_; 
v___x_1553_ = lean_usize_dec_lt(v_i_1544_, v_sz_1543_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec_ref(v___x_1542_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_bs_1545_);
lean_ctor_set(v___x_1554_, 1, v___y_1551_);
return v___x_1554_;
}
else
{
lean_object* v_v_1555_; lean_object* v___x_1556_; 
v_v_1555_ = lean_array_uget_borrowed(v_bs_1545_, v_i_1544_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc_ref(v___y_1546_);
lean_inc(v_v_1555_);
lean_inc_ref(v___x_1542_);
v___x_1556_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1542_, v_v_1555_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v_a_1558_; lean_object* v___x_1559_; lean_object* v_bs_x27_1560_; size_t v___x_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
v_a_1558_ = lean_ctor_get(v___x_1556_, 1);
lean_inc(v_a_1558_);
lean_dec_ref(v___x_1556_);
v___x_1559_ = lean_unsigned_to_nat(0u);
v_bs_x27_1560_ = lean_array_uset(v_bs_1545_, v_i_1544_, v___x_1559_);
v___x_1561_ = ((size_t)1ULL);
v___x_1562_ = lean_usize_add(v_i_1544_, v___x_1561_);
v___x_1563_ = lean_array_uset(v_bs_x27_1560_, v_i_1544_, v_a_1557_);
v_i_1544_ = v___x_1562_;
v_bs_1545_ = v___x_1563_;
v___y_1551_ = v_a_1558_;
goto _start;
}
else
{
lean_object* v_a_1565_; lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec_ref(v_bs_1545_);
lean_dec_ref(v___x_1542_);
v_a_1565_ = lean_ctor_get(v___x_1556_, 0);
v_a_1566_ = lean_ctor_get(v___x_1556_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1556_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_inc(v_a_1565_);
lean_dec(v___x_1556_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1565_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1574_, lean_object* v_sz_1575_, lean_object* v_i_1576_, lean_object* v_bs_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
size_t v_sz_boxed_1585_; size_t v_i_boxed_1586_; lean_object* v_res_1587_; 
v_sz_boxed_1585_ = lean_unbox_usize(v_sz_1575_);
lean_dec(v_sz_1575_);
v_i_boxed_1586_ = lean_unbox_usize(v_i_1576_);
lean_dec(v_i_1576_);
v_res_1587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1574_, v_sz_boxed_1585_, v_i_boxed_1586_, v_bs_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object* v_a_1588_, lean_object* v_as_1589_, size_t v_i_1590_, size_t v_stop_1591_, lean_object* v_b_1592_, lean_object* v___y_1593_){
_start:
{
uint8_t v___x_1595_; 
v___x_1595_ = lean_usize_dec_eq(v_i_1590_, v_stop_1591_);
if (v___x_1595_ == 0)
{
lean_object* v_log_1596_; uint8_t v_action_1597_; uint8_t v_wantsRebuild_1598_; lean_object* v_trace_1599_; lean_object* v_buildTime_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_log_1596_ = lean_ctor_get(v___y_1593_, 0);
v_action_1597_ = lean_ctor_get_uint8(v___y_1593_, sizeof(void*)*3);
v_wantsRebuild_1598_ = lean_ctor_get_uint8(v___y_1593_, sizeof(void*)*3 + 1);
v_trace_1599_ = lean_ctor_get(v___y_1593_, 1);
v_buildTime_1600_ = lean_ctor_get(v___y_1593_, 2);
v___x_1601_ = lean_array_uget_borrowed(v_as_1589_, v_i_1590_);
v___x_1602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
lean_inc(v___x_1601_);
v___x_1603_ = lean_string_append(v___x_1601_, v___x_1602_);
v___x_1604_ = lean_io_prim_handle_put_str(v_a_1588_, v___x_1603_);
lean_dec_ref(v___x_1603_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; size_t v___x_1606_; size_t v___x_1607_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v___x_1604_);
v___x_1606_ = ((size_t)1ULL);
v___x_1607_ = lean_usize_add(v_i_1590_, v___x_1606_);
v_i_1590_ = v___x_1607_;
v_b_1592_ = v_a_1605_;
goto _start;
}
else
{
lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1622_; 
lean_inc(v_buildTime_1600_);
lean_inc_ref(v_trace_1599_);
lean_inc_ref(v_log_1596_);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___y_1593_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; lean_object* v_unused_1624_; lean_object* v_unused_1625_; 
v_unused_1623_ = lean_ctor_get(v___y_1593_, 2);
lean_dec(v_unused_1623_);
v_unused_1624_ = lean_ctor_get(v___y_1593_, 1);
lean_dec(v_unused_1624_);
v_unused_1625_ = lean_ctor_get(v___y_1593_, 0);
lean_dec(v_unused_1625_);
v___x_1610_ = v___y_1593_;
v_isShared_1611_ = v_isSharedCheck_1622_;
goto v_resetjp_1609_;
}
else
{
lean_dec(v___y_1593_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1622_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v_a_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v_a_1612_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1612_);
lean_dec_ref(v___x_1604_);
v___x_1613_ = lean_io_error_to_string(v_a_1612_);
v___x_1614_ = 3;
v___x_1615_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set_uint8(v___x_1615_, sizeof(void*)*1, v___x_1614_);
v___x_1616_ = lean_array_get_size(v_log_1596_);
v___x_1617_ = lean_array_push(v_log_1596_, v___x_1615_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1617_);
v___x_1619_ = v___x_1610_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_trace_1599_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v_buildTime_1600_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, sizeof(void*)*3, v_action_1597_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, sizeof(void*)*3 + 1, v_wantsRebuild_1598_);
v___x_1619_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1616_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
return v___x_1620_;
}
}
}
}
else
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v_b_1592_);
lean_ctor_set(v___x_1626_, 1, v___y_1593_);
return v___x_1626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object* v_a_1627_, lean_object* v_as_1628_, lean_object* v_i_1629_, lean_object* v_stop_1630_, lean_object* v_b_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
size_t v_i_boxed_1634_; size_t v_stop_boxed_1635_; lean_object* v_res_1636_; 
v_i_boxed_1634_ = lean_unbox_usize(v_i_1629_);
lean_dec(v_i_1629_);
v_stop_boxed_1635_ = lean_unbox_usize(v_stop_1630_);
lean_dec(v_stop_1630_);
v_res_1636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1627_, v_as_1628_, v_i_boxed_1634_, v_stop_boxed_1635_, v_b_1631_, v___y_1632_);
lean_dec_ref(v_as_1628_);
lean_dec(v_a_1627_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t v_bootstrap_1637_, lean_object* v___y_1638_, lean_object* v_oFiles_1639_, uint8_t v_shouldExport_1640_, uint8_t v___x_1641_, size_t v___x_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
if (v_bootstrap_1637_ == 0)
{
lean_object* v_toContext_1650_; lean_object* v_lakeEnv_1651_; lean_object* v_lean_1652_; lean_object* v_log_1653_; uint8_t v_action_1654_; uint8_t v_wantsRebuild_1655_; lean_object* v_trace_1656_; lean_object* v_buildTime_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1687_; 
v_toContext_1650_ = lean_ctor_get(v___y_1647_, 1);
lean_inc(v_toContext_1650_);
lean_dec_ref(v___y_1647_);
v_lakeEnv_1651_ = lean_ctor_get(v_toContext_1650_, 1);
lean_inc_ref(v_lakeEnv_1651_);
lean_dec(v_toContext_1650_);
v_lean_1652_ = lean_ctor_get(v_lakeEnv_1651_, 1);
lean_inc_ref(v_lean_1652_);
lean_dec_ref(v_lakeEnv_1651_);
v_log_1653_ = lean_ctor_get(v___y_1648_, 0);
v_action_1654_ = lean_ctor_get_uint8(v___y_1648_, sizeof(void*)*3);
v_wantsRebuild_1655_ = lean_ctor_get_uint8(v___y_1648_, sizeof(void*)*3 + 1);
v_trace_1656_ = lean_ctor_get(v___y_1648_, 1);
v_buildTime_1657_ = lean_ctor_get(v___y_1648_, 2);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___y_1648_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1659_ = v___y_1648_;
v_isShared_1660_ = v_isSharedCheck_1687_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_buildTime_1657_);
lean_inc(v_trace_1656_);
lean_inc(v_log_1653_);
lean_dec(v___y_1648_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1687_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v_ar_1661_; lean_object* v___x_1662_; 
v_ar_1661_ = lean_ctor_get(v_lean_1652_, 12);
lean_inc_ref(v_ar_1661_);
lean_dec_ref(v_lean_1652_);
v___x_1662_ = l_Lake_compileStaticLib(v___y_1638_, v_oFiles_1639_, v_ar_1661_, v_bootstrap_1637_, v_log_1653_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1674_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_a_1664_ = lean_ctor_get(v___x_1662_, 1);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1666_ = v___x_1662_;
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v_a_1664_);
v___x_1669_ = v___x_1659_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1664_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_trace_1656_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_buildTime_1657_);
lean_ctor_set_uint8(v_reuseFailAlloc_1673_, sizeof(void*)*3, v_action_1654_);
lean_ctor_set_uint8(v_reuseFailAlloc_1673_, sizeof(void*)*3 + 1, v_wantsRebuild_1655_);
v___x_1669_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v___x_1669_);
v___x_1671_ = v___x_1666_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1663_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1686_; 
v_a_1675_ = lean_ctor_get(v___x_1662_, 0);
v_a_1676_ = lean_ctor_get(v___x_1662_, 1);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1678_ = v___x_1662_;
v_isShared_1679_ = v_isSharedCheck_1686_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_inc(v_a_1675_);
lean_dec(v___x_1662_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1686_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v_a_1676_);
v___x_1681_ = v___x_1659_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1676_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_trace_1656_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_buildTime_1657_);
lean_ctor_set_uint8(v_reuseFailAlloc_1685_, sizeof(void*)*3, v_action_1654_);
lean_ctor_set_uint8(v_reuseFailAlloc_1685_, sizeof(void*)*3 + 1, v_wantsRebuild_1655_);
v___x_1681_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1683_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 1, v___x_1681_);
v___x_1683_ = v___x_1678_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1675_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
}
else
{
uint8_t v___x_1688_; 
v___x_1688_ = l_System_Platform_isOSX;
if (v___x_1688_ == 0)
{
uint8_t v___x_1689_; 
v___x_1689_ = l_System_Platform_isWindows;
if (v___x_1689_ == 0)
{
lean_object* v_toContext_1690_; lean_object* v_lakeEnv_1691_; lean_object* v_lean_1692_; lean_object* v_log_1693_; uint8_t v_action_1694_; uint8_t v_wantsRebuild_1695_; lean_object* v_trace_1696_; lean_object* v_buildTime_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1727_; 
v_toContext_1690_ = lean_ctor_get(v___y_1647_, 1);
lean_inc(v_toContext_1690_);
lean_dec_ref(v___y_1647_);
v_lakeEnv_1691_ = lean_ctor_get(v_toContext_1690_, 1);
lean_inc_ref(v_lakeEnv_1691_);
lean_dec(v_toContext_1690_);
v_lean_1692_ = lean_ctor_get(v_lakeEnv_1691_, 1);
lean_inc_ref(v_lean_1692_);
lean_dec_ref(v_lakeEnv_1691_);
v_log_1693_ = lean_ctor_get(v___y_1648_, 0);
v_action_1694_ = lean_ctor_get_uint8(v___y_1648_, sizeof(void*)*3);
v_wantsRebuild_1695_ = lean_ctor_get_uint8(v___y_1648_, sizeof(void*)*3 + 1);
v_trace_1696_ = lean_ctor_get(v___y_1648_, 1);
v_buildTime_1697_ = lean_ctor_get(v___y_1648_, 2);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___y_1648_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1699_ = v___y_1648_;
v_isShared_1700_ = v_isSharedCheck_1727_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_buildTime_1697_);
lean_inc(v_trace_1696_);
lean_inc(v_log_1693_);
lean_dec(v___y_1648_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1727_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v_ar_1701_; lean_object* v___x_1702_; 
v_ar_1701_ = lean_ctor_get(v_lean_1692_, 12);
lean_inc_ref(v_ar_1701_);
lean_dec_ref(v_lean_1692_);
v___x_1702_ = l_Lake_compileStaticLib(v___y_1638_, v_oFiles_1639_, v_ar_1701_, v___x_1689_, v_log_1693_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1714_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
v_a_1704_ = lean_ctor_get(v___x_1702_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1706_ = v___x_1702_;
v_isShared_1707_ = v_isSharedCheck_1714_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_inc(v_a_1703_);
lean_dec(v___x_1702_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1714_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v_a_1704_);
v___x_1709_ = v___x_1699_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1704_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_trace_1696_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v_buildTime_1697_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, sizeof(void*)*3, v_action_1694_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, sizeof(void*)*3 + 1, v_wantsRebuild_1695_);
v___x_1709_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1711_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 1, v___x_1709_);
v___x_1711_ = v___x_1706_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1703_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1726_; 
v_a_1715_ = lean_ctor_get(v___x_1702_, 0);
v_a_1716_ = lean_ctor_get(v___x_1702_, 1);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1718_ = v___x_1702_;
v_isShared_1719_ = v_isSharedCheck_1726_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_inc(v_a_1715_);
lean_dec(v___x_1702_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1726_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v_a_1716_);
v___x_1721_ = v___x_1699_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1716_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_trace_1696_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_buildTime_1697_);
lean_ctor_set_uint8(v_reuseFailAlloc_1725_, sizeof(void*)*3, v_action_1694_);
lean_ctor_set_uint8(v_reuseFailAlloc_1725_, sizeof(void*)*3 + 1, v_wantsRebuild_1695_);
v___x_1721_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1723_; 
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 1, v___x_1721_);
v___x_1723_ = v___x_1718_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1715_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1728_; lean_object* v_lakeEnv_1729_; lean_object* v_lean_1730_; lean_object* v_log_1731_; uint8_t v_action_1732_; uint8_t v_wantsRebuild_1733_; lean_object* v_trace_1734_; lean_object* v_buildTime_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1765_; 
v_toContext_1728_ = lean_ctor_get(v___y_1647_, 1);
lean_inc(v_toContext_1728_);
lean_dec_ref(v___y_1647_);
v_lakeEnv_1729_ = lean_ctor_get(v_toContext_1728_, 1);
lean_inc_ref(v_lakeEnv_1729_);
lean_dec(v_toContext_1728_);
v_lean_1730_ = lean_ctor_get(v_lakeEnv_1729_, 1);
lean_inc_ref(v_lean_1730_);
lean_dec_ref(v_lakeEnv_1729_);
v_log_1731_ = lean_ctor_get(v___y_1648_, 0);
v_action_1732_ = lean_ctor_get_uint8(v___y_1648_, sizeof(void*)*3);
v_wantsRebuild_1733_ = lean_ctor_get_uint8(v___y_1648_, sizeof(void*)*3 + 1);
v_trace_1734_ = lean_ctor_get(v___y_1648_, 1);
v_buildTime_1735_ = lean_ctor_get(v___y_1648_, 2);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___y_1648_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1737_ = v___y_1648_;
v_isShared_1738_ = v_isSharedCheck_1765_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_buildTime_1735_);
lean_inc(v_trace_1734_);
lean_inc(v_log_1731_);
lean_dec(v___y_1648_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1765_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v_ar_1739_; lean_object* v___x_1740_; 
v_ar_1739_ = lean_ctor_get(v_lean_1730_, 12);
lean_inc_ref(v_ar_1739_);
lean_dec_ref(v_lean_1730_);
v___x_1740_ = l_Lake_compileStaticLib(v___y_1638_, v_oFiles_1639_, v_ar_1739_, v_shouldExport_1640_, v_log_1731_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1752_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_a_1742_ = lean_ctor_get(v___x_1740_, 1);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1744_ = v___x_1740_;
v_isShared_1745_ = v_isSharedCheck_1752_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1752_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v_a_1742_);
v___x_1747_ = v___x_1737_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1742_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_trace_1734_);
lean_ctor_set(v_reuseFailAlloc_1751_, 2, v_buildTime_1735_);
lean_ctor_set_uint8(v_reuseFailAlloc_1751_, sizeof(void*)*3, v_action_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1751_, sizeof(void*)*3 + 1, v_wantsRebuild_1733_);
v___x_1747_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1749_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v___x_1747_);
v___x_1749_ = v___x_1744_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1741_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1764_; 
v_a_1753_ = lean_ctor_get(v___x_1740_, 0);
v_a_1754_ = lean_ctor_get(v___x_1740_, 1);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1756_ = v___x_1740_;
v_isShared_1757_ = v_isSharedCheck_1764_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_inc(v_a_1753_);
lean_dec(v___x_1740_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1764_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v_a_1754_);
v___x_1759_ = v___x_1737_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1754_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_trace_1734_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_buildTime_1735_);
lean_ctor_set_uint8(v_reuseFailAlloc_1763_, sizeof(void*)*3, v_action_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1763_, sizeof(void*)*3 + 1, v_wantsRebuild_1733_);
v___x_1759_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1761_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v___x_1759_);
v___x_1761_ = v___x_1756_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1753_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1766_; uint8_t v_action_1767_; uint8_t v_wantsRebuild_1768_; lean_object* v_trace_1769_; lean_object* v_buildTime_1770_; lean_object* v___x_1771_; 
lean_dec_ref(v___y_1647_);
v_log_1766_ = lean_ctor_get(v___y_1648_, 0);
v_action_1767_ = lean_ctor_get_uint8(v___y_1648_, sizeof(void*)*3);
v_wantsRebuild_1768_ = lean_ctor_get_uint8(v___y_1648_, sizeof(void*)*3 + 1);
v_trace_1769_ = lean_ctor_get(v___y_1648_, 1);
v_buildTime_1770_ = lean_ctor_get(v___y_1648_, 2);
lean_inc_ref(v___y_1638_);
v___x_1771_ = l_Lake_createParentDirs(v___y_1638_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v_a_1775_; lean_object* v___y_1824_; uint8_t v___x_1826_; lean_object* v___x_1827_; 
lean_dec_ref(v___x_1771_);
v___x_1772_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1638_);
v___x_1773_ = l_System_FilePath_addExtension(v___y_1638_, v___x_1772_);
v___x_1826_ = 1;
v___x_1827_ = lean_io_prim_handle_mk(v___x_1773_, v___x_1826_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref(v___x_1827_);
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1830_ = lean_array_get_size(v_oFiles_1639_);
v___x_1831_ = lean_nat_dec_lt(v___x_1829_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_dec(v_a_1828_);
lean_dec_ref(v_oFiles_1639_);
v_a_1775_ = v___y_1648_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = lean_box(0);
v___x_1833_ = lean_nat_dec_le(v___x_1830_, v___x_1830_);
if (v___x_1833_ == 0)
{
if (v___x_1831_ == 0)
{
lean_dec(v_a_1828_);
lean_dec_ref(v_oFiles_1639_);
v_a_1775_ = v___y_1648_;
goto v___jp_1774_;
}
else
{
size_t v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_usize_of_nat(v___x_1830_);
v___x_1835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1828_, v_oFiles_1639_, v___x_1642_, v___x_1834_, v___x_1832_, v___y_1648_);
lean_dec_ref(v_oFiles_1639_);
lean_dec(v_a_1828_);
v___y_1824_ = v___x_1835_;
goto v___jp_1823_;
}
}
else
{
size_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = lean_usize_of_nat(v___x_1830_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1828_, v_oFiles_1639_, v___x_1642_, v___x_1836_, v___x_1832_, v___y_1648_);
lean_dec_ref(v_oFiles_1639_);
lean_dec(v_a_1828_);
v___y_1824_ = v___x_1837_;
goto v___jp_1823_;
}
}
}
else
{
lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1851_; 
lean_inc(v_buildTime_1770_);
lean_inc_ref(v_trace_1769_);
lean_inc_ref(v_log_1766_);
lean_dec_ref(v___x_1773_);
lean_dec_ref(v_oFiles_1639_);
lean_dec_ref(v___y_1638_);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___y_1648_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; 
v_unused_1852_ = lean_ctor_get(v___y_1648_, 2);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v___y_1648_, 1);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v___y_1648_, 0);
lean_dec(v_unused_1854_);
v___x_1839_ = v___y_1648_;
v_isShared_1840_ = v_isSharedCheck_1851_;
goto v_resetjp_1838_;
}
else
{
lean_dec(v___y_1648_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1851_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v_a_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v_a_1841_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1841_);
lean_dec_ref(v___x_1827_);
v___x_1842_ = lean_io_error_to_string(v_a_1841_);
v___x_1843_ = 3;
v___x_1844_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set_uint8(v___x_1844_, sizeof(void*)*1, v___x_1843_);
v___x_1845_ = lean_array_get_size(v_log_1766_);
v___x_1846_ = lean_array_push(v_log_1766_, v___x_1844_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1846_);
v___x_1848_ = v___x_1839_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_trace_1769_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_buildTime_1770_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*3, v_action_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*3 + 1, v_wantsRebuild_1768_);
v___x_1848_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1845_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
return v___x_1849_;
}
}
}
v___jp_1774_:
{
lean_object* v___x_1776_; lean_object* v_log_1777_; uint8_t v_action_1778_; uint8_t v_wantsRebuild_1779_; lean_object* v_trace_1780_; lean_object* v_buildTime_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1822_; 
v___x_1776_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1777_ = lean_ctor_get(v_a_1775_, 0);
v_action_1778_ = lean_ctor_get_uint8(v_a_1775_, sizeof(void*)*3);
v_wantsRebuild_1779_ = lean_ctor_get_uint8(v_a_1775_, sizeof(void*)*3 + 1);
v_trace_1780_ = lean_ctor_get(v_a_1775_, 1);
v_buildTime_1781_ = lean_ctor_get(v_a_1775_, 2);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_a_1775_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1783_ = v_a_1775_;
v_isShared_1784_ = v_isSharedCheck_1822_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_buildTime_1781_);
lean_inc(v_trace_1780_);
lean_inc(v_log_1777_);
lean_dec(v_a_1775_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1822_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1785_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1786_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1787_ = lean_unsigned_to_nat(5u);
v___x_1788_ = lean_mk_empty_array_with_capacity(v___x_1787_);
lean_dec_ref(v___x_1788_);
v___x_1789_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1790_ = lean_array_push(v___x_1789_, v___y_1638_);
v___x_1791_ = lean_array_push(v___x_1790_, v___x_1786_);
v___x_1792_ = lean_array_push(v___x_1791_, v___x_1773_);
v___x_1793_ = lean_box(0);
v___x_1794_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1795_ = 0;
v___x_1796_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1796_, 0, v___x_1776_);
lean_ctor_set(v___x_1796_, 1, v___x_1785_);
lean_ctor_set(v___x_1796_, 2, v___x_1792_);
lean_ctor_set(v___x_1796_, 3, v___x_1793_);
lean_ctor_set(v___x_1796_, 4, v___x_1794_);
lean_ctor_set_uint8(v___x_1796_, sizeof(void*)*5, v___x_1641_);
lean_ctor_set_uint8(v___x_1796_, sizeof(void*)*5 + 1, v___x_1795_);
v___x_1797_ = l_Lake_proc(v___x_1796_, v___x_1795_, v_log_1777_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1809_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_a_1799_ = lean_ctor_get(v___x_1797_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1801_ = v___x_1797_;
v_isShared_1802_ = v_isSharedCheck_1809_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1809_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v_a_1799_);
v___x_1804_ = v___x_1783_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1799_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_trace_1780_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_buildTime_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1808_, sizeof(void*)*3, v_action_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1808_, sizeof(void*)*3 + 1, v_wantsRebuild_1779_);
v___x_1804_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1806_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1804_);
v___x_1806_ = v___x_1801_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1798_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1821_; 
v_a_1810_ = lean_ctor_get(v___x_1797_, 0);
v_a_1811_ = lean_ctor_get(v___x_1797_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1813_ = v___x_1797_;
v_isShared_1814_ = v_isSharedCheck_1821_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_inc(v_a_1810_);
lean_dec(v___x_1797_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1821_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v_a_1811_);
v___x_1816_ = v___x_1783_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1811_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_trace_1780_);
lean_ctor_set(v_reuseFailAlloc_1820_, 2, v_buildTime_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*3, v_action_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*3 + 1, v_wantsRebuild_1779_);
v___x_1816_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1818_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 1, v___x_1816_);
v___x_1818_ = v___x_1813_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1810_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
}
v___jp_1823_:
{
if (lean_obj_tag(v___y_1824_) == 0)
{
lean_object* v_a_1825_; 
v_a_1825_ = lean_ctor_get(v___y_1824_, 1);
lean_inc(v_a_1825_);
lean_dec_ref(v___y_1824_);
v_a_1775_ = v_a_1825_;
goto v___jp_1774_;
}
else
{
lean_dec_ref(v___x_1773_);
lean_dec_ref(v___y_1638_);
return v___y_1824_;
}
}
}
else
{
lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1868_; 
lean_inc(v_buildTime_1770_);
lean_inc_ref(v_trace_1769_);
lean_inc_ref(v_log_1766_);
lean_dec_ref(v_oFiles_1639_);
lean_dec_ref(v___y_1638_);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___y_1648_);
if (v_isSharedCheck_1868_ == 0)
{
lean_object* v_unused_1869_; lean_object* v_unused_1870_; lean_object* v_unused_1871_; 
v_unused_1869_ = lean_ctor_get(v___y_1648_, 2);
lean_dec(v_unused_1869_);
v_unused_1870_ = lean_ctor_get(v___y_1648_, 1);
lean_dec(v_unused_1870_);
v_unused_1871_ = lean_ctor_get(v___y_1648_, 0);
lean_dec(v_unused_1871_);
v___x_1856_ = v___y_1648_;
v_isShared_1857_ = v_isSharedCheck_1868_;
goto v_resetjp_1855_;
}
else
{
lean_dec(v___y_1648_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1868_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v_a_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v_a_1858_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1858_);
lean_dec_ref(v___x_1771_);
v___x_1859_ = lean_io_error_to_string(v_a_1858_);
v___x_1860_ = 3;
v___x_1861_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set_uint8(v___x_1861_, sizeof(void*)*1, v___x_1860_);
v___x_1862_ = lean_array_get_size(v_log_1766_);
v___x_1863_ = lean_array_push(v_log_1766_, v___x_1861_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1863_);
v___x_1865_ = v___x_1856_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_trace_1769_);
lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_buildTime_1770_);
lean_ctor_set_uint8(v_reuseFailAlloc_1867_, sizeof(void*)*3, v_action_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1867_, sizeof(void*)*3 + 1, v_wantsRebuild_1768_);
v___x_1865_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1862_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
return v___x_1866_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v_bootstrap_1872_, lean_object* v___y_1873_, lean_object* v_oFiles_1874_, lean_object* v_shouldExport_1875_, lean_object* v___x_1876_, lean_object* v___x_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
uint8_t v_bootstrap_boxed_1885_; uint8_t v_shouldExport_boxed_1886_; uint8_t v___x_7506__boxed_1887_; size_t v___x_7507__boxed_1888_; lean_object* v_res_1889_; 
v_bootstrap_boxed_1885_ = lean_unbox(v_bootstrap_1872_);
v_shouldExport_boxed_1886_ = lean_unbox(v_shouldExport_1875_);
v___x_7506__boxed_1887_ = lean_unbox(v___x_1876_);
v___x_7507__boxed_1888_ = lean_unbox_usize(v___x_1877_);
lean_dec(v___x_1877_);
v_res_1889_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_1885_, v___y_1873_, v_oFiles_1874_, v_shouldExport_boxed_1886_, v___x_7506__boxed_1887_, v___x_7507__boxed_1888_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t v_bootstrap_1890_, lean_object* v___y_1891_, uint8_t v_shouldExport_1892_, uint8_t v___x_1893_, size_t v___x_1894_, lean_object* v_oFiles_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___y_1907_; uint8_t v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1903_ = lean_box(v_bootstrap_1890_);
v___x_1904_ = lean_box(v_shouldExport_1892_);
v___x_1905_ = lean_box(v___x_1893_);
v___x_1906_ = lean_box_usize(v___x_1894_);
lean_inc_ref(v___y_1891_);
v___y_1907_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 13, 6);
lean_closure_set(v___y_1907_, 0, v___x_1903_);
lean_closure_set(v___y_1907_, 1, v___y_1891_);
lean_closure_set(v___y_1907_, 2, v_oFiles_1895_);
lean_closure_set(v___y_1907_, 3, v___x_1904_);
lean_closure_set(v___y_1907_, 4, v___x_1905_);
lean_closure_set(v___y_1907_, 5, v___x_1906_);
v___x_1908_ = 0;
v___x_1909_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1910_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1891_, v___y_1907_, v___x_1908_, v___x_1909_, v___x_1893_, v___x_1908_, v___x_1908_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1920_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_a_1912_ = lean_ctor_get(v___x_1910_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1914_ = v___x_1910_;
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v_path_1916_; lean_object* v___x_1918_; 
v_path_1916_ = lean_ctor_get(v_a_1911_, 1);
lean_inc_ref(v_path_1916_);
lean_dec(v_a_1911_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v_path_1916_);
v___x_1918_ = v___x_1914_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_path_1916_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_a_1912_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
v_a_1921_ = lean_ctor_get(v___x_1910_, 0);
v_a_1922_ = lean_ctor_get(v___x_1910_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1910_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_inc(v_a_1921_);
lean_dec(v___x_1910_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1921_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* v_bootstrap_1930_, lean_object* v___y_1931_, lean_object* v_shouldExport_1932_, lean_object* v___x_1933_, lean_object* v___x_1934_, lean_object* v_oFiles_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
uint8_t v_bootstrap_boxed_1943_; uint8_t v_shouldExport_boxed_1944_; uint8_t v___x_7916__boxed_1945_; size_t v___x_7917__boxed_1946_; lean_object* v_res_1947_; 
v_bootstrap_boxed_1943_ = lean_unbox(v_bootstrap_1930_);
v_shouldExport_boxed_1944_ = lean_unbox(v_shouldExport_1932_);
v___x_7916__boxed_1945_ = lean_unbox(v___x_1933_);
v___x_7917__boxed_1946_ = lean_unbox_usize(v___x_1934_);
lean_dec(v___x_1934_);
v_res_1947_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_1943_, v___y_1931_, v_shouldExport_boxed_1944_, v___x_7916__boxed_1945_, v___x_7917__boxed_1946_, v_oFiles_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_1948_, size_t v_sz_1949_, size_t v_i_1950_, lean_object* v_bs_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
uint8_t v___x_1959_; 
v___x_1959_ = lean_usize_dec_lt(v_i_1950_, v_sz_1949_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; 
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec_ref(v_a_1948_);
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v_bs_1951_);
lean_ctor_set(v___x_1960_, 1, v___y_1957_);
return v___x_1960_;
}
else
{
lean_object* v_v_1961_; lean_object* v___x_1962_; 
v_v_1961_ = lean_array_uget_borrowed(v_bs_1951_, v_i_1950_);
lean_inc_ref(v___y_1956_);
lean_inc(v___y_1955_);
lean_inc(v___y_1954_);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1952_);
lean_inc_ref(v_a_1948_);
lean_inc(v_v_1961_);
v___x_1962_ = l_Lake_ModuleFacet_fetch___redArg(v_v_1961_, v_a_1948_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v_a_1964_; lean_object* v___x_1965_; lean_object* v_bs_x27_1966_; size_t v___x_1967_; size_t v___x_1968_; lean_object* v___x_1969_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
v_a_1964_ = lean_ctor_get(v___x_1962_, 1);
lean_inc(v_a_1964_);
lean_dec_ref(v___x_1962_);
v___x_1965_ = lean_unsigned_to_nat(0u);
v_bs_x27_1966_ = lean_array_uset(v_bs_1951_, v_i_1950_, v___x_1965_);
v___x_1967_ = ((size_t)1ULL);
v___x_1968_ = lean_usize_add(v_i_1950_, v___x_1967_);
v___x_1969_ = lean_array_uset(v_bs_x27_1966_, v_i_1950_, v_a_1963_);
v_i_1950_ = v___x_1968_;
v_bs_1951_ = v___x_1969_;
v___y_1957_ = v_a_1964_;
goto _start;
}
else
{
lean_object* v_a_1971_; lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec_ref(v_bs_1951_);
lean_dec_ref(v_a_1948_);
v_a_1971_ = lean_ctor_get(v___x_1962_, 0);
v_a_1972_ = lean_ctor_get(v___x_1962_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1962_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_inc(v_a_1971_);
lean_dec(v___x_1962_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1971_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_1980_, lean_object* v_sz_1981_, lean_object* v_i_1982_, lean_object* v_bs_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
size_t v_sz_boxed_1991_; size_t v_i_boxed_1992_; lean_object* v_res_1993_; 
v_sz_boxed_1991_ = lean_unbox_usize(v_sz_1981_);
lean_dec(v_sz_1981_);
v_i_boxed_1992_ = lean_unbox_usize(v_i_1982_);
lean_dec(v_i_1982_);
v_res_1993_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_1980_, v_sz_boxed_1991_, v_i_boxed_1992_, v_bs_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t v_shouldExport_1994_, lean_object* v_as_1995_, size_t v_i_1996_, size_t v_stop_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
uint8_t v___x_2006_; 
v___x_2006_ = lean_usize_dec_eq(v_i_1996_, v_stop_1997_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v_lib_2008_; lean_object* v_config_2009_; lean_object* v_nativeFacets_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; size_t v_sz_2013_; size_t v___x_2014_; lean_object* v___x_2015_; 
v___x_2007_ = lean_array_uget_borrowed(v_as_1995_, v_i_1996_);
v_lib_2008_ = lean_ctor_get(v___x_2007_, 0);
v_config_2009_ = lean_ctor_get(v_lib_2008_, 2);
v_nativeFacets_2010_ = lean_ctor_get(v_config_2009_, 8);
v___x_2011_ = lean_box(v_shouldExport_1994_);
lean_inc_ref(v_nativeFacets_2010_);
v___x_2012_ = lean_apply_1(v_nativeFacets_2010_, v___x_2011_);
v_sz_2013_ = lean_array_size(v___x_2012_);
v___x_2014_ = ((size_t)0ULL);
lean_inc_ref(v___y_2003_);
lean_inc(v___y_2002_);
lean_inc(v___y_2001_);
lean_inc(v___y_2000_);
lean_inc_ref(v___y_1999_);
lean_inc(v___x_2007_);
v___x_2015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2007_, v_sz_2013_, v___x_2014_, v___x_2012_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v_a_2017_; lean_object* v___x_2018_; size_t v___x_2019_; size_t v___x_2020_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
v_a_2017_ = lean_ctor_get(v___x_2015_, 1);
lean_inc(v_a_2017_);
lean_dec_ref(v___x_2015_);
v___x_2018_ = l_Array_append___redArg(v_b_1998_, v_a_2016_);
lean_dec(v_a_2016_);
v___x_2019_ = ((size_t)1ULL);
v___x_2020_ = lean_usize_add(v_i_1996_, v___x_2019_);
v_i_1996_ = v___x_2020_;
v_b_1998_ = v___x_2018_;
v___y_2004_ = v_a_2017_;
goto _start;
}
else
{
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v_b_1998_);
return v___x_2015_;
}
}
else
{
lean_object* v___x_2022_; 
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v_b_1998_);
lean_ctor_set(v___x_2022_, 1, v___y_2004_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object* v_shouldExport_2023_, lean_object* v_as_2024_, lean_object* v_i_2025_, lean_object* v_stop_2026_, lean_object* v_b_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v_shouldExport_boxed_2035_; size_t v_i_boxed_2036_; size_t v_stop_boxed_2037_; lean_object* v_res_2038_; 
v_shouldExport_boxed_2035_ = lean_unbox(v_shouldExport_2023_);
v_i_boxed_2036_ = lean_unbox_usize(v_i_2025_);
lean_dec(v_i_2025_);
v_stop_boxed_2037_ = lean_unbox_usize(v_stop_2026_);
lean_dec(v_stop_2026_);
v_res_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_2035_, v_as_2024_, v_i_boxed_2036_, v_stop_boxed_2037_, v_b_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec_ref(v_as_2024_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object* v___x_2039_, lean_object* v___x_2040_, lean_object* v_config_2041_, lean_object* v_config_2042_, lean_object* v_pkg_2043_, uint8_t v_shouldExport_2044_, uint8_t v___x_2045_, lean_object* v___x_2046_, lean_object* v_dir_2047_, lean_object* v_self_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___y_2057_; lean_object* v___y_2058_; size_t v___y_2059_; uint8_t v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v_a_2077_; lean_object* v_a_2078_; lean_object* v___y_2121_; lean_object* v___x_2133_; 
lean_inc_ref(v___y_2049_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2040_);
v___x_2133_ = lean_apply_7(v___y_2049_, v___x_2039_, v___x_2040_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, lean_box(0));
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v_a_2135_; lean_object* v___x_2136_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
v_a_2135_ = lean_ctor_get(v___x_2133_, 1);
lean_inc(v_a_2135_);
lean_dec_ref(v___x_2133_);
v___x_2136_ = l_Lake_Job_await___redArg(v_a_2134_, v_a_2135_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v_a_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
v_a_2138_ = lean_ctor_get(v___x_2136_, 1);
lean_inc(v_a_2138_);
lean_dec_ref(v___x_2136_);
v___x_2139_ = lean_unsigned_to_nat(0u);
v___x_2140_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_2141_ = lean_array_get_size(v_a_2137_);
v___x_2142_ = lean_nat_dec_lt(v___x_2139_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_dec(v_a_2137_);
v_a_2077_ = v___x_2140_;
v_a_2078_ = v_a_2138_;
goto v___jp_2076_;
}
else
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_nat_dec_le(v___x_2141_, v___x_2141_);
if (v___x_2143_ == 0)
{
if (v___x_2142_ == 0)
{
lean_dec(v_a_2137_);
v_a_2077_ = v___x_2140_;
v_a_2078_ = v_a_2138_;
goto v___jp_2076_;
}
else
{
size_t v___x_2144_; size_t v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = ((size_t)0ULL);
v___x_2145_ = lean_usize_of_nat(v___x_2141_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2040_);
lean_inc_ref(v___y_2049_);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2044_, v_a_2137_, v___x_2144_, v___x_2145_, v___x_2140_, v___y_2049_, v___x_2040_, v___y_2051_, v___y_2052_, v___y_2053_, v_a_2138_);
lean_dec(v_a_2137_);
v___y_2121_ = v___x_2146_;
goto v___jp_2120_;
}
}
else
{
size_t v___x_2147_; size_t v___x_2148_; lean_object* v___x_2149_; 
v___x_2147_ = ((size_t)0ULL);
v___x_2148_ = lean_usize_of_nat(v___x_2141_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2040_);
lean_inc_ref(v___y_2049_);
v___x_2149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2044_, v_a_2137_, v___x_2147_, v___x_2148_, v___x_2140_, v___y_2049_, v___x_2040_, v___y_2051_, v___y_2052_, v___y_2053_, v_a_2138_);
lean_dec(v_a_2137_);
v___y_2121_ = v___x_2149_;
goto v___jp_2120_;
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_self_2048_);
lean_dec_ref(v_dir_2047_);
lean_dec(v___x_2046_);
lean_dec_ref(v_pkg_2043_);
lean_dec_ref(v_config_2041_);
lean_dec(v___x_2040_);
v_a_2150_ = lean_ctor_get(v___x_2136_, 0);
v_a_2151_ = lean_ctor_get(v___x_2136_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2136_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_inc(v_a_2150_);
lean_dec(v___x_2136_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2150_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_self_2048_);
lean_dec_ref(v_dir_2047_);
lean_dec(v___x_2046_);
lean_dec_ref(v_pkg_2043_);
lean_dec_ref(v_config_2041_);
lean_dec(v___x_2040_);
v_a_2159_ = lean_ctor_get(v___x_2133_, 0);
v_a_2160_ = lean_ctor_get(v___x_2133_, 1);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2133_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_inc(v_a_2159_);
lean_dec(v___x_2133_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2159_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
v___jp_2056_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___f_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2063_ = lean_box(v___y_2060_);
v___x_2064_ = lean_box(v_shouldExport_2044_);
v___x_2065_ = lean_box(v___x_2045_);
v___x_2066_ = lean_box_usize(v___y_2059_);
v___f_2067_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2067_, 0, v___x_2063_);
lean_closure_set(v___f_2067_, 1, v___y_2062_);
lean_closure_set(v___f_2067_, 2, v___x_2064_);
lean_closure_set(v___f_2067_, 3, v___x_2065_);
lean_closure_set(v___f_2067_, 4, v___x_2066_);
v___x_2068_ = l_Array_append___redArg(v___y_2061_, v___y_2057_);
lean_dec_ref(v___y_2057_);
v___x_2069_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_2070_ = l_Lake_Job_collectArray___redArg(v___x_2068_, v___x_2069_);
lean_dec_ref(v___x_2068_);
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = 0;
v___x_2073_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2074_ = l_Lake_Job_mapM___redArg(v___x_2046_, v___x_2070_, v___f_2067_, v___x_2071_, v___x_2072_, v___y_2049_, v___x_2040_, v___y_2051_, v___y_2052_, v___y_2053_, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
lean_ctor_set(v___x_2075_, 1, v___y_2058_);
return v___x_2075_;
}
v___jp_2076_:
{
lean_object* v_toLeanConfig_2079_; lean_object* v_toLeanConfig_2080_; uint8_t v_bootstrap_2081_; lean_object* v_buildDir_2082_; lean_object* v_nativeLibDir_2083_; lean_object* v_moreLinkObjs_2084_; lean_object* v_moreLinkObjs_2085_; lean_object* v___x_2086_; size_t v_sz_2087_; size_t v___x_2088_; lean_object* v___x_2089_; 
v_toLeanConfig_2079_ = lean_ctor_get(v_config_2041_, 1);
lean_inc_ref(v_toLeanConfig_2079_);
v_toLeanConfig_2080_ = lean_ctor_get(v_config_2042_, 0);
v_bootstrap_2081_ = lean_ctor_get_uint8(v_config_2041_, sizeof(void*)*26);
v_buildDir_2082_ = lean_ctor_get(v_config_2041_, 5);
lean_inc_ref(v_buildDir_2082_);
v_nativeLibDir_2083_ = lean_ctor_get(v_config_2041_, 7);
lean_inc_ref(v_nativeLibDir_2083_);
lean_dec_ref(v_config_2041_);
v_moreLinkObjs_2084_ = lean_ctor_get(v_toLeanConfig_2079_, 6);
lean_inc_ref(v_moreLinkObjs_2084_);
lean_dec_ref(v_toLeanConfig_2079_);
v_moreLinkObjs_2085_ = lean_ctor_get(v_toLeanConfig_2080_, 6);
v___x_2086_ = l_Array_append___redArg(v_moreLinkObjs_2084_, v_moreLinkObjs_2085_);
v_sz_2087_ = lean_array_size(v___x_2086_);
v___x_2088_ = ((size_t)0ULL);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc(v___x_2040_);
lean_inc_ref(v___y_2049_);
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_2043_, v_sz_2087_, v___x_2088_, v___x_2086_, v___y_2049_, v___x_2040_, v___y_2051_, v___y_2052_, v___y_2053_, v_a_2078_);
if (lean_obj_tag(v___x_2089_) == 0)
{
if (v_shouldExport_2044_ == 0)
{
lean_object* v_a_2090_; lean_object* v_a_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
v_a_2091_ = lean_ctor_get(v___x_2089_, 1);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2089_);
v___x_2092_ = l_System_FilePath_normalize(v_buildDir_2082_);
v___x_2093_ = l_Lake_joinRelative(v_dir_2047_, v___x_2092_);
v___x_2094_ = l_System_FilePath_normalize(v_nativeLibDir_2083_);
v___x_2095_ = l_Lake_joinRelative(v___x_2093_, v___x_2094_);
v___x_2096_ = l_Lake_LeanLib_libName(v_self_2048_);
v___x_2097_ = l_Lake_nameToStaticLib(v___x_2096_, v_shouldExport_2044_);
v___x_2098_ = l_Lake_joinRelative(v___x_2095_, v___x_2097_);
v___y_2057_ = v_a_2090_;
v___y_2058_ = v_a_2091_;
v___y_2059_ = v___x_2088_;
v___y_2060_ = v_bootstrap_2081_;
v___y_2061_ = v_a_2077_;
v___y_2062_ = v___x_2098_;
goto v___jp_2056_;
}
else
{
lean_object* v_a_2099_; lean_object* v_a_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_a_2099_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2099_);
v_a_2100_ = lean_ctor_get(v___x_2089_, 1);
lean_inc(v_a_2100_);
lean_dec_ref(v___x_2089_);
v___x_2101_ = l_System_FilePath_normalize(v_buildDir_2082_);
v___x_2102_ = l_Lake_joinRelative(v_dir_2047_, v___x_2101_);
v___x_2103_ = l_System_FilePath_normalize(v_nativeLibDir_2083_);
v___x_2104_ = l_Lake_joinRelative(v___x_2102_, v___x_2103_);
v___x_2105_ = l_Lake_LeanLib_libName(v_self_2048_);
v___x_2106_ = 0;
v___x_2107_ = l_Lake_nameToStaticLib(v___x_2105_, v___x_2106_);
v___x_2108_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_2109_ = l_System_FilePath_addExtension(v___x_2107_, v___x_2108_);
v___x_2110_ = l_Lake_joinRelative(v___x_2104_, v___x_2109_);
v___y_2057_ = v_a_2099_;
v___y_2058_ = v_a_2100_;
v___y_2059_ = v___x_2088_;
v___y_2060_ = v_bootstrap_2081_;
v___y_2061_ = v_a_2077_;
v___y_2062_ = v___x_2110_;
goto v___jp_2056_;
}
}
else
{
lean_object* v_a_2111_; lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref(v_nativeLibDir_2083_);
lean_dec_ref(v_buildDir_2082_);
lean_dec_ref(v_a_2077_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_self_2048_);
lean_dec_ref(v_dir_2047_);
lean_dec(v___x_2046_);
lean_dec(v___x_2040_);
v_a_2111_ = lean_ctor_get(v___x_2089_, 0);
v_a_2112_ = lean_ctor_get(v___x_2089_, 1);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2089_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_inc(v_a_2111_);
lean_dec(v___x_2089_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2111_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
v___jp_2120_:
{
if (lean_obj_tag(v___y_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v_a_2123_; 
v_a_2122_ = lean_ctor_get(v___y_2121_, 0);
lean_inc(v_a_2122_);
v_a_2123_ = lean_ctor_get(v___y_2121_, 1);
lean_inc(v_a_2123_);
lean_dec_ref(v___y_2121_);
v_a_2077_ = v_a_2122_;
v_a_2078_ = v_a_2123_;
goto v___jp_2076_;
}
else
{
lean_object* v_a_2124_; lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_self_2048_);
lean_dec_ref(v_dir_2047_);
lean_dec(v___x_2046_);
lean_dec_ref(v_pkg_2043_);
lean_dec_ref(v_config_2041_);
lean_dec(v___x_2040_);
v_a_2124_ = lean_ctor_get(v___y_2121_, 0);
v_a_2125_ = lean_ctor_get(v___y_2121_, 1);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___y_2121_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___y_2121_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_inc(v_a_2124_);
lean_dec(v___y_2121_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2124_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object** _args){
lean_object* v___x_2168_ = _args[0];
lean_object* v___x_2169_ = _args[1];
lean_object* v_config_2170_ = _args[2];
lean_object* v_config_2171_ = _args[3];
lean_object* v_pkg_2172_ = _args[4];
lean_object* v_shouldExport_2173_ = _args[5];
lean_object* v___x_2174_ = _args[6];
lean_object* v___x_2175_ = _args[7];
lean_object* v_dir_2176_ = _args[8];
lean_object* v_self_2177_ = _args[9];
lean_object* v___y_2178_ = _args[10];
lean_object* v___y_2179_ = _args[11];
lean_object* v___y_2180_ = _args[12];
lean_object* v___y_2181_ = _args[13];
lean_object* v___y_2182_ = _args[14];
lean_object* v___y_2183_ = _args[15];
lean_object* v___y_2184_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_2185_; uint8_t v___x_8118__boxed_2186_; lean_object* v_res_2187_; 
v_shouldExport_boxed_2185_ = lean_unbox(v_shouldExport_2173_);
v___x_8118__boxed_2186_ = lean_unbox(v___x_2174_);
v_res_2187_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v___x_2168_, v___x_2169_, v_config_2170_, v_config_2171_, v_pkg_2172_, v_shouldExport_boxed_2185_, v___x_8118__boxed_2186_, v___x_2175_, v_dir_2176_, v_self_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2179_);
lean_dec(v_config_2171_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_2188_, lean_object* v_self_2189_, uint8_t v_shouldExport_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_toBuildConfig_2197_; lean_object* v_registeredJobs_2198_; uint8_t v_verbosity_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; uint8_t v___x_2202_; uint8_t v___x_2203_; lean_object* v___y_2205_; 
v_toBuildConfig_2197_ = lean_ctor_get(v_a_2194_, 0);
v_registeredJobs_2198_ = lean_ctor_get(v_a_2194_, 3);
lean_inc(v_registeredJobs_2198_);
v_verbosity_2199_ = lean_ctor_get_uint8(v_toBuildConfig_2197_, sizeof(void*)*2 + 3);
v___x_2200_ = l_Lake_instDataKindFilePath;
v___x_2201_ = 2;
v___x_2202_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2199_, v___x_2201_);
v___x_2203_ = 1;
if (v___x_2202_ == 0)
{
lean_object* v___x_2250_; 
v___x_2250_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_2205_ = v___x_2250_;
goto v___jp_2204_;
}
else
{
if (v_shouldExport_2190_ == 0)
{
lean_object* v___x_2251_; 
v___x_2251_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_2205_ = v___x_2251_;
goto v___jp_2204_;
}
else
{
lean_object* v___x_2252_; 
v___x_2252_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_2205_ = v___x_2252_;
goto v___jp_2204_;
}
}
v___jp_2204_:
{
lean_object* v_pkg_2206_; lean_object* v_name_2207_; lean_object* v_config_2208_; lean_object* v_keyName_2209_; lean_object* v_dir_2210_; lean_object* v_config_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___f_2219_; lean_object* v___x_2220_; 
v_pkg_2206_ = lean_ctor_get(v_self_2189_, 0);
lean_inc_ref(v_pkg_2206_);
v_name_2207_ = lean_ctor_get(v_self_2189_, 1);
lean_inc(v_name_2207_);
v_config_2208_ = lean_ctor_get(v_self_2189_, 2);
lean_inc(v_config_2208_);
v_keyName_2209_ = lean_ctor_get(v_pkg_2206_, 2);
v_dir_2210_ = lean_ctor_get(v_pkg_2206_, 4);
lean_inc_ref(v_dir_2210_);
v_config_2211_ = lean_ctor_get(v_pkg_2206_, 6);
lean_inc_ref(v_config_2211_);
v___x_2212_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_2207_);
lean_inc(v_keyName_2209_);
v___x_2213_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2213_, 0, v_keyName_2209_);
lean_ctor_set(v___x_2213_, 1, v_name_2207_);
v___x_2214_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2189_);
v___x_2215_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2213_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
lean_ctor_set(v___x_2215_, 2, v_self_2189_);
lean_ctor_set(v___x_2215_, 3, v___x_2212_);
lean_inc_ref(v_pkg_2206_);
v___x_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2216_, 0, v_pkg_2206_);
v___x_2217_ = lean_box(v_shouldExport_2190_);
v___x_2218_ = lean_box(v___x_2203_);
v___f_2219_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed), 17, 10);
lean_closure_set(v___f_2219_, 0, v___x_2215_);
lean_closure_set(v___f_2219_, 1, v___x_2216_);
lean_closure_set(v___f_2219_, 2, v_config_2211_);
lean_closure_set(v___f_2219_, 3, v_config_2208_);
lean_closure_set(v___f_2219_, 4, v_pkg_2206_);
lean_closure_set(v___f_2219_, 5, v___x_2217_);
lean_closure_set(v___f_2219_, 6, v___x_2218_);
lean_closure_set(v___f_2219_, 7, v___x_2200_);
lean_closure_set(v___f_2219_, 8, v_dir_2210_);
lean_closure_set(v___f_2219_, 9, v_self_2189_);
v___x_2220_ = l_Lake_ensureJob___redArg(v___x_2200_, v___f_2219_, v___y_2188_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2249_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_a_2222_ = lean_ctor_get(v___x_2220_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2224_ = v___x_2220_;
v_isShared_2225_ = v_isSharedCheck_2249_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2249_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v_task_2226_; lean_object* v_kind_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2247_; 
v_task_2226_ = lean_ctor_get(v_a_2221_, 0);
v_kind_2227_ = lean_ctor_get(v_a_2221_, 1);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_a_2221_);
if (v_isSharedCheck_2247_ == 0)
{
lean_object* v_unused_2248_; 
v_unused_2248_ = lean_ctor_get(v_a_2221_, 2);
lean_dec(v_unused_2248_);
v___x_2229_ = v_a_2221_;
v_isShared_2230_ = v_isSharedCheck_2247_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_kind_2227_);
lean_inc(v_task_2226_);
lean_dec(v_a_2221_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2247_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; lean_object* v_job_2238_; 
v___x_2231_ = lean_st_ref_take(v_registeredJobs_2198_);
v___x_2232_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2207_, v___x_2203_);
v___x_2233_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_2234_ = lean_string_append(v___x_2232_, v___x_2233_);
v___x_2235_ = lean_string_append(v___x_2234_, v___y_2205_);
lean_dec_ref(v___y_2205_);
v___x_2236_ = 0;
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 2, v___x_2235_);
v_job_2238_ = v___x_2229_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_task_2226_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_kind_2227_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v___x_2235_);
v_job_2238_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2244_; 
lean_ctor_set_uint8(v_job_2238_, sizeof(void*)*3, v___x_2236_);
lean_inc_ref(v_job_2238_);
v___x_2239_ = l_Lake_Job_toOpaque___redArg(v_job_2238_);
v___x_2240_ = lean_array_push(v___x_2231_, v___x_2239_);
v___x_2241_ = lean_st_ref_set(v_registeredJobs_2198_, v___x_2240_);
lean_dec(v_registeredJobs_2198_);
v___x_2242_ = l_Lake_Job_renew___redArg(v_job_2238_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2242_);
v___x_2244_ = v___x_2224_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_a_2222_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
else
{
lean_dec(v_name_2207_);
lean_dec_ref(v___y_2205_);
lean_dec(v_registeredJobs_2198_);
return v___x_2220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_2253_, lean_object* v_self_2254_, lean_object* v_shouldExport_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
uint8_t v_shouldExport_boxed_2262_; lean_object* v_res_2263_; 
v_shouldExport_boxed_2262_ = lean_unbox(v_shouldExport_2255_);
v_res_2263_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2253_, v_self_2254_, v_shouldExport_boxed_2262_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
uint8_t v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = 0;
v___x_2273_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2265_, v_x_2264_, v___x_2272_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
return v_res_2282_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; lean_object* v___f_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___f_2285_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2286_ = 1;
v___x_2287_ = l_Lake_instDataKindFilePath;
v___f_2288_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_2289_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2290_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set(v___x_2290_, 1, v___f_2288_);
lean_ctor_set(v___x_2290_, 2, v___x_2287_);
lean_ctor_set(v___x_2290_, 3, v___f_2285_);
lean_ctor_set_uint8(v___x_2290_, sizeof(void*)*4, v___x_2286_);
lean_ctor_set_uint8(v___x_2290_, sizeof(void*)*4 + 1, v___x_2286_);
return v___x_2290_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object* v_a_2292_, lean_object* v_as_2293_, size_t v_i_2294_, size_t v_stop_2295_, lean_object* v_b_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2292_, v_as_2293_, v_i_2294_, v_stop_2295_, v_b_2296_, v___y_2302_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_a_2305_, lean_object* v_as_2306_, lean_object* v_i_2307_, lean_object* v_stop_2308_, lean_object* v_b_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
size_t v_i_boxed_2317_; size_t v_stop_boxed_2318_; lean_object* v_res_2319_; 
v_i_boxed_2317_ = lean_unbox_usize(v_i_2307_);
lean_dec(v_i_2307_);
v_stop_boxed_2318_ = lean_unbox_usize(v_stop_2308_);
lean_dec(v_stop_2308_);
v_res_2319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2305_, v_as_2306_, v_i_boxed_2317_, v_stop_boxed_2318_, v_b_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec_ref(v_as_2306_);
lean_dec(v_a_2305_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = 1;
v___x_2329_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2321_, v_x_2320_, v___x_2328_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
return v_res_2338_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___f_2340_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2341_ = 1;
v___x_2342_ = l_Lake_instDataKindFilePath;
v___f_2343_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_2344_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2345_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
lean_ctor_set(v___x_2345_, 1, v___f_2343_);
lean_ctor_set(v___x_2345_, 2, v___x_2342_);
lean_ctor_set(v___x_2345_, 3, v___f_2340_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*4, v___x_2341_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*4 + 1, v___x_2341_);
return v___x_2345_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_2346_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_2347_; lean_object* v_name_2348_; lean_object* v___x_2349_; 
v___x_2347_ = 1;
v_name_2348_ = l_Lake_instDataKindDynlib;
v___x_2349_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2348_, v___x_2347_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_2350_, lean_object* v_self_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
uint8_t v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = 1;
lean_inc_ref_n(v_self_2351_, 2);
v___x_2360_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_2350_, v_self_2351_, v_self_2351_, v___x_2359_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v_snd_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2403_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
v_snd_2362_ = lean_ctor_get(v_a_2361_, 1);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_a_2361_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; 
v_unused_2404_ = lean_ctor_get(v_a_2361_, 0);
lean_dec(v_unused_2404_);
v___x_2364_ = v_a_2361_;
v_isShared_2365_ = v_isSharedCheck_2403_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_snd_2362_);
lean_dec(v_a_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2403_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2401_; 
v_a_2366_ = lean_ctor_get(v___x_2360_, 1);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; 
v_unused_2402_ = lean_ctor_get(v___x_2360_, 0);
lean_dec(v_unused_2402_);
v___x_2368_ = v___x_2360_;
v_isShared_2369_ = v_isSharedCheck_2401_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2360_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2401_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v_kind_2370_; lean_object* v_name_2371_; lean_object* v___y_2373_; uint8_t v___x_2391_; 
v_kind_2370_ = lean_ctor_get(v_snd_2362_, 1);
v_name_2371_ = l_Lake_instDataKindDynlib;
v___x_2391_ = lean_name_eq(v_kind_2370_, v_name_2371_);
if (v___x_2391_ == 0)
{
uint8_t v___x_2392_; 
lean_inc(v_kind_2370_);
lean_del_object(v___x_2364_);
lean_dec(v_snd_2362_);
v___x_2392_ = l_Lean_Name_isAnonymous(v_kind_2370_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2393_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_2394_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2370_, v___x_2359_);
v___x_2395_ = lean_string_append(v___x_2393_, v___x_2394_);
lean_dec_ref(v___x_2394_);
v___x_2396_ = lean_string_append(v___x_2395_, v___x_2393_);
v___y_2373_ = v___x_2396_;
goto v___jp_2372_;
}
else
{
lean_object* v___x_2397_; 
lean_dec(v_kind_2370_);
v___x_2397_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_2373_ = v___x_2397_;
goto v___jp_2372_;
}
}
else
{
lean_object* v___x_2399_; 
lean_del_object(v___x_2368_);
lean_dec_ref(v_self_2351_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 1, v_a_2366_);
lean_ctor_set(v___x_2364_, 0, v_snd_2362_);
v___x_2399_ = v___x_2364_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_snd_2362_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_a_2366_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
v___jp_2372_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
v___x_2374_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_2375_ = l_Lake_PartialBuildKey_toString(v_self_2351_);
v___x_2376_ = lean_string_append(v___x_2374_, v___x_2375_);
lean_dec_ref(v___x_2375_);
v___x_2377_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_2378_ = lean_string_append(v___x_2376_, v___x_2377_);
v___x_2379_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
v___x_2380_ = lean_string_append(v___x_2378_, v___x_2379_);
v___x_2381_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_2382_ = lean_string_append(v___x_2380_, v___x_2381_);
v___x_2383_ = lean_string_append(v___x_2382_, v___y_2373_);
lean_dec_ref(v___y_2373_);
v___x_2384_ = 3;
v___x_2385_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set_uint8(v___x_2385_, sizeof(void*)*1, v___x_2384_);
v___x_2386_ = lean_array_get_size(v_a_2366_);
v___x_2387_ = lean_array_push(v_a_2366_, v___x_2385_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set_tag(v___x_2368_, 1);
lean_ctor_set(v___x_2368_, 1, v___x_2387_);
lean_ctor_set(v___x_2368_, 0, v___x_2386_);
v___x_2389_ = v___x_2368_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec_ref(v_self_2351_);
v_a_2405_ = lean_ctor_get(v___x_2360_, 0);
v_a_2406_ = lean_ctor_get(v___x_2360_, 1);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2360_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_inc(v_a_2405_);
lean_dec(v___x_2360_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2405_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_2414_, lean_object* v_self_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2414_, v_self_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
return v_res_2423_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2426_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_2427_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v___x_2426_);
return v___x_2428_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_2430_, lean_object* v_as_2431_, size_t v_i_2432_, size_t v_stop_2433_, lean_object* v_b_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
uint8_t v___x_2442_; 
v___x_2442_ = lean_usize_dec_eq(v_i_2432_, v_stop_2433_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_array_uget_borrowed(v_as_2431_, v_i_2432_);
lean_inc_ref(v___y_2439_);
lean_inc(v___y_2438_);
lean_inc(v___y_2437_);
lean_inc(v___y_2436_);
lean_inc_ref(v___y_2435_);
lean_inc(v___x_2443_);
lean_inc_ref(v___x_2430_);
v___x_2444_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_2430_, v___x_2443_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v_a_2446_; lean_object* v___x_2447_; size_t v___x_2448_; size_t v___x_2449_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_a_2445_);
v_a_2446_ = lean_ctor_get(v___x_2444_, 1);
lean_inc(v_a_2446_);
lean_dec_ref(v___x_2444_);
v___x_2447_ = lean_array_push(v_b_2434_, v_a_2445_);
v___x_2448_ = ((size_t)1ULL);
v___x_2449_ = lean_usize_add(v_i_2432_, v___x_2448_);
v_i_2432_ = v___x_2449_;
v_b_2434_ = v___x_2447_;
v___y_2440_ = v_a_2446_;
goto _start;
}
else
{
lean_object* v_a_2451_; lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec_ref(v_b_2434_);
lean_dec_ref(v___x_2430_);
v_a_2451_ = lean_ctor_get(v___x_2444_, 0);
v_a_2452_ = lean_ctor_get(v___x_2444_, 1);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2444_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_inc(v_a_2451_);
lean_dec(v___x_2444_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2451_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
else
{
lean_object* v___x_2460_; 
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec_ref(v___x_2430_);
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v_b_2434_);
lean_ctor_set(v___x_2460_, 1, v___y_2440_);
return v___x_2460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_2461_, lean_object* v_as_2462_, lean_object* v_i_2463_, lean_object* v_stop_2464_, lean_object* v_b_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
size_t v_i_boxed_2473_; size_t v_stop_boxed_2474_; lean_object* v_res_2475_; 
v_i_boxed_2473_ = lean_unbox_usize(v_i_2463_);
lean_dec(v_i_2463_);
v_stop_boxed_2474_ = lean_unbox_usize(v_stop_2464_);
lean_dec(v_stop_2464_);
v_res_2475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2461_, v_as_2462_, v_i_boxed_2473_, v_stop_boxed_2474_, v_b_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
lean_dec_ref(v_as_2462_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_toHashSet_2478_; lean_object* v_toArray_2479_; uint8_t v___x_2480_; 
v_toHashSet_2478_ = lean_ctor_get(v_self_2476_, 0);
v_toArray_2479_ = lean_ctor_get(v_self_2476_, 1);
v___x_2480_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_2478_, v_a_2477_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2490_; 
lean_inc_ref(v_toArray_2479_);
lean_inc_ref(v_toHashSet_2478_);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_self_2476_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; lean_object* v_unused_2492_; 
v_unused_2491_ = lean_ctor_get(v_self_2476_, 1);
lean_dec(v_unused_2491_);
v_unused_2492_ = lean_ctor_get(v_self_2476_, 0);
lean_dec(v_unused_2492_);
v___x_2482_ = v_self_2476_;
v_isShared_2483_ = v_isSharedCheck_2490_;
goto v_resetjp_2481_;
}
else
{
lean_dec(v_self_2476_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2490_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2484_ = lean_box(0);
lean_inc_ref(v_a_2477_);
v___x_2485_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_2478_, v_a_2477_, v___x_2484_);
v___x_2486_ = lean_array_push(v_toArray_2479_, v_a_2477_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v___x_2486_);
lean_ctor_set(v___x_2482_, 0, v___x_2485_);
v___x_2488_ = v___x_2482_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
else
{
lean_dec_ref(v_a_2477_);
return v_self_2476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_2493_, size_t v_i_2494_, size_t v_stop_2495_, lean_object* v_b_2496_){
_start:
{
uint8_t v___x_2497_; 
v___x_2497_ = lean_usize_dec_eq(v_i_2494_, v_stop_2495_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; size_t v___x_2500_; size_t v___x_2501_; 
v___x_2498_ = lean_array_uget_borrowed(v_as_2493_, v_i_2494_);
lean_inc(v___x_2498_);
v___x_2499_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_2496_, v___x_2498_);
v___x_2500_ = ((size_t)1ULL);
v___x_2501_ = lean_usize_add(v_i_2494_, v___x_2500_);
v_i_2494_ = v___x_2501_;
v_b_2496_ = v___x_2499_;
goto _start;
}
else
{
return v_b_2496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_2503_, lean_object* v_i_2504_, lean_object* v_stop_2505_, lean_object* v_b_2506_){
_start:
{
size_t v_i_boxed_2507_; size_t v_stop_boxed_2508_; lean_object* v_res_2509_; 
v_i_boxed_2507_ = lean_unbox_usize(v_i_2504_);
lean_dec(v_i_2504_);
v_stop_boxed_2508_ = lean_unbox_usize(v_stop_2505_);
lean_dec(v_stop_2505_);
v_res_2509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2503_, v_i_boxed_2507_, v_stop_boxed_2508_, v_b_2506_);
lean_dec_ref(v_as_2503_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_2510_, lean_object* v_arr_2511_){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2512_ = lean_unsigned_to_nat(0u);
v___x_2513_ = lean_array_get_size(v_arr_2511_);
v___x_2514_ = lean_nat_dec_lt(v___x_2512_, v___x_2513_);
if (v___x_2514_ == 0)
{
return v_self_2510_;
}
else
{
uint8_t v___x_2515_; 
v___x_2515_ = lean_nat_dec_le(v___x_2513_, v___x_2513_);
if (v___x_2515_ == 0)
{
if (v___x_2514_ == 0)
{
return v_self_2510_;
}
else
{
size_t v___x_2516_; size_t v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = ((size_t)0ULL);
v___x_2517_ = lean_usize_of_nat(v___x_2513_);
v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2511_, v___x_2516_, v___x_2517_, v_self_2510_);
return v___x_2518_;
}
}
else
{
size_t v___x_2519_; size_t v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = ((size_t)0ULL);
v___x_2520_ = lean_usize_of_nat(v___x_2513_);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2511_, v___x_2519_, v___x_2520_, v_self_2510_);
return v___x_2521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object* v_self_2522_, lean_object* v_arr_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_self_2522_, v_arr_2523_);
lean_dec_ref(v_arr_2523_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object* v_as_2525_, size_t v_i_2526_, size_t v_stop_2527_, lean_object* v_b_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
uint8_t v___x_2536_; 
v___x_2536_ = lean_usize_dec_eq(v_i_2526_, v_stop_2527_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; lean_object* v_lib_2538_; lean_object* v_pkg_2539_; lean_object* v_name_2540_; lean_object* v_keyName_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2537_ = lean_array_uget_borrowed(v_as_2525_, v_i_2526_);
v_lib_2538_ = lean_ctor_get(v___x_2537_, 0);
v_pkg_2539_ = lean_ctor_get(v_lib_2538_, 0);
v_name_2540_ = lean_ctor_get(v___x_2537_, 1);
v_keyName_2541_ = lean_ctor_get(v_pkg_2539_, 2);
v___x_2542_ = l_Lake_Module_transImportsFacet;
lean_inc(v_name_2540_);
lean_inc(v_keyName_2541_);
v___x_2543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2543_, 0, v_keyName_2541_);
lean_ctor_set(v___x_2543_, 1, v_name_2540_);
v___x_2544_ = l_Lake_Module_keyword;
lean_inc(v___x_2537_);
v___x_2545_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
lean_ctor_set(v___x_2545_, 2, v___x_2537_);
lean_ctor_set(v___x_2545_, 3, v___x_2542_);
lean_inc_ref(v___y_2529_);
lean_inc_ref(v___y_2533_);
lean_inc(v___y_2532_);
lean_inc(v___y_2531_);
lean_inc(v___y_2530_);
v___x_2546_ = lean_apply_7(v___y_2529_, v___x_2545_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, lean_box(0));
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v_a_2548_; lean_object* v___x_2549_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
v_a_2548_ = lean_ctor_get(v___x_2546_, 1);
lean_inc(v_a_2548_);
lean_dec_ref(v___x_2546_);
v___x_2549_ = l_Lake_Job_await___redArg(v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v_a_2551_; lean_object* v___x_2552_; size_t v___x_2553_; size_t v___x_2554_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
v_a_2551_ = lean_ctor_get(v___x_2549_, 1);
lean_inc(v_a_2551_);
lean_dec_ref(v___x_2549_);
v___x_2552_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_b_2528_, v_a_2550_);
lean_dec(v_a_2550_);
v___x_2553_ = ((size_t)1ULL);
v___x_2554_ = lean_usize_add(v_i_2526_, v___x_2553_);
v_i_2526_ = v___x_2554_;
v_b_2528_ = v___x_2552_;
v___y_2534_ = v_a_2551_;
goto _start;
}
else
{
lean_object* v_a_2556_; lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v_b_2528_);
v_a_2556_ = lean_ctor_get(v___x_2549_, 0);
v_a_2557_ = lean_ctor_get(v___x_2549_, 1);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2549_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_inc(v_a_2556_);
lean_dec(v___x_2549_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2556_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v_b_2528_);
v_a_2565_ = lean_ctor_get(v___x_2546_, 0);
v_a_2566_ = lean_ctor_get(v___x_2546_, 1);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2546_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_inc(v_a_2565_);
lean_dec(v___x_2546_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2565_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
else
{
lean_object* v___x_2574_; 
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_b_2528_);
lean_ctor_set(v___x_2574_, 1, v___y_2534_);
return v___x_2574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object* v_as_2575_, lean_object* v_i_2576_, lean_object* v_stop_2577_, lean_object* v_b_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
size_t v_i_boxed_2586_; size_t v_stop_boxed_2587_; lean_object* v_res_2588_; 
v_i_boxed_2586_ = lean_unbox_usize(v_i_2576_);
lean_dec(v_i_2576_);
v_stop_boxed_2587_ = lean_unbox_usize(v_stop_2577_);
lean_dec(v_stop_2577_);
v_res_2588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_2575_, v_i_boxed_2586_, v_stop_boxed_2587_, v_b_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec_ref(v_as_2575_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object* v_as_2589_, size_t v_i_2590_, size_t v_stop_2591_, lean_object* v_b_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
uint8_t v___x_2600_; 
v___x_2600_ = lean_usize_dec_eq(v_i_2590_, v_stop_2591_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; lean_object* v_pkg_2602_; lean_object* v_name_2603_; lean_object* v_keyName_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2601_ = lean_array_uget_borrowed(v_as_2589_, v_i_2590_);
v_pkg_2602_ = lean_ctor_get(v___x_2601_, 0);
v_name_2603_ = lean_ctor_get(v___x_2601_, 1);
v_keyName_2604_ = lean_ctor_get(v_pkg_2602_, 2);
v___x_2605_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_2603_);
lean_inc(v_keyName_2604_);
v___x_2606_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2606_, 0, v_keyName_2604_);
lean_ctor_set(v___x_2606_, 1, v_name_2603_);
v___x_2607_ = l_Lake_ExternLib_keyword;
lean_inc(v___x_2601_);
v___x_2608_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
lean_ctor_set(v___x_2608_, 2, v___x_2601_);
lean_ctor_set(v___x_2608_, 3, v___x_2605_);
lean_inc_ref(v___y_2593_);
lean_inc_ref(v___y_2597_);
lean_inc(v___y_2596_);
lean_inc(v___y_2595_);
lean_inc(v___y_2594_);
v___x_2609_ = lean_apply_7(v___y_2593_, v___x_2608_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, lean_box(0));
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v_a_2611_; lean_object* v___x_2612_; size_t v___x_2613_; size_t v___x_2614_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
v_a_2611_ = lean_ctor_get(v___x_2609_, 1);
lean_inc(v_a_2611_);
lean_dec_ref(v___x_2609_);
v___x_2612_ = lean_array_push(v_b_2592_, v_a_2610_);
v___x_2613_ = ((size_t)1ULL);
v___x_2614_ = lean_usize_add(v_i_2590_, v___x_2613_);
v_i_2590_ = v___x_2614_;
v_b_2592_ = v___x_2612_;
v___y_2598_ = v_a_2611_;
goto _start;
}
else
{
lean_object* v_a_2616_; lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec_ref(v_b_2592_);
v_a_2616_ = lean_ctor_get(v___x_2609_, 0);
v_a_2617_ = lean_ctor_get(v___x_2609_, 1);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2609_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_inc(v_a_2616_);
lean_dec(v___x_2609_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2616_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v___x_2625_; 
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v_b_2592_);
lean_ctor_set(v___x_2625_, 1, v___y_2598_);
return v___x_2625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object* v_as_2626_, lean_object* v_i_2627_, lean_object* v_stop_2628_, lean_object* v_b_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
size_t v_i_boxed_2637_; size_t v_stop_boxed_2638_; lean_object* v_res_2639_; 
v_i_boxed_2637_ = lean_unbox_usize(v_i_2627_);
lean_dec(v_i_2627_);
v_stop_boxed_2638_ = lean_unbox_usize(v_stop_2628_);
lean_dec(v_stop_2628_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_2626_, v_i_boxed_2637_, v_stop_boxed_2638_, v_b_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec_ref(v_as_2626_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object* v_as_2640_, size_t v_i_2641_, size_t v_stop_2642_, lean_object* v_b_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_a_2652_; lean_object* v_a_2653_; uint8_t v___x_2657_; 
v___x_2657_ = lean_usize_dec_eq(v_i_2641_, v_stop_2642_);
if (v___x_2657_ == 0)
{
lean_object* v_fst_2658_; lean_object* v_snd_2659_; lean_object* v___x_2660_; lean_object* v_lib_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2698_; 
v_fst_2658_ = lean_ctor_get(v_b_2643_, 0);
v_snd_2659_ = lean_ctor_get(v_b_2643_, 1);
v___x_2660_ = lean_array_uget(v_as_2640_, v_i_2641_);
v_lib_2661_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v___x_2660_, 1);
lean_dec(v_unused_2699_);
v___x_2663_ = v___x_2660_;
v_isShared_2664_ = v_isSharedCheck_2698_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_lib_2661_);
lean_dec(v___x_2660_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2698_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v_pkg_2665_; lean_object* v_name_2666_; uint8_t v___x_2667_; 
v_pkg_2665_ = lean_ctor_get(v_lib_2661_, 0);
v_name_2666_ = lean_ctor_get(v_lib_2661_, 1);
lean_inc(v_name_2666_);
v___x_2667_ = l_Lean_NameSet_contains(v_fst_2658_, v_name_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2695_; 
lean_inc(v_snd_2659_);
lean_inc(v_fst_2658_);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_b_2643_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; lean_object* v_unused_2697_; 
v_unused_2696_ = lean_ctor_get(v_b_2643_, 1);
lean_dec(v_unused_2696_);
v_unused_2697_ = lean_ctor_get(v_b_2643_, 0);
lean_dec(v_unused_2697_);
v___x_2669_ = v_b_2643_;
v_isShared_2670_ = v_isSharedCheck_2695_;
goto v_resetjp_2668_;
}
else
{
lean_dec(v_b_2643_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2695_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v_keyName_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
v_keyName_2671_ = lean_ctor_get(v_pkg_2665_, 2);
v___x_2672_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_2666_);
lean_inc(v_keyName_2671_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set_tag(v___x_2663_, 3);
lean_ctor_set(v___x_2663_, 1, v_name_2666_);
lean_ctor_set(v___x_2663_, 0, v_keyName_2671_);
v___x_2674_ = v___x_2663_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_keyName_2671_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_name_2666_);
v___x_2674_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2675_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2676_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
lean_ctor_set(v___x_2676_, 2, v_lib_2661_);
lean_ctor_set(v___x_2676_, 3, v___x_2672_);
lean_inc_ref(v___y_2644_);
lean_inc_ref(v___y_2648_);
lean_inc(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc(v___y_2645_);
v___x_2677_ = lean_apply_7(v___y_2644_, v___x_2676_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, lean_box(0));
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v_a_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
v_a_2679_ = lean_ctor_get(v___x_2677_, 1);
lean_inc(v_a_2679_);
lean_dec_ref(v___x_2677_);
v___x_2680_ = lean_array_push(v_snd_2659_, v_a_2678_);
v___x_2681_ = l_Lean_NameSet_insert(v_fst_2658_, v_name_2666_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 1, v___x_2680_);
lean_ctor_set(v___x_2669_, 0, v___x_2681_);
v___x_2683_ = v___x_2669_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v___x_2680_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
v_a_2652_ = v___x_2683_;
v_a_2653_ = v_a_2679_;
goto v___jp_2651_;
}
}
else
{
lean_object* v_a_2685_; lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_del_object(v___x_2669_);
lean_dec(v_name_2666_);
lean_dec(v_snd_2659_);
lean_dec(v_fst_2658_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
v_a_2685_ = lean_ctor_get(v___x_2677_, 0);
v_a_2686_ = lean_ctor_get(v___x_2677_, 1);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2677_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_inc(v_a_2685_);
lean_dec(v___x_2677_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2685_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
}
else
{
lean_dec(v_name_2666_);
lean_del_object(v___x_2663_);
lean_dec_ref(v_lib_2661_);
v_a_2652_ = v_b_2643_;
v_a_2653_ = v___y_2649_;
goto v___jp_2651_;
}
}
}
else
{
lean_object* v___x_2700_; 
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v_b_2643_);
lean_ctor_set(v___x_2700_, 1, v___y_2649_);
return v___x_2700_;
}
v___jp_2651_:
{
size_t v___x_2654_; size_t v___x_2655_; 
v___x_2654_ = ((size_t)1ULL);
v___x_2655_ = lean_usize_add(v_i_2641_, v___x_2654_);
v_i_2641_ = v___x_2655_;
v_b_2643_ = v_a_2652_;
v___y_2649_ = v_a_2653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object* v_as_2701_, lean_object* v_i_2702_, lean_object* v_stop_2703_, lean_object* v_b_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
size_t v_i_boxed_2712_; size_t v_stop_boxed_2713_; lean_object* v_res_2714_; 
v_i_boxed_2712_ = lean_unbox_usize(v_i_2702_);
lean_dec(v_i_2702_);
v_stop_boxed_2713_ = lean_unbox_usize(v_stop_2703_);
lean_dec(v_stop_2703_);
v_res_2714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_2701_, v_i_boxed_2712_, v_stop_boxed_2713_, v_b_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec_ref(v_as_2701_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object* v___x_2715_, lean_object* v_as_2716_, size_t v_i_2717_, size_t v_stop_2718_, lean_object* v_b_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
uint8_t v___x_2727_; 
v___x_2727_ = lean_usize_dec_eq(v_i_2717_, v_stop_2718_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = lean_array_uget_borrowed(v_as_2716_, v_i_2717_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
lean_inc(v___x_2728_);
lean_inc_ref(v___x_2715_);
v___x_2729_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v___x_2715_, v___x_2728_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v_a_2731_; lean_object* v___x_2732_; size_t v___x_2733_; size_t v___x_2734_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
v_a_2731_ = lean_ctor_get(v___x_2729_, 1);
lean_inc(v_a_2731_);
lean_dec_ref(v___x_2729_);
v___x_2732_ = lean_array_push(v_b_2719_, v_a_2730_);
v___x_2733_ = ((size_t)1ULL);
v___x_2734_ = lean_usize_add(v_i_2717_, v___x_2733_);
v_i_2717_ = v___x_2734_;
v_b_2719_ = v___x_2732_;
v___y_2725_ = v_a_2731_;
goto _start;
}
else
{
lean_object* v_a_2736_; lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec_ref(v_b_2719_);
lean_dec_ref(v___x_2715_);
v_a_2736_ = lean_ctor_get(v___x_2729_, 0);
v_a_2737_ = lean_ctor_get(v___x_2729_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2729_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_inc(v_a_2736_);
lean_dec(v___x_2729_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2736_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
else
{
lean_object* v___x_2745_; 
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec_ref(v___x_2715_);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v_b_2719_);
lean_ctor_set(v___x_2745_, 1, v___y_2725_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* v___x_2746_, lean_object* v_as_2747_, lean_object* v_i_2748_, lean_object* v_stop_2749_, lean_object* v_b_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
size_t v_i_boxed_2758_; size_t v_stop_boxed_2759_; lean_object* v_res_2760_; 
v_i_boxed_2758_ = lean_unbox_usize(v_i_2748_);
lean_dec(v_i_2748_);
v_stop_boxed_2759_ = lean_unbox_usize(v_stop_2749_);
lean_dec(v_stop_2749_);
v_res_2760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_2746_, v_as_2747_, v_i_boxed_2758_, v_stop_boxed_2759_, v_b_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec_ref(v_as_2747_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object* v___x_2761_, lean_object* v_as_2762_, size_t v_i_2763_, size_t v_stop_2764_, lean_object* v_b_2765_){
_start:
{
lean_object* v___y_2767_; uint8_t v___x_2771_; 
v___x_2771_ = lean_usize_dec_eq(v_i_2763_, v_stop_2764_);
if (v___x_2771_ == 0)
{
lean_object* v_toConfigDecl_2772_; lean_object* v_name_2773_; lean_object* v_kind_2774_; lean_object* v_config_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v_toConfigDecl_2772_ = lean_array_uget_borrowed(v_as_2762_, v_i_2763_);
v_name_2773_ = lean_ctor_get(v_toConfigDecl_2772_, 1);
v_kind_2774_ = lean_ctor_get(v_toConfigDecl_2772_, 2);
v_config_2775_ = lean_ctor_get(v_toConfigDecl_2772_, 3);
v___x_2776_ = l_Lake_ExternLib_keyword;
v___x_2777_ = lean_name_eq(v_kind_2774_, v___x_2776_);
if (v___x_2777_ == 0)
{
v___y_2767_ = v_b_2765_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
lean_inc(v_config_2775_);
lean_inc(v_name_2773_);
lean_inc_ref(v___x_2761_);
v___x_2778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2761_);
lean_ctor_set(v___x_2778_, 1, v_name_2773_);
lean_ctor_set(v___x_2778_, 2, v_config_2775_);
v___x_2779_ = lean_array_push(v_b_2765_, v___x_2778_);
v___y_2767_ = v___x_2779_;
goto v___jp_2766_;
}
}
else
{
lean_dec_ref(v___x_2761_);
return v_b_2765_;
}
v___jp_2766_:
{
size_t v___x_2768_; size_t v___x_2769_; 
v___x_2768_ = ((size_t)1ULL);
v___x_2769_ = lean_usize_add(v_i_2763_, v___x_2768_);
v_i_2763_ = v___x_2769_;
v_b_2765_ = v___y_2767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object* v___x_2780_, lean_object* v_as_2781_, lean_object* v_i_2782_, lean_object* v_stop_2783_, lean_object* v_b_2784_){
_start:
{
size_t v_i_boxed_2785_; size_t v_stop_boxed_2786_; lean_object* v_res_2787_; 
v_i_boxed_2785_ = lean_unbox_usize(v_i_2782_);
lean_dec(v_i_2782_);
v_stop_boxed_2786_ = lean_unbox_usize(v_stop_2783_);
lean_dec(v_stop_2783_);
v_res_2787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_2780_, v_as_2781_, v_i_boxed_2785_, v_stop_boxed_2786_, v_b_2784_);
lean_dec_ref(v_as_2781_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(lean_object* v_as_2788_, size_t v_i_2789_, size_t v_stop_2790_, lean_object* v_b_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
uint8_t v___x_2799_; 
v___x_2799_ = lean_usize_dec_eq(v_i_2789_, v_stop_2790_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; lean_object* v_lib_2801_; lean_object* v_config_2802_; lean_object* v_nativeFacets_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; size_t v_sz_2807_; size_t v___x_2808_; lean_object* v___x_2809_; 
v___x_2800_ = lean_array_uget_borrowed(v_as_2788_, v_i_2789_);
v_lib_2801_ = lean_ctor_get(v___x_2800_, 0);
v_config_2802_ = lean_ctor_get(v_lib_2801_, 2);
v_nativeFacets_2803_ = lean_ctor_get(v_config_2802_, 8);
v___x_2804_ = 1;
v___x_2805_ = lean_box(v___x_2804_);
lean_inc_ref(v_nativeFacets_2803_);
v___x_2806_ = lean_apply_1(v_nativeFacets_2803_, v___x_2805_);
v_sz_2807_ = lean_array_size(v___x_2806_);
v___x_2808_ = ((size_t)0ULL);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
lean_inc(v___y_2793_);
lean_inc_ref(v___y_2792_);
lean_inc(v___x_2800_);
v___x_2809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2800_, v_sz_2807_, v___x_2808_, v___x_2806_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v_a_2811_; lean_object* v___x_2812_; size_t v___x_2813_; size_t v___x_2814_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
v_a_2811_ = lean_ctor_get(v___x_2809_, 1);
lean_inc(v_a_2811_);
lean_dec_ref(v___x_2809_);
v___x_2812_ = l_Array_append___redArg(v_b_2791_, v_a_2810_);
lean_dec(v_a_2810_);
v___x_2813_ = ((size_t)1ULL);
v___x_2814_ = lean_usize_add(v_i_2789_, v___x_2813_);
v_i_2789_ = v___x_2814_;
v_b_2791_ = v___x_2812_;
v___y_2797_ = v_a_2811_;
goto _start;
}
else
{
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec_ref(v_b_2791_);
return v___x_2809_;
}
}
else
{
lean_object* v___x_2816_; 
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
v___x_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2816_, 0, v_b_2791_);
lean_ctor_set(v___x_2816_, 1, v___y_2797_);
return v___x_2816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object* v_as_2817_, lean_object* v_i_2818_, lean_object* v_stop_2819_, lean_object* v_b_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
size_t v_i_boxed_2828_; size_t v_stop_boxed_2829_; lean_object* v_res_2830_; 
v_i_boxed_2828_ = lean_unbox_usize(v_i_2818_);
lean_dec(v_i_2818_);
v_stop_boxed_2829_ = lean_unbox_usize(v_stop_2819_);
lean_dec(v_stop_2819_);
v_res_2830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_2817_, v_i_boxed_2828_, v_stop_boxed_2829_, v_b_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec_ref(v_as_2817_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object* v___x_2831_, lean_object* v___x_2832_, lean_object* v_self_2833_, lean_object* v_dir_2834_, lean_object* v_targetDecls_2835_, lean_object* v_pkg_2836_, lean_object* v_name_2837_, lean_object* v_config_2838_, lean_object* v_config_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v_a_2855_; lean_object* v_a_2856_; lean_object* v_a_2873_; lean_object* v_a_2874_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v_a_2919_; lean_object* v_a_2920_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v_snd_2956_; lean_object* v_a_2957_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v_a_2996_; lean_object* v_a_2997_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___x_3035_; 
lean_inc_ref(v___y_2840_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___x_2832_);
v___x_3035_ = lean_apply_7(v___y_2840_, v___x_2831_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, lean_box(0));
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v_a_3037_; lean_object* v___x_3038_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
v_a_3037_ = lean_ctor_get(v___x_3035_, 1);
lean_inc(v_a_3037_);
lean_dec_ref(v___x_3035_);
v___x_3038_ = l_Lake_Job_await___redArg(v_a_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v_a_3040_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v_a_3051_; lean_object* v_a_3052_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v_a_3086_; lean_object* v_a_3087_; lean_object* v___y_3112_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
v_a_3040_ = lean_ctor_get(v___x_3038_, 1);
lean_inc(v_a_3040_);
lean_dec_ref(v___x_3038_);
v___x_3124_ = lean_unsigned_to_nat(0u);
v___x_3125_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_3126_ = lean_array_get_size(v_a_3039_);
v___x_3127_ = lean_nat_dec_lt(v___x_3124_, v___x_3126_);
if (v___x_3127_ == 0)
{
v_a_3086_ = v___x_3125_;
v_a_3087_ = v_a_3040_;
goto v___jp_3085_;
}
else
{
uint8_t v___x_3128_; 
v___x_3128_ = lean_nat_dec_le(v___x_3126_, v___x_3126_);
if (v___x_3128_ == 0)
{
if (v___x_3127_ == 0)
{
v_a_3086_ = v___x_3125_;
v_a_3087_ = v_a_3040_;
goto v___jp_3085_;
}
else
{
size_t v___x_3129_; size_t v___x_3130_; lean_object* v___x_3131_; 
v___x_3129_ = ((size_t)0ULL);
v___x_3130_ = lean_usize_of_nat(v___x_3126_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___x_2832_);
lean_inc_ref(v___y_2840_);
v___x_3131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3039_, v___x_3129_, v___x_3130_, v___x_3125_, v___y_2840_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v_a_3040_);
v___y_3112_ = v___x_3131_;
goto v___jp_3111_;
}
}
else
{
size_t v___x_3132_; size_t v___x_3133_; lean_object* v___x_3134_; 
v___x_3132_ = ((size_t)0ULL);
v___x_3133_ = lean_usize_of_nat(v___x_3126_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___x_2832_);
lean_inc_ref(v___y_2840_);
v___x_3134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3039_, v___x_3132_, v___x_3133_, v___x_3125_, v___y_2840_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v_a_3040_);
v___y_3112_ = v___x_3134_;
goto v___jp_3111_;
}
}
v___jp_3041_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3053_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_3054_ = lean_array_get_size(v_a_3039_);
v___x_3055_ = lean_nat_dec_lt(v___y_3043_, v___x_3054_);
if (v___x_3055_ == 0)
{
lean_dec(v_a_3039_);
v___y_2986_ = v_a_3051_;
v___y_2987_ = v___y_3042_;
v___y_2988_ = v___y_3043_;
v___y_2989_ = v___y_3044_;
v___y_2990_ = v___y_3045_;
v___y_2991_ = v___y_3046_;
v___y_2992_ = v___y_3047_;
v___y_2993_ = v___y_3048_;
v___y_2994_ = v___y_3049_;
v___y_2995_ = v___y_3050_;
v_a_2996_ = v___x_3053_;
v_a_2997_ = v_a_3052_;
goto v___jp_2985_;
}
else
{
uint8_t v___x_3056_; 
v___x_3056_ = lean_nat_dec_le(v___x_3054_, v___x_3054_);
if (v___x_3056_ == 0)
{
if (v___x_3055_ == 0)
{
lean_dec(v_a_3039_);
v___y_2986_ = v_a_3051_;
v___y_2987_ = v___y_3042_;
v___y_2988_ = v___y_3043_;
v___y_2989_ = v___y_3044_;
v___y_2990_ = v___y_3045_;
v___y_2991_ = v___y_3046_;
v___y_2992_ = v___y_3047_;
v___y_2993_ = v___y_3048_;
v___y_2994_ = v___y_3049_;
v___y_2995_ = v___y_3050_;
v_a_2996_ = v___x_3053_;
v_a_2997_ = v_a_3052_;
goto v___jp_2985_;
}
else
{
size_t v___x_3057_; size_t v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = ((size_t)0ULL);
v___x_3058_ = lean_usize_of_nat(v___x_3054_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___x_2832_);
lean_inc_ref(v___y_2840_);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3039_, v___x_3057_, v___x_3058_, v___x_3053_, v___y_2840_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v_a_3052_);
lean_dec(v_a_3039_);
v___y_3020_ = v___y_3042_;
v___y_3021_ = v_a_3051_;
v___y_3022_ = v___y_3043_;
v___y_3023_ = v___y_3045_;
v___y_3024_ = v___y_3044_;
v___y_3025_ = v___y_3047_;
v___y_3026_ = v___y_3046_;
v___y_3027_ = v___y_3049_;
v___y_3028_ = v___y_3048_;
v___y_3029_ = v___y_3050_;
v___y_3030_ = v___x_3059_;
goto v___jp_3019_;
}
}
else
{
size_t v___x_3060_; size_t v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = ((size_t)0ULL);
v___x_3061_ = lean_usize_of_nat(v___x_3054_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___x_2832_);
lean_inc_ref(v___y_2840_);
v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3039_, v___x_3060_, v___x_3061_, v___x_3053_, v___y_2840_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v_a_3052_);
lean_dec(v_a_3039_);
v___y_3020_ = v___y_3042_;
v___y_3021_ = v_a_3051_;
v___y_3022_ = v___y_3043_;
v___y_3023_ = v___y_3045_;
v___y_3024_ = v___y_3044_;
v___y_3025_ = v___y_3047_;
v___y_3026_ = v___y_3046_;
v___y_3027_ = v___y_3049_;
v___y_3028_ = v___y_3048_;
v___y_3029_ = v___y_3050_;
v___y_3030_ = v___x_3062_;
goto v___jp_3019_;
}
}
}
v___jp_3063_:
{
if (lean_obj_tag(v___y_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v_a_3075_; 
v_a_3074_ = lean_ctor_get(v___y_3073_, 0);
lean_inc(v_a_3074_);
v_a_3075_ = lean_ctor_get(v___y_3073_, 1);
lean_inc(v_a_3075_);
lean_dec_ref(v___y_3073_);
v___y_3042_ = v___y_3064_;
v___y_3043_ = v___y_3065_;
v___y_3044_ = v___y_3067_;
v___y_3045_ = v___y_3066_;
v___y_3046_ = v___y_3069_;
v___y_3047_ = v___y_3068_;
v___y_3048_ = v___y_3071_;
v___y_3049_ = v___y_3070_;
v___y_3050_ = v___y_3072_;
v_a_3051_ = v_a_3074_;
v_a_3052_ = v_a_3075_;
goto v___jp_3041_;
}
else
{
lean_object* v_a_3076_; lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec_ref(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec_ref(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec_ref(v___y_3064_);
lean_dec(v_a_3039_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2840_);
lean_dec(v_name_2837_);
lean_dec_ref(v_pkg_2836_);
lean_dec_ref(v_dir_2834_);
lean_dec_ref(v_self_2833_);
lean_dec(v___x_2832_);
v_a_3076_ = lean_ctor_get(v___y_3073_, 0);
v_a_3077_ = lean_ctor_get(v___y_3073_, 1);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___y_3073_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___y_3073_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_inc(v_a_3076_);
lean_dec(v___y_3073_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3076_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
v___jp_3085_:
{
lean_object* v_toLeanConfig_3088_; lean_object* v_toLeanConfig_3089_; lean_object* v_buildDir_3090_; lean_object* v_nativeLibDir_3091_; lean_object* v_moreLinkObjs_3092_; lean_object* v_moreLinkLibs_3093_; lean_object* v_moreLinkArgs_3094_; lean_object* v_weakLinkArgs_3095_; lean_object* v_moreLinkObjs_3096_; lean_object* v_moreLinkLibs_3097_; lean_object* v_moreLinkArgs_3098_; lean_object* v_weakLinkArgs_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v_toLeanConfig_3088_ = lean_ctor_get(v_config_2838_, 1);
lean_inc_ref(v_toLeanConfig_3088_);
v_toLeanConfig_3089_ = lean_ctor_get(v_config_2839_, 0);
v_buildDir_3090_ = lean_ctor_get(v_config_2838_, 5);
lean_inc_ref(v_buildDir_3090_);
v_nativeLibDir_3091_ = lean_ctor_get(v_config_2838_, 7);
lean_inc_ref(v_nativeLibDir_3091_);
lean_dec_ref(v_config_2838_);
v_moreLinkObjs_3092_ = lean_ctor_get(v_toLeanConfig_3088_, 6);
lean_inc_ref(v_moreLinkObjs_3092_);
v_moreLinkLibs_3093_ = lean_ctor_get(v_toLeanConfig_3088_, 7);
lean_inc_ref(v_moreLinkLibs_3093_);
v_moreLinkArgs_3094_ = lean_ctor_get(v_toLeanConfig_3088_, 8);
lean_inc_ref(v_moreLinkArgs_3094_);
v_weakLinkArgs_3095_ = lean_ctor_get(v_toLeanConfig_3088_, 9);
lean_inc_ref(v_weakLinkArgs_3095_);
lean_dec_ref(v_toLeanConfig_3088_);
v_moreLinkObjs_3096_ = lean_ctor_get(v_toLeanConfig_3089_, 6);
v_moreLinkLibs_3097_ = lean_ctor_get(v_toLeanConfig_3089_, 7);
v_moreLinkArgs_3098_ = lean_ctor_get(v_toLeanConfig_3089_, 8);
v_weakLinkArgs_3099_ = lean_ctor_get(v_toLeanConfig_3089_, 9);
v___x_3100_ = l_Array_append___redArg(v_moreLinkObjs_3092_, v_moreLinkObjs_3096_);
v___x_3101_ = lean_unsigned_to_nat(0u);
v___x_3102_ = lean_array_get_size(v___x_3100_);
v___x_3103_ = lean_nat_dec_lt(v___x_3101_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_dec_ref(v___x_3100_);
v___y_3042_ = v_weakLinkArgs_3095_;
v___y_3043_ = v___x_3101_;
v___y_3044_ = v_moreLinkLibs_3093_;
v___y_3045_ = v_moreLinkLibs_3097_;
v___y_3046_ = v_moreLinkArgs_3098_;
v___y_3047_ = v_buildDir_3090_;
v___y_3048_ = v_moreLinkArgs_3094_;
v___y_3049_ = v_weakLinkArgs_3099_;
v___y_3050_ = v_nativeLibDir_3091_;
v_a_3051_ = v_a_3086_;
v_a_3052_ = v_a_3087_;
goto v___jp_3041_;
}
else
{
uint8_t v___x_3104_; 
v___x_3104_ = lean_nat_dec_le(v___x_3102_, v___x_3102_);
if (v___x_3104_ == 0)
{
if (v___x_3103_ == 0)
{
lean_dec_ref(v___x_3100_);
v___y_3042_ = v_weakLinkArgs_3095_;
v___y_3043_ = v___x_3101_;
v___y_3044_ = v_moreLinkLibs_3093_;
v___y_3045_ = v_moreLinkLibs_3097_;
v___y_3046_ = v_moreLinkArgs_3098_;
v___y_3047_ = v_buildDir_3090_;
v___y_3048_ = v_moreLinkArgs_3094_;
v___y_3049_ = v_weakLinkArgs_3099_;
v___y_3050_ = v_nativeLibDir_3091_;
v_a_3051_ = v_a_3086_;
v_a_3052_ = v_a_3087_;
goto v___jp_3041_;
}
else
{
size_t v___x_3105_; size_t v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = ((size_t)0ULL);
v___x_3106_ = lean_usize_of_nat(v___x_3102_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___x_2832_);
lean_inc_ref(v___y_2840_);
lean_inc_ref(v_pkg_2836_);
v___x_3107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2836_, v___x_3100_, v___x_3105_, v___x_3106_, v_a_3086_, v___y_2840_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v_a_3087_);
lean_dec_ref(v___x_3100_);
v___y_3064_ = v_weakLinkArgs_3095_;
v___y_3065_ = v___x_3101_;
v___y_3066_ = v_moreLinkLibs_3097_;
v___y_3067_ = v_moreLinkLibs_3093_;
v___y_3068_ = v_buildDir_3090_;
v___y_3069_ = v_moreLinkArgs_3098_;
v___y_3070_ = v_weakLinkArgs_3099_;
v___y_3071_ = v_moreLinkArgs_3094_;
v___y_3072_ = v_nativeLibDir_3091_;
v___y_3073_ = v___x_3107_;
goto v___jp_3063_;
}
}
else
{
size_t v___x_3108_; size_t v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = ((size_t)0ULL);
v___x_3109_ = lean_usize_of_nat(v___x_3102_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___x_2832_);
lean_inc_ref(v___y_2840_);
lean_inc_ref(v_pkg_2836_);
v___x_3110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2836_, v___x_3100_, v___x_3108_, v___x_3109_, v_a_3086_, v___y_2840_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v_a_3087_);
lean_dec_ref(v___x_3100_);
v___y_3064_ = v_weakLinkArgs_3095_;
v___y_3065_ = v___x_3101_;
v___y_3066_ = v_moreLinkLibs_3097_;
v___y_3067_ = v_moreLinkLibs_3093_;
v___y_3068_ = v_buildDir_3090_;
v___y_3069_ = v_moreLinkArgs_3098_;
v___y_3070_ = v_weakLinkArgs_3099_;
v___y_3071_ = v_moreLinkArgs_3094_;
v___y_3072_ = v_nativeLibDir_3091_;
v___y_3073_ = v___x_3110_;
goto v___jp_3063_;
}
}
}
v___jp_3111_:
{
if (lean_obj_tag(v___y_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v_a_3114_; 
v_a_3113_ = lean_ctor_get(v___y_3112_, 0);
lean_inc(v_a_3113_);
v_a_3114_ = lean_ctor_get(v___y_3112_, 1);
lean_inc(v_a_3114_);
lean_dec_ref(v___y_3112_);
v_a_3086_ = v_a_3113_;
v_a_3087_ = v_a_3114_;
goto v___jp_3085_;
}
else
{
lean_object* v_a_3115_; lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec(v_a_3039_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v_config_2838_);
lean_dec(v_name_2837_);
lean_dec_ref(v_pkg_2836_);
lean_dec_ref(v_dir_2834_);
lean_dec_ref(v_self_2833_);
lean_dec(v___x_2832_);
v_a_3115_ = lean_ctor_get(v___y_3112_, 0);
v_a_3116_ = lean_ctor_get(v___y_3112_, 1);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___y_3112_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___y_3112_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_inc(v_a_3115_);
lean_dec(v___y_3112_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3115_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v_config_2838_);
lean_dec(v_name_2837_);
lean_dec_ref(v_pkg_2836_);
lean_dec_ref(v_dir_2834_);
lean_dec_ref(v_self_2833_);
lean_dec(v___x_2832_);
v_a_3135_ = lean_ctor_get(v___x_3038_, 0);
v_a_3136_ = lean_ctor_get(v___x_3038_, 1);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3038_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_inc(v_a_3135_);
lean_dec(v___x_3038_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3135_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v_config_2838_);
lean_dec(v_name_2837_);
lean_dec_ref(v_pkg_2836_);
lean_dec_ref(v_dir_2834_);
lean_dec_ref(v_self_2833_);
lean_dec(v___x_2832_);
v_a_3144_ = lean_ctor_get(v___x_3035_, 0);
v_a_3145_ = lean_ctor_get(v___x_3035_, 1);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3035_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_inc(v_a_3144_);
lean_dec(v___x_3035_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3144_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
v___jp_2847_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; uint8_t v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_inc_ref(v_self_2833_);
v___x_2857_ = l_Lake_LeanLib_libName(v_self_2833_);
v___x_2858_ = l_System_FilePath_normalize(v___y_2851_);
v___x_2859_ = l_Lake_joinRelative(v_dir_2834_, v___x_2858_);
v___x_2860_ = l_System_FilePath_normalize(v___y_2854_);
v___x_2861_ = l_Lake_joinRelative(v___x_2859_, v___x_2860_);
v___x_2862_ = 0;
v___x_2863_ = l_Lake_nameToSharedLib(v___x_2857_, v___x_2862_);
v___x_2864_ = l_Lake_joinRelative(v___x_2861_, v___x_2863_);
v___x_2865_ = l_Array_append___redArg(v___y_2849_, v___y_2853_);
v___x_2866_ = l_Array_append___redArg(v___y_2852_, v___y_2850_);
v___x_2867_ = l_Lake_LeanLib_isPlugin(v_self_2833_);
v___x_2868_ = l_System_Platform_isWindows;
v___x_2869_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2870_ = l_Lake_buildLeanSharedLib(v___x_2857_, v___x_2864_, v___y_2848_, v_a_2855_, v___x_2865_, v___x_2866_, v___x_2867_, v___x_2868_, v___y_2840_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v___x_2869_);
lean_dec_ref(v___y_2848_);
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
lean_ctor_set(v___x_2871_, 1, v_a_2856_);
return v___x_2871_;
}
v___jp_2872_:
{
lean_object* v___x_2875_; 
v___x_2875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2875_, 0, v_a_2873_);
lean_ctor_set(v___x_2875_, 1, v_a_2874_);
return v___x_2875_;
}
v___jp_2876_:
{
if (lean_obj_tag(v___y_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v_a_2886_; 
v_a_2885_ = lean_ctor_get(v___y_2884_, 0);
lean_inc(v_a_2885_);
v_a_2886_ = lean_ctor_get(v___y_2884_, 1);
lean_inc(v_a_2886_);
lean_dec_ref(v___y_2884_);
v___y_2848_ = v___y_2878_;
v___y_2849_ = v___y_2877_;
v___y_2850_ = v___y_2880_;
v___y_2851_ = v___y_2879_;
v___y_2852_ = v___y_2882_;
v___y_2853_ = v___y_2881_;
v___y_2854_ = v___y_2883_;
v_a_2855_ = v_a_2885_;
v_a_2856_ = v_a_2886_;
goto v___jp_2847_;
}
else
{
lean_object* v_a_2887_; lean_object* v_a_2888_; 
lean_dec_ref(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v_dir_2834_);
lean_dec_ref(v_self_2833_);
lean_dec(v___x_2832_);
v_a_2887_ = lean_ctor_get(v___y_2884_, 0);
lean_inc(v_a_2887_);
v_a_2888_ = lean_ctor_get(v___y_2884_, 1);
lean_inc(v_a_2888_);
lean_dec_ref(v___y_2884_);
v_a_2873_ = v_a_2887_;
v_a_2874_ = v_a_2888_;
goto v___jp_2872_;
}
}
v___jp_2889_:
{
lean_object* v___x_2901_; uint8_t v___x_2902_; 
v___x_2901_ = lean_array_get_size(v___y_2900_);
v___x_2902_ = lean_nat_dec_lt(v___y_2892_, v___x_2901_);
if (v___x_2902_ == 0)
{
lean_dec_ref(v___y_2900_);
v___y_2848_ = v___y_2891_;
v___y_2849_ = v___y_2890_;
v___y_2850_ = v___y_2894_;
v___y_2851_ = v___y_2893_;
v___y_2852_ = v___y_2897_;
v___y_2853_ = v___y_2896_;
v___y_2854_ = v___y_2899_;
v_a_2855_ = v___y_2895_;
v_a_2856_ = v___y_2898_;
goto v___jp_2847_;
}
else
{
uint8_t v___x_2903_; 
v___x_2903_ = lean_nat_dec_le(v___x_2901_, v___x_2901_);
if (v___x_2903_ == 0)
{
if (v___x_2902_ == 0)
{
lean_dec_ref(v___y_2900_);
v___y_2848_ = v___y_2891_;
v___y_2849_ = v___y_2890_;
v___y_2850_ = v___y_2894_;
v___y_2851_ = v___y_2893_;
v___y_2852_ = v___y_2897_;
v___y_2853_ = v___y_2896_;
v___y_2854_ = v___y_2899_;
v_a_2855_ = v___y_2895_;
v_a_2856_ = v___y_2898_;
goto v___jp_2847_;
}
else
{
size_t v___x_2904_; size_t v___x_2905_; lean_object* v___x_2906_; 
v___x_2904_ = ((size_t)0ULL);
v___x_2905_ = lean_usize_of_nat(v___x_2901_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___x_2832_);
lean_inc_ref(v___y_2840_);
v___x_2906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2900_, v___x_2904_, v___x_2905_, v___y_2895_, v___y_2840_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2898_);
lean_dec_ref(v___y_2900_);
v___y_2877_ = v___y_2890_;
v___y_2878_ = v___y_2891_;
v___y_2879_ = v___y_2893_;
v___y_2880_ = v___y_2894_;
v___y_2881_ = v___y_2896_;
v___y_2882_ = v___y_2897_;
v___y_2883_ = v___y_2899_;
v___y_2884_ = v___x_2906_;
goto v___jp_2876_;
}
}
else
{
size_t v___x_2907_; size_t v___x_2908_; lean_object* v___x_2909_; 
v___x_2907_ = ((size_t)0ULL);
v___x_2908_ = lean_usize_of_nat(v___x_2901_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___x_2832_);
lean_inc_ref(v___y_2840_);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2900_, v___x_2907_, v___x_2908_, v___y_2895_, v___y_2840_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2898_);
lean_dec_ref(v___y_2900_);
v___y_2877_ = v___y_2890_;
v___y_2878_ = v___y_2891_;
v___y_2879_ = v___y_2893_;
v___y_2880_ = v___y_2894_;
v___y_2881_ = v___y_2896_;
v___y_2882_ = v___y_2897_;
v___y_2883_ = v___y_2899_;
v___y_2884_ = v___x_2909_;
goto v___jp_2876_;
}
}
}
v___jp_2910_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2921_ = lean_mk_empty_array_with_capacity(v___y_2913_);
v___x_2922_ = lean_array_get_size(v_targetDecls_2835_);
v___x_2923_ = lean_nat_dec_lt(v___y_2913_, v___x_2922_);
if (v___x_2923_ == 0)
{
lean_dec_ref(v_pkg_2836_);
v___y_2890_ = v___y_2912_;
v___y_2891_ = v___y_2911_;
v___y_2892_ = v___y_2913_;
v___y_2893_ = v___y_2915_;
v___y_2894_ = v___y_2914_;
v___y_2895_ = v_a_2919_;
v___y_2896_ = v___y_2917_;
v___y_2897_ = v___y_2916_;
v___y_2898_ = v_a_2920_;
v___y_2899_ = v___y_2918_;
v___y_2900_ = v___x_2921_;
goto v___jp_2889_;
}
else
{
uint8_t v___x_2924_; 
v___x_2924_ = lean_nat_dec_le(v___x_2922_, v___x_2922_);
if (v___x_2924_ == 0)
{
if (v___x_2923_ == 0)
{
lean_dec_ref(v_pkg_2836_);
v___y_2890_ = v___y_2912_;
v___y_2891_ = v___y_2911_;
v___y_2892_ = v___y_2913_;
v___y_2893_ = v___y_2915_;
v___y_2894_ = v___y_2914_;
v___y_2895_ = v_a_2919_;
v___y_2896_ = v___y_2917_;
v___y_2897_ = v___y_2916_;
v___y_2898_ = v_a_2920_;
v___y_2899_ = v___y_2918_;
v___y_2900_ = v___x_2921_;
goto v___jp_2889_;
}
else
{
size_t v___x_2925_; size_t v___x_2926_; lean_object* v___x_2927_; 
v___x_2925_ = ((size_t)0ULL);
v___x_2926_ = lean_usize_of_nat(v___x_2922_);
v___x_2927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2836_, v_targetDecls_2835_, v___x_2925_, v___x_2926_, v___x_2921_);
v___y_2890_ = v___y_2912_;
v___y_2891_ = v___y_2911_;
v___y_2892_ = v___y_2913_;
v___y_2893_ = v___y_2915_;
v___y_2894_ = v___y_2914_;
v___y_2895_ = v_a_2919_;
v___y_2896_ = v___y_2917_;
v___y_2897_ = v___y_2916_;
v___y_2898_ = v_a_2920_;
v___y_2899_ = v___y_2918_;
v___y_2900_ = v___x_2927_;
goto v___jp_2889_;
}
}
else
{
size_t v___x_2928_; size_t v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = ((size_t)0ULL);
v___x_2929_ = lean_usize_of_nat(v___x_2922_);
v___x_2930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2836_, v_targetDecls_2835_, v___x_2928_, v___x_2929_, v___x_2921_);
v___y_2890_ = v___y_2912_;
v___y_2891_ = v___y_2911_;
v___y_2892_ = v___y_2913_;
v___y_2893_ = v___y_2915_;
v___y_2894_ = v___y_2914_;
v___y_2895_ = v_a_2919_;
v___y_2896_ = v___y_2917_;
v___y_2897_ = v___y_2916_;
v___y_2898_ = v_a_2920_;
v___y_2899_ = v___y_2918_;
v___y_2900_ = v___x_2930_;
goto v___jp_2889_;
}
}
}
v___jp_2931_:
{
if (lean_obj_tag(v___y_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v_a_2942_; 
v_a_2941_ = lean_ctor_get(v___y_2940_, 0);
lean_inc(v_a_2941_);
v_a_2942_ = lean_ctor_get(v___y_2940_, 1);
lean_inc(v_a_2942_);
lean_dec_ref(v___y_2940_);
v___y_2911_ = v___y_2933_;
v___y_2912_ = v___y_2932_;
v___y_2913_ = v___y_2934_;
v___y_2914_ = v___y_2936_;
v___y_2915_ = v___y_2935_;
v___y_2916_ = v___y_2938_;
v___y_2917_ = v___y_2937_;
v___y_2918_ = v___y_2939_;
v_a_2919_ = v_a_2941_;
v_a_2920_ = v_a_2942_;
goto v___jp_2910_;
}
else
{
lean_object* v_a_2943_; lean_object* v_a_2944_; 
lean_dec_ref(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v_pkg_2836_);
lean_dec_ref(v_dir_2834_);
lean_dec_ref(v_self_2833_);
lean_dec(v___x_2832_);
v_a_2943_ = lean_ctor_get(v___y_2940_, 0);
lean_inc(v_a_2943_);
v_a_2944_ = lean_ctor_get(v___y_2940_, 1);
lean_inc(v_a_2944_);
lean_dec_ref(v___y_2940_);
v_a_2873_ = v_a_2943_;
v_a_2874_ = v_a_2944_;
goto v___jp_2872_;
}
}
v___jp_2945_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2958_ = l_Array_append___redArg(v___y_2950_, v___y_2949_);
v___x_2959_ = lean_array_get_size(v___x_2958_);
v___x_2960_ = lean_nat_dec_lt(v___y_2948_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_dec_ref(v___x_2958_);
v___y_2911_ = v___y_2947_;
v___y_2912_ = v___y_2946_;
v___y_2913_ = v___y_2948_;
v___y_2914_ = v___y_2952_;
v___y_2915_ = v___y_2951_;
v___y_2916_ = v___y_2954_;
v___y_2917_ = v___y_2953_;
v___y_2918_ = v___y_2955_;
v_a_2919_ = v_snd_2956_;
v_a_2920_ = v_a_2957_;
goto v___jp_2910_;
}
else
{
uint8_t v___x_2961_; 
v___x_2961_ = lean_nat_dec_le(v___x_2959_, v___x_2959_);
if (v___x_2961_ == 0)
{
if (v___x_2960_ == 0)
{
lean_dec_ref(v___x_2958_);
v___y_2911_ = v___y_2947_;
v___y_2912_ = v___y_2946_;
v___y_2913_ = v___y_2948_;
v___y_2914_ = v___y_2952_;
v___y_2915_ = v___y_2951_;
v___y_2916_ = v___y_2954_;
v___y_2917_ = v___y_2953_;
v___y_2918_ = v___y_2955_;
v_a_2919_ = v_snd_2956_;
v_a_2920_ = v_a_2957_;
goto v___jp_2910_;
}
else
{
size_t v___x_2962_; size_t v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = ((size_t)0ULL);
v___x_2963_ = lean_usize_of_nat(v___x_2959_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___x_2832_);
lean_inc_ref(v___y_2840_);
lean_inc_ref(v_pkg_2836_);
v___x_2964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2836_, v___x_2958_, v___x_2962_, v___x_2963_, v_snd_2956_, v___y_2840_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v_a_2957_);
lean_dec_ref(v___x_2958_);
v___y_2932_ = v___y_2946_;
v___y_2933_ = v___y_2947_;
v___y_2934_ = v___y_2948_;
v___y_2935_ = v___y_2951_;
v___y_2936_ = v___y_2952_;
v___y_2937_ = v___y_2953_;
v___y_2938_ = v___y_2954_;
v___y_2939_ = v___y_2955_;
v___y_2940_ = v___x_2964_;
goto v___jp_2931_;
}
}
else
{
size_t v___x_2965_; size_t v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = ((size_t)0ULL);
v___x_2966_ = lean_usize_of_nat(v___x_2959_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___x_2832_);
lean_inc_ref(v___y_2840_);
lean_inc_ref(v_pkg_2836_);
v___x_2967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2836_, v___x_2958_, v___x_2965_, v___x_2966_, v_snd_2956_, v___y_2840_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v_a_2957_);
lean_dec_ref(v___x_2958_);
v___y_2932_ = v___y_2946_;
v___y_2933_ = v___y_2947_;
v___y_2934_ = v___y_2948_;
v___y_2935_ = v___y_2951_;
v___y_2936_ = v___y_2952_;
v___y_2937_ = v___y_2953_;
v___y_2938_ = v___y_2954_;
v___y_2939_ = v___y_2955_;
v___y_2940_ = v___x_2967_;
goto v___jp_2931_;
}
}
}
v___jp_2968_:
{
if (lean_obj_tag(v___y_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v_a_2981_; lean_object* v_snd_2982_; 
v_a_2980_ = lean_ctor_get(v___y_2979_, 0);
lean_inc(v_a_2980_);
v_a_2981_ = lean_ctor_get(v___y_2979_, 1);
lean_inc(v_a_2981_);
lean_dec_ref(v___y_2979_);
v_snd_2982_ = lean_ctor_get(v_a_2980_, 1);
lean_inc(v_snd_2982_);
lean_dec(v_a_2980_);
v___y_2946_ = v___y_2970_;
v___y_2947_ = v___y_2969_;
v___y_2948_ = v___y_2971_;
v___y_2949_ = v___y_2973_;
v___y_2950_ = v___y_2972_;
v___y_2951_ = v___y_2975_;
v___y_2952_ = v___y_2974_;
v___y_2953_ = v___y_2977_;
v___y_2954_ = v___y_2976_;
v___y_2955_ = v___y_2978_;
v_snd_2956_ = v_snd_2982_;
v_a_2957_ = v_a_2981_;
goto v___jp_2945_;
}
else
{
lean_object* v_a_2983_; lean_object* v_a_2984_; 
lean_dec_ref(v___y_2978_);
lean_dec_ref(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec_ref(v___y_2972_);
lean_dec_ref(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v_pkg_2836_);
lean_dec_ref(v_dir_2834_);
lean_dec_ref(v_self_2833_);
lean_dec(v___x_2832_);
v_a_2983_ = lean_ctor_get(v___y_2979_, 0);
lean_inc(v_a_2983_);
v_a_2984_ = lean_ctor_get(v___y_2979_, 1);
lean_inc(v_a_2984_);
lean_dec_ref(v___y_2979_);
v_a_2873_ = v_a_2983_;
v_a_2874_ = v_a_2984_;
goto v___jp_2872_;
}
}
v___jp_2985_:
{
lean_object* v_toArray_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3017_; 
v_toArray_2998_ = lean_ctor_get(v_a_2996_, 1);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_a_2996_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v_a_2996_, 0);
lean_dec(v_unused_3018_);
v___x_3000_ = v_a_2996_;
v_isShared_3001_ = v_isSharedCheck_3017_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_toArray_2998_);
lean_dec(v_a_2996_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3017_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3002_ = lean_mk_empty_array_with_capacity(v___y_2988_);
v___x_3003_ = lean_array_get_size(v_toArray_2998_);
v___x_3004_ = lean_nat_dec_lt(v___y_2988_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_del_object(v___x_3000_);
lean_dec_ref(v_toArray_2998_);
lean_dec(v_name_2837_);
v___y_2946_ = v___y_2987_;
v___y_2947_ = v___y_2986_;
v___y_2948_ = v___y_2988_;
v___y_2949_ = v___y_2990_;
v___y_2950_ = v___y_2989_;
v___y_2951_ = v___y_2992_;
v___y_2952_ = v___y_2991_;
v___y_2953_ = v___y_2994_;
v___y_2954_ = v___y_2993_;
v___y_2955_ = v___y_2995_;
v_snd_2956_ = v___x_3002_;
v_a_2957_ = v_a_2997_;
goto v___jp_2945_;
}
else
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3008_; 
v___x_3005_ = l_Lean_NameSet_empty;
v___x_3006_ = l_Lean_NameSet_insert(v___x_3005_, v_name_2837_);
lean_inc_ref(v___x_3002_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 1, v___x_3002_);
lean_ctor_set(v___x_3000_, 0, v___x_3006_);
v___x_3008_ = v___x_3000_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3006_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v___x_3002_);
v___x_3008_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
uint8_t v___x_3009_; 
v___x_3009_ = lean_nat_dec_le(v___x_3003_, v___x_3003_);
if (v___x_3009_ == 0)
{
if (v___x_3004_ == 0)
{
lean_dec_ref(v___x_3008_);
lean_dec_ref(v_toArray_2998_);
v___y_2946_ = v___y_2987_;
v___y_2947_ = v___y_2986_;
v___y_2948_ = v___y_2988_;
v___y_2949_ = v___y_2990_;
v___y_2950_ = v___y_2989_;
v___y_2951_ = v___y_2992_;
v___y_2952_ = v___y_2991_;
v___y_2953_ = v___y_2994_;
v___y_2954_ = v___y_2993_;
v___y_2955_ = v___y_2995_;
v_snd_2956_ = v___x_3002_;
v_a_2957_ = v_a_2997_;
goto v___jp_2945_;
}
else
{
size_t v___x_3010_; size_t v___x_3011_; lean_object* v___x_3012_; 
lean_dec_ref(v___x_3002_);
v___x_3010_ = ((size_t)0ULL);
v___x_3011_ = lean_usize_of_nat(v___x_3003_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___x_2832_);
lean_inc_ref(v___y_2840_);
v___x_3012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_2998_, v___x_3010_, v___x_3011_, v___x_3008_, v___y_2840_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v_a_2997_);
lean_dec_ref(v_toArray_2998_);
v___y_2969_ = v___y_2986_;
v___y_2970_ = v___y_2987_;
v___y_2971_ = v___y_2988_;
v___y_2972_ = v___y_2989_;
v___y_2973_ = v___y_2990_;
v___y_2974_ = v___y_2991_;
v___y_2975_ = v___y_2992_;
v___y_2976_ = v___y_2993_;
v___y_2977_ = v___y_2994_;
v___y_2978_ = v___y_2995_;
v___y_2979_ = v___x_3012_;
goto v___jp_2968_;
}
}
else
{
size_t v___x_3013_; size_t v___x_3014_; lean_object* v___x_3015_; 
lean_dec_ref(v___x_3002_);
v___x_3013_ = ((size_t)0ULL);
v___x_3014_ = lean_usize_of_nat(v___x_3003_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___x_2832_);
lean_inc_ref(v___y_2840_);
v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_2998_, v___x_3013_, v___x_3014_, v___x_3008_, v___y_2840_, v___x_2832_, v___y_2842_, v___y_2843_, v___y_2844_, v_a_2997_);
lean_dec_ref(v_toArray_2998_);
v___y_2969_ = v___y_2986_;
v___y_2970_ = v___y_2987_;
v___y_2971_ = v___y_2988_;
v___y_2972_ = v___y_2989_;
v___y_2973_ = v___y_2990_;
v___y_2974_ = v___y_2991_;
v___y_2975_ = v___y_2992_;
v___y_2976_ = v___y_2993_;
v___y_2977_ = v___y_2994_;
v___y_2978_ = v___y_2995_;
v___y_2979_ = v___x_3015_;
goto v___jp_2968_;
}
}
}
}
}
v___jp_3019_:
{
if (lean_obj_tag(v___y_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v_a_3032_; 
v_a_3031_ = lean_ctor_get(v___y_3030_, 0);
lean_inc(v_a_3031_);
v_a_3032_ = lean_ctor_get(v___y_3030_, 1);
lean_inc(v_a_3032_);
lean_dec_ref(v___y_3030_);
v___y_2986_ = v___y_3021_;
v___y_2987_ = v___y_3020_;
v___y_2988_ = v___y_3022_;
v___y_2989_ = v___y_3024_;
v___y_2990_ = v___y_3023_;
v___y_2991_ = v___y_3026_;
v___y_2992_ = v___y_3025_;
v___y_2993_ = v___y_3028_;
v___y_2994_ = v___y_3027_;
v___y_2995_ = v___y_3029_;
v_a_2996_ = v_a_3031_;
v_a_2997_ = v_a_3032_;
goto v___jp_2985_;
}
else
{
lean_object* v_a_3033_; lean_object* v_a_3034_; 
lean_dec_ref(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec_ref(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec_ref(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2840_);
lean_dec(v_name_2837_);
lean_dec_ref(v_pkg_2836_);
lean_dec_ref(v_dir_2834_);
lean_dec_ref(v_self_2833_);
lean_dec(v___x_2832_);
v_a_3033_ = lean_ctor_get(v___y_3030_, 0);
lean_inc(v_a_3033_);
v_a_3034_ = lean_ctor_get(v___y_3030_, 1);
lean_inc(v_a_3034_);
lean_dec_ref(v___y_3030_);
v_a_2873_ = v_a_3033_;
v_a_2874_ = v_a_3034_;
goto v___jp_2872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v___x_3153_, lean_object* v___x_3154_, lean_object* v_self_3155_, lean_object* v_dir_3156_, lean_object* v_targetDecls_3157_, lean_object* v_pkg_3158_, lean_object* v_name_3159_, lean_object* v_config_3160_, lean_object* v_config_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v___x_3153_, v___x_3154_, v_self_3155_, v_dir_3156_, v_targetDecls_3157_, v_pkg_3158_, v_name_3159_, v_config_3160_, v_config_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3163_);
lean_dec(v_config_3161_);
lean_dec_ref(v_targetDecls_3157_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v_pkg_3179_; lean_object* v_name_3180_; lean_object* v_config_3181_; lean_object* v_keyName_3182_; lean_object* v_dir_3183_; lean_object* v_config_3184_; lean_object* v_targetDecls_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; 
v_pkg_3179_ = lean_ctor_get(v_self_3171_, 0);
lean_inc_ref(v_pkg_3179_);
v_name_3180_ = lean_ctor_get(v_self_3171_, 1);
lean_inc(v_name_3180_);
v_config_3181_ = lean_ctor_get(v_self_3171_, 2);
lean_inc(v_config_3181_);
v_keyName_3182_ = lean_ctor_get(v_pkg_3179_, 2);
v_dir_3183_ = lean_ctor_get(v_pkg_3179_, 4);
lean_inc_ref(v_dir_3183_);
v_config_3184_ = lean_ctor_get(v_pkg_3179_, 6);
lean_inc_ref(v_config_3184_);
v_targetDecls_3185_ = lean_ctor_get(v_pkg_3179_, 13);
lean_inc_ref(v_targetDecls_3185_);
v___x_3186_ = l_Lake_instDataKindDynlib;
v___x_3187_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_3180_);
lean_inc(v_keyName_3182_);
v___x_3188_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3188_, 0, v_keyName_3182_);
lean_ctor_set(v___x_3188_, 1, v_name_3180_);
v___x_3189_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3171_);
v___x_3190_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3188_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
lean_ctor_set(v___x_3190_, 2, v_self_3171_);
lean_ctor_set(v___x_3190_, 3, v___x_3187_);
lean_inc_ref(v_pkg_3179_);
v___x_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3191_, 0, v_pkg_3179_);
lean_inc(v_name_3180_);
v___f_3192_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3192_, 0, v___x_3190_);
lean_closure_set(v___f_3192_, 1, v___x_3191_);
lean_closure_set(v___f_3192_, 2, v_self_3171_);
lean_closure_set(v___f_3192_, 3, v_dir_3183_);
lean_closure_set(v___f_3192_, 4, v_targetDecls_3185_);
lean_closure_set(v___f_3192_, 5, v_pkg_3179_);
lean_closure_set(v___f_3192_, 6, v_name_3180_);
lean_closure_set(v___f_3192_, 7, v_config_3184_);
lean_closure_set(v___f_3192_, 8, v_config_3181_);
lean_inc_ref(v_a_3176_);
v___x_3193_ = l_Lake_ensureJob___redArg(v___x_3186_, v___f_3192_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3223_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
v_a_3195_ = lean_ctor_get(v___x_3193_, 1);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3197_ = v___x_3193_;
v_isShared_3198_ = v_isSharedCheck_3223_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_inc(v_a_3194_);
lean_dec(v___x_3193_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3223_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v_task_3199_; lean_object* v_kind_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3221_; 
v_task_3199_ = lean_ctor_get(v_a_3194_, 0);
v_kind_3200_ = lean_ctor_get(v_a_3194_, 1);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_a_3194_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v_a_3194_, 2);
lean_dec(v_unused_3222_);
v___x_3202_ = v_a_3194_;
v_isShared_3203_ = v_isSharedCheck_3221_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_kind_3200_);
lean_inc(v_task_3199_);
lean_dec(v_a_3194_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3221_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v_registeredJobs_3204_; lean_object* v___x_3205_; uint8_t v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; lean_object* v_job_3212_; 
v_registeredJobs_3204_ = lean_ctor_get(v_a_3176_, 3);
lean_inc(v_registeredJobs_3204_);
lean_dec_ref(v_a_3176_);
v___x_3205_ = lean_st_ref_take(v_registeredJobs_3204_);
v___x_3206_ = 1;
v___x_3207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3180_, v___x_3206_);
v___x_3208_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_3209_ = lean_string_append(v___x_3207_, v___x_3208_);
v___x_3210_ = 0;
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 2, v___x_3209_);
v_job_3212_ = v___x_3202_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_task_3199_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_kind_3200_);
lean_ctor_set(v_reuseFailAlloc_3220_, 2, v___x_3209_);
v_job_3212_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3218_; 
lean_ctor_set_uint8(v_job_3212_, sizeof(void*)*3, v___x_3210_);
lean_inc_ref(v_job_3212_);
v___x_3213_ = l_Lake_Job_toOpaque___redArg(v_job_3212_);
v___x_3214_ = lean_array_push(v___x_3205_, v___x_3213_);
v___x_3215_ = lean_st_ref_set(v_registeredJobs_3204_, v___x_3214_);
lean_dec(v_registeredJobs_3204_);
v___x_3216_ = l_Lake_Job_renew___redArg(v_job_3212_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3216_);
v___x_3218_ = v___x_3197_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3216_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v_a_3195_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
}
else
{
lean_dec(v_name_3180_);
lean_dec_ref(v_a_3176_);
return v___x_3193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_3233_, lean_object* v_a_3234_){
_start:
{
if (v_fmt_3233_ == 0)
{
lean_object* v_path_3235_; 
v_path_3235_ = lean_ctor_get(v_a_3234_, 0);
lean_inc_ref(v_path_3235_);
return v_path_3235_;
}
else
{
lean_object* v_path_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v_path_3236_ = lean_ctor_get(v_a_3234_, 0);
lean_inc_ref(v_path_3236_);
v___x_3237_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3237_, 0, v_path_3236_);
v___x_3238_ = l_Lean_Json_compress(v___x_3237_);
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_3239_, lean_object* v_a_3240_){
_start:
{
uint8_t v_fmt_boxed_3241_; lean_object* v_res_3242_; 
v_fmt_boxed_3241_ = lean_unbox(v_fmt_3239_);
v_res_3242_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_3241_, v_a_3240_);
lean_dec_ref(v_a_3240_);
return v_res_3242_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3245_; uint8_t v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___f_3245_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_3246_ = 1;
v___x_3247_ = l_Lake_instDataKindDynlib;
v___x_3248_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
v___x_3249_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3250_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
lean_ctor_set(v___x_3250_, 1, v___x_3248_);
lean_ctor_set(v___x_3250_, 2, v___x_3247_);
lean_ctor_set(v___x_3250_, 3, v___f_3245_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*4, v___x_3246_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*4 + 1, v___x_3246_);
return v___x_3250_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_3252_, lean_object* v_as_3253_, size_t v_sz_3254_, size_t v_i_3255_, lean_object* v_b_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
uint8_t v___x_3264_; 
v___x_3264_ = lean_usize_dec_lt(v_i_3255_, v_sz_3254_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; 
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec_ref(v___x_3252_);
v___x_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3265_, 0, v_b_3256_);
lean_ctor_set(v___x_3265_, 1, v___y_3262_);
return v___x_3265_;
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3267_; 
v_a_3266_ = lean_array_uget_borrowed(v_as_3253_, v_i_3255_);
lean_inc_ref(v___y_3261_);
lean_inc(v___y_3260_);
lean_inc(v___y_3259_);
lean_inc(v___y_3258_);
lean_inc_ref(v___y_3257_);
lean_inc_n(v_a_3266_, 2);
lean_inc_ref(v___x_3252_);
v___x_3267_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_3252_, v_a_3266_, v_a_3266_, v___x_3264_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v_a_3269_; lean_object* v_snd_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; size_t v___x_3273_; size_t v___x_3274_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3268_);
v_a_3269_ = lean_ctor_get(v___x_3267_, 1);
lean_inc(v_a_3269_);
lean_dec_ref(v___x_3267_);
v_snd_3270_ = lean_ctor_get(v_a_3268_, 1);
lean_inc(v_snd_3270_);
lean_dec(v_a_3268_);
v___x_3271_ = l_Lake_Job_toOpaque___redArg(v_snd_3270_);
v___x_3272_ = l_Lake_Job_mix___redArg(v_b_3256_, v___x_3271_);
v___x_3273_ = ((size_t)1ULL);
v___x_3274_ = lean_usize_add(v_i_3255_, v___x_3273_);
v_i_3255_ = v___x_3274_;
v_b_3256_ = v___x_3272_;
v___y_3262_ = v_a_3269_;
goto _start;
}
else
{
lean_object* v_a_3276_; lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec_ref(v_b_3256_);
lean_dec_ref(v___x_3252_);
v_a_3276_ = lean_ctor_get(v___x_3267_, 0);
v_a_3277_ = lean_ctor_get(v___x_3267_, 1);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3267_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_inc(v_a_3276_);
lean_dec(v___x_3267_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3276_);
lean_ctor_set(v_reuseFailAlloc_3283_, 1, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_3285_, lean_object* v_as_3286_, lean_object* v_sz_3287_, lean_object* v_i_3288_, lean_object* v_b_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
size_t v_sz_boxed_3297_; size_t v_i_boxed_3298_; lean_object* v_res_3299_; 
v_sz_boxed_3297_ = lean_unbox_usize(v_sz_3287_);
lean_dec(v_sz_3287_);
v_i_boxed_3298_ = lean_unbox_usize(v_i_3288_);
lean_dec(v_i_3288_);
v_res_3299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3285_, v_as_3286_, v_sz_boxed_3297_, v_i_boxed_3298_, v_b_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec_ref(v_as_3286_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_3300_, lean_object* v_as_3301_, size_t v_sz_3302_, size_t v_i_3303_, lean_object* v_b_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
uint8_t v___x_3312_; 
v___x_3312_ = lean_usize_dec_lt(v_i_3303_, v_sz_3302_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; 
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec_ref(v___x_3300_);
v___x_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3313_, 0, v_b_3304_);
lean_ctor_set(v___x_3313_, 1, v___y_3310_);
return v___x_3313_;
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3315_; 
v_a_3314_ = lean_array_uget_borrowed(v_as_3301_, v_i_3303_);
lean_inc_ref(v___y_3309_);
lean_inc(v___y_3308_);
lean_inc(v___y_3307_);
lean_inc(v___y_3306_);
lean_inc_ref(v___y_3305_);
lean_inc(v_a_3314_);
lean_inc_ref(v___x_3300_);
v___x_3315_ = l_Lake_Package_fetchTargetJob(v___x_3300_, v_a_3314_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v_a_3317_; lean_object* v___x_3318_; size_t v___x_3319_; size_t v___x_3320_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
v_a_3317_ = lean_ctor_get(v___x_3315_, 1);
lean_inc(v_a_3317_);
lean_dec_ref(v___x_3315_);
v___x_3318_ = l_Lake_Job_mix___redArg(v_b_3304_, v_a_3316_);
v___x_3319_ = ((size_t)1ULL);
v___x_3320_ = lean_usize_add(v_i_3303_, v___x_3319_);
v_i_3303_ = v___x_3320_;
v_b_3304_ = v___x_3318_;
v___y_3310_ = v_a_3317_;
goto _start;
}
else
{
lean_object* v_a_3322_; lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec_ref(v_b_3304_);
lean_dec_ref(v___x_3300_);
v_a_3322_ = lean_ctor_get(v___x_3315_, 0);
v_a_3323_ = lean_ctor_get(v___x_3315_, 1);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3315_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_inc(v_a_3322_);
lean_dec(v___x_3315_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3322_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_3331_, lean_object* v_as_3332_, lean_object* v_sz_3333_, lean_object* v_i_3334_, lean_object* v_b_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
size_t v_sz_boxed_3343_; size_t v_i_boxed_3344_; lean_object* v_res_3345_; 
v_sz_boxed_3343_ = lean_unbox_usize(v_sz_3333_);
lean_dec(v_sz_3333_);
v_i_boxed_3344_ = lean_unbox_usize(v_i_3334_);
lean_dec(v_i_3334_);
v_res_3345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3331_, v_as_3332_, v_sz_boxed_3343_, v_i_boxed_3344_, v_b_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
lean_dec_ref(v_as_3332_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v_pkg_3356_; lean_object* v_name_3357_; lean_object* v_config_3358_; lean_object* v_baseName_3359_; lean_object* v_keyName_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v_pkg_3356_ = lean_ctor_get(v_self_3348_, 0);
lean_inc_ref(v_pkg_3356_);
v_name_3357_ = lean_ctor_get(v_self_3348_, 1);
lean_inc(v_name_3357_);
v_config_3358_ = lean_ctor_get(v_self_3348_, 2);
lean_inc(v_config_3358_);
lean_dec_ref(v_self_3348_);
v_baseName_3359_ = lean_ctor_get(v_pkg_3356_, 1);
v_keyName_3360_ = lean_ctor_get(v_pkg_3356_, 2);
v___x_3361_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_3360_);
v___x_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3362_, 0, v_keyName_3360_);
v___x_3363_ = l_Lake_Package_keyword;
lean_inc_ref(v_pkg_3356_);
v___x_3364_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3362_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
lean_ctor_set(v___x_3364_, 2, v_pkg_3356_);
lean_ctor_set(v___x_3364_, 3, v___x_3361_);
lean_inc_ref(v_a_3349_);
lean_inc_ref(v_a_3353_);
lean_inc(v_a_3352_);
lean_inc(v_a_3351_);
lean_inc(v_a_3350_);
v___x_3365_ = lean_apply_7(v_a_3349_, v___x_3364_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, lean_box(0));
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3403_; 
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
v_a_3367_ = lean_ctor_get(v___x_3365_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3369_ = v___x_3365_;
v_isShared_3370_ = v_isSharedCheck_3403_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_inc(v_a_3366_);
lean_dec(v___x_3365_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3403_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
uint8_t v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v_needs_3375_; lean_object* v_extraDepTargets_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; uint8_t v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3390_; 
v___x_3371_ = 1;
lean_inc(v_baseName_3359_);
v___x_3372_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3359_, v___x_3371_);
v___x_3373_ = lean_unsigned_to_nat(0u);
v___x_3374_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v_needs_3375_ = lean_ctor_get(v_config_3358_, 5);
lean_inc_ref(v_needs_3375_);
v_extraDepTargets_3376_ = lean_ctor_get(v_config_3358_, 6);
lean_inc_ref(v_extraDepTargets_3376_);
lean_dec(v_config_3358_);
v___x_3377_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_3378_ = lean_string_append(v___x_3372_, v___x_3377_);
v___x_3379_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3357_, v___x_3371_);
v___x_3380_ = lean_string_append(v___x_3378_, v___x_3379_);
lean_dec_ref(v___x_3379_);
v___x_3381_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_3382_ = lean_string_append(v___x_3380_, v___x_3381_);
v___x_3383_ = 0;
v___x_3384_ = 0;
v___x_3385_ = l_Lake_BuildTrace_nil(v___x_3382_);
v___x_3386_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3386_, 0, v___x_3374_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
lean_ctor_set(v___x_3386_, 2, v___x_3373_);
lean_ctor_set_uint8(v___x_3386_, sizeof(void*)*3, v___x_3383_);
lean_ctor_set_uint8(v___x_3386_, sizeof(void*)*3 + 1, v___x_3384_);
v___x_3387_ = lean_box(0);
v___x_3388_ = lean_box(0);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 1, v___x_3386_);
lean_ctor_set(v___x_3369_, 0, v___x_3388_);
v___x_3390_ = v___x_3369_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v___x_3386_);
v___x_3390_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v_job_3393_; lean_object* v___x_3394_; size_t v_sz_3395_; size_t v___x_3396_; lean_object* v___x_3397_; 
v___x_3391_ = lean_task_pure(v___x_3390_);
v___x_3392_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_3393_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_3393_, 0, v___x_3391_);
lean_ctor_set(v_job_3393_, 1, v___x_3387_);
lean_ctor_set(v_job_3393_, 2, v___x_3392_);
lean_ctor_set_uint8(v_job_3393_, sizeof(void*)*3, v___x_3384_);
v___x_3394_ = l_Lake_Job_mix___redArg(v_job_3393_, v_a_3366_);
v_sz_3395_ = lean_array_size(v_extraDepTargets_3376_);
v___x_3396_ = ((size_t)0ULL);
lean_inc_ref(v_a_3353_);
lean_inc(v_a_3352_);
lean_inc(v_a_3351_);
lean_inc(v_a_3350_);
lean_inc_ref(v_a_3349_);
lean_inc_ref(v_pkg_3356_);
v___x_3397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_3356_, v_extraDepTargets_3376_, v_sz_3395_, v___x_3396_, v___x_3394_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3367_);
lean_dec_ref(v_extraDepTargets_3376_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v_a_3399_; size_t v_sz_3400_; lean_object* v___x_3401_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3398_);
v_a_3399_ = lean_ctor_get(v___x_3397_, 1);
lean_inc(v_a_3399_);
lean_dec_ref(v___x_3397_);
v_sz_3400_ = lean_array_size(v_needs_3375_);
v___x_3401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_3356_, v_needs_3375_, v_sz_3400_, v___x_3396_, v_a_3398_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3399_);
lean_dec_ref(v_needs_3375_);
return v___x_3401_;
}
else
{
lean_dec_ref(v_needs_3375_);
lean_dec_ref(v_pkg_3356_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
return v___x_3397_;
}
}
}
}
else
{
lean_dec(v_config_3358_);
lean_dec(v_name_3357_);
lean_dec_ref(v_pkg_3356_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
return v___x_3365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
return v_res_3412_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3414_; uint8_t v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___f_3414_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3415_ = 1;
v___x_3416_ = l_Lake_instDataKindUnit;
v___x_3417_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_3418_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3419_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
lean_ctor_set(v___x_3419_, 1, v___x_3417_);
lean_ctor_set(v___x_3419_, 2, v___x_3416_);
lean_ctor_set(v___x_3419_, 3, v___f_3414_);
lean_ctor_set_uint8(v___x_3419_, sizeof(void*)*4, v___x_3415_);
lean_ctor_set_uint8(v___x_3419_, sizeof(void*)*4 + 1, v___x_3415_);
return v___x_3419_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_3420_; 
v___x_3420_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_3421_, size_t v_sz_3422_, size_t v_i_3423_, lean_object* v_bs_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
uint8_t v___x_3432_; 
v___x_3432_ = lean_usize_dec_lt(v_i_3423_, v_sz_3422_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; 
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v_self_3421_);
v___x_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3433_, 0, v_bs_3424_);
lean_ctor_set(v___x_3433_, 1, v___y_3430_);
return v___x_3433_;
}
else
{
lean_object* v_pkg_3434_; lean_object* v_name_3435_; lean_object* v_keyName_3436_; lean_object* v_v_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v_pkg_3434_ = lean_ctor_get(v_self_3421_, 0);
v_name_3435_ = lean_ctor_get(v_self_3421_, 1);
v_keyName_3436_ = lean_ctor_get(v_pkg_3434_, 2);
v_v_3437_ = lean_array_uget_borrowed(v_bs_3424_, v_i_3423_);
lean_inc(v_name_3435_);
lean_inc(v_keyName_3436_);
v___x_3438_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3438_, 0, v_keyName_3436_);
lean_ctor_set(v___x_3438_, 1, v_name_3435_);
v___x_3439_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc(v_v_3437_);
lean_inc_ref(v_self_3421_);
v___x_3440_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3438_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
lean_ctor_set(v___x_3440_, 2, v_self_3421_);
lean_ctor_set(v___x_3440_, 3, v_v_3437_);
lean_inc_ref(v___y_3425_);
lean_inc_ref(v___y_3429_);
lean_inc(v___y_3428_);
lean_inc(v___y_3427_);
lean_inc(v___y_3426_);
v___x_3441_ = lean_apply_7(v___y_3425_, v___x_3440_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, lean_box(0));
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v_a_3443_; lean_object* v___x_3444_; lean_object* v_bs_x27_3445_; lean_object* v___x_3446_; size_t v___x_3447_; size_t v___x_3448_; lean_object* v___x_3449_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
v_a_3443_ = lean_ctor_get(v___x_3441_, 1);
lean_inc(v_a_3443_);
lean_dec_ref(v___x_3441_);
v___x_3444_ = lean_unsigned_to_nat(0u);
v_bs_x27_3445_ = lean_array_uset(v_bs_3424_, v_i_3423_, v___x_3444_);
v___x_3446_ = l_Lake_Job_toOpaque___redArg(v_a_3442_);
v___x_3447_ = ((size_t)1ULL);
v___x_3448_ = lean_usize_add(v_i_3423_, v___x_3447_);
v___x_3449_ = lean_array_uset(v_bs_x27_3445_, v_i_3423_, v___x_3446_);
v_i_3423_ = v___x_3448_;
v_bs_3424_ = v___x_3449_;
v___y_3430_ = v_a_3443_;
goto _start;
}
else
{
lean_object* v_a_3451_; lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v_bs_3424_);
lean_dec_ref(v_self_3421_);
v_a_3451_ = lean_ctor_get(v___x_3441_, 0);
v_a_3452_ = lean_ctor_get(v___x_3441_, 1);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3441_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_inc(v_a_3451_);
lean_dec(v___x_3441_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3451_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_3460_, lean_object* v_sz_3461_, lean_object* v_i_3462_, lean_object* v_bs_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
size_t v_sz_boxed_3471_; size_t v_i_boxed_3472_; lean_object* v_res_3473_; 
v_sz_boxed_3471_ = lean_unbox_usize(v_sz_3461_);
lean_dec(v_sz_3461_);
v_i_boxed_3472_ = lean_unbox_usize(v_i_3462_);
lean_dec(v_i_3462_);
v_res_3473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3460_, v_sz_boxed_3471_, v_i_boxed_3472_, v_bs_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_){
_start:
{
lean_object* v_config_3483_; lean_object* v_defaultFacets_3484_; size_t v_sz_3485_; size_t v___x_3486_; lean_object* v___x_3487_; 
v_config_3483_ = lean_ctor_get(v_self_3475_, 2);
v_defaultFacets_3484_ = lean_ctor_get(v_config_3483_, 7);
lean_inc_ref(v_defaultFacets_3484_);
v_sz_3485_ = lean_array_size(v_defaultFacets_3484_);
v___x_3486_ = ((size_t)0ULL);
v___x_3487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3475_, v_sz_3485_, v___x_3486_, v_defaultFacets_3484_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3498_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
v_a_3489_ = lean_ctor_get(v___x_3487_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3491_ = v___x_3487_;
v_isShared_3492_ = v_isSharedCheck_3498_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_inc(v_a_3488_);
lean_dec(v___x_3487_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3498_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3496_; 
v___x_3493_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_3494_ = l_Lake_Job_mixArray___redArg(v_a_3488_, v___x_3493_);
lean_dec(v_a_3488_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v___x_3494_);
v___x_3496_ = v___x_3491_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3494_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_a_3489_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
else
{
lean_object* v_a_3499_; lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
v_a_3499_ = lean_ctor_get(v___x_3487_, 0);
v_a_3500_ = lean_ctor_get(v___x_3487_, 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3487_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_inc(v_a_3499_);
lean_dec(v___x_3487_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3499_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
return v_res_3516_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3518_; uint8_t v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___f_3518_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3519_ = 1;
v___x_3520_ = l_Lake_instDataKindUnit;
v___x_3521_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_3522_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3523_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
lean_ctor_set(v___x_3523_, 1, v___x_3521_);
lean_ctor_set(v___x_3523_, 2, v___x_3520_);
lean_ctor_set(v___x_3523_, 3, v___f_3518_);
lean_ctor_set_uint8(v___x_3523_, sizeof(void*)*4, v___x_3519_);
lean_ctor_set_uint8(v___x_3523_, sizeof(void*)*4 + 1, v___x_3519_);
return v___x_3523_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_3525_, lean_object* v_v_3526_, lean_object* v_t_3527_){
_start:
{
if (lean_obj_tag(v_t_3527_) == 0)
{
lean_object* v_size_3528_; lean_object* v_k_3529_; lean_object* v_v_3530_; lean_object* v_l_3531_; lean_object* v_r_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3812_; 
v_size_3528_ = lean_ctor_get(v_t_3527_, 0);
v_k_3529_ = lean_ctor_get(v_t_3527_, 1);
v_v_3530_ = lean_ctor_get(v_t_3527_, 2);
v_l_3531_ = lean_ctor_get(v_t_3527_, 3);
v_r_3532_ = lean_ctor_get(v_t_3527_, 4);
v_isSharedCheck_3812_ = !lean_is_exclusive(v_t_3527_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3534_ = v_t_3527_;
v_isShared_3535_ = v_isSharedCheck_3812_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_r_3532_);
lean_inc(v_l_3531_);
lean_inc(v_v_3530_);
lean_inc(v_k_3529_);
lean_inc(v_size_3528_);
lean_dec(v_t_3527_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3812_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
uint8_t v___x_3536_; 
v___x_3536_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3525_, v_k_3529_);
switch(v___x_3536_)
{
case 0:
{
lean_object* v_impl_3537_; lean_object* v___x_3538_; 
lean_dec(v_size_3528_);
v_impl_3537_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3525_, v_v_3526_, v_l_3531_);
v___x_3538_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3532_) == 0)
{
lean_object* v_size_3539_; lean_object* v_size_3540_; lean_object* v_k_3541_; lean_object* v_v_3542_; lean_object* v_l_3543_; lean_object* v_r_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v_size_3539_ = lean_ctor_get(v_r_3532_, 0);
v_size_3540_ = lean_ctor_get(v_impl_3537_, 0);
lean_inc(v_size_3540_);
v_k_3541_ = lean_ctor_get(v_impl_3537_, 1);
lean_inc(v_k_3541_);
v_v_3542_ = lean_ctor_get(v_impl_3537_, 2);
lean_inc(v_v_3542_);
v_l_3543_ = lean_ctor_get(v_impl_3537_, 3);
lean_inc(v_l_3543_);
v_r_3544_ = lean_ctor_get(v_impl_3537_, 4);
lean_inc(v_r_3544_);
v___x_3545_ = lean_unsigned_to_nat(3u);
v___x_3546_ = lean_nat_mul(v___x_3545_, v_size_3539_);
v___x_3547_ = lean_nat_dec_lt(v___x_3546_, v_size_3540_);
lean_dec(v___x_3546_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3551_; 
lean_dec(v_r_3544_);
lean_dec(v_l_3543_);
lean_dec(v_v_3542_);
lean_dec(v_k_3541_);
v___x_3548_ = lean_nat_add(v___x_3538_, v_size_3540_);
lean_dec(v_size_3540_);
v___x_3549_ = lean_nat_add(v___x_3548_, v_size_3539_);
lean_dec(v___x_3548_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 3, v_impl_3537_);
lean_ctor_set(v___x_3534_, 0, v___x_3549_);
v___x_3551_ = v___x_3534_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_k_3529_);
lean_ctor_set(v_reuseFailAlloc_3552_, 2, v_v_3530_);
lean_ctor_set(v_reuseFailAlloc_3552_, 3, v_impl_3537_);
lean_ctor_set(v_reuseFailAlloc_3552_, 4, v_r_3532_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
else
{
lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3618_; 
v_isSharedCheck_3618_ = !lean_is_exclusive(v_impl_3537_);
if (v_isSharedCheck_3618_ == 0)
{
lean_object* v_unused_3619_; lean_object* v_unused_3620_; lean_object* v_unused_3621_; lean_object* v_unused_3622_; lean_object* v_unused_3623_; 
v_unused_3619_ = lean_ctor_get(v_impl_3537_, 4);
lean_dec(v_unused_3619_);
v_unused_3620_ = lean_ctor_get(v_impl_3537_, 3);
lean_dec(v_unused_3620_);
v_unused_3621_ = lean_ctor_get(v_impl_3537_, 2);
lean_dec(v_unused_3621_);
v_unused_3622_ = lean_ctor_get(v_impl_3537_, 1);
lean_dec(v_unused_3622_);
v_unused_3623_ = lean_ctor_get(v_impl_3537_, 0);
lean_dec(v_unused_3623_);
v___x_3554_ = v_impl_3537_;
v_isShared_3555_ = v_isSharedCheck_3618_;
goto v_resetjp_3553_;
}
else
{
lean_dec(v_impl_3537_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3618_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v_size_3556_; lean_object* v_size_3557_; lean_object* v_k_3558_; lean_object* v_v_3559_; lean_object* v_l_3560_; lean_object* v_r_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v_size_3556_ = lean_ctor_get(v_l_3543_, 0);
v_size_3557_ = lean_ctor_get(v_r_3544_, 0);
v_k_3558_ = lean_ctor_get(v_r_3544_, 1);
v_v_3559_ = lean_ctor_get(v_r_3544_, 2);
v_l_3560_ = lean_ctor_get(v_r_3544_, 3);
v_r_3561_ = lean_ctor_get(v_r_3544_, 4);
v___x_3562_ = lean_unsigned_to_nat(2u);
v___x_3563_ = lean_nat_mul(v___x_3562_, v_size_3556_);
v___x_3564_ = lean_nat_dec_lt(v_size_3557_, v___x_3563_);
lean_dec(v___x_3563_);
if (v___x_3564_ == 0)
{
lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3593_; 
lean_inc(v_r_3561_);
lean_inc(v_l_3560_);
lean_inc(v_v_3559_);
lean_inc(v_k_3558_);
v_isSharedCheck_3593_ = !lean_is_exclusive(v_r_3544_);
if (v_isSharedCheck_3593_ == 0)
{
lean_object* v_unused_3594_; lean_object* v_unused_3595_; lean_object* v_unused_3596_; lean_object* v_unused_3597_; lean_object* v_unused_3598_; 
v_unused_3594_ = lean_ctor_get(v_r_3544_, 4);
lean_dec(v_unused_3594_);
v_unused_3595_ = lean_ctor_get(v_r_3544_, 3);
lean_dec(v_unused_3595_);
v_unused_3596_ = lean_ctor_get(v_r_3544_, 2);
lean_dec(v_unused_3596_);
v_unused_3597_ = lean_ctor_get(v_r_3544_, 1);
lean_dec(v_unused_3597_);
v_unused_3598_ = lean_ctor_get(v_r_3544_, 0);
lean_dec(v_unused_3598_);
v___x_3566_ = v_r_3544_;
v_isShared_3567_ = v_isSharedCheck_3593_;
goto v_resetjp_3565_;
}
else
{
lean_dec(v_r_3544_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3593_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___x_3581_; lean_object* v___y_3583_; 
v___x_3568_ = lean_nat_add(v___x_3538_, v_size_3540_);
lean_dec(v_size_3540_);
v___x_3569_ = lean_nat_add(v___x_3568_, v_size_3539_);
lean_dec(v___x_3568_);
v___x_3581_ = lean_nat_add(v___x_3538_, v_size_3556_);
if (lean_obj_tag(v_l_3560_) == 0)
{
lean_object* v_size_3591_; 
v_size_3591_ = lean_ctor_get(v_l_3560_, 0);
lean_inc(v_size_3591_);
v___y_3583_ = v_size_3591_;
goto v___jp_3582_;
}
else
{
lean_object* v___x_3592_; 
v___x_3592_ = lean_unsigned_to_nat(0u);
v___y_3583_ = v___x_3592_;
goto v___jp_3582_;
}
v___jp_3570_:
{
lean_object* v___x_3574_; lean_object* v___x_3576_; 
v___x_3574_ = lean_nat_add(v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec(v___y_3572_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 4, v_r_3532_);
lean_ctor_set(v___x_3566_, 3, v_r_3561_);
lean_ctor_set(v___x_3566_, 2, v_v_3530_);
lean_ctor_set(v___x_3566_, 1, v_k_3529_);
lean_ctor_set(v___x_3566_, 0, v___x_3574_);
v___x_3576_ = v___x_3566_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3574_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_k_3529_);
lean_ctor_set(v_reuseFailAlloc_3580_, 2, v_v_3530_);
lean_ctor_set(v_reuseFailAlloc_3580_, 3, v_r_3561_);
lean_ctor_set(v_reuseFailAlloc_3580_, 4, v_r_3532_);
v___x_3576_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3578_; 
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 4, v___x_3576_);
lean_ctor_set(v___x_3554_, 3, v___y_3571_);
lean_ctor_set(v___x_3554_, 2, v_v_3559_);
lean_ctor_set(v___x_3554_, 1, v_k_3558_);
lean_ctor_set(v___x_3554_, 0, v___x_3569_);
v___x_3578_ = v___x_3554_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3569_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_k_3558_);
lean_ctor_set(v_reuseFailAlloc_3579_, 2, v_v_3559_);
lean_ctor_set(v_reuseFailAlloc_3579_, 3, v___y_3571_);
lean_ctor_set(v_reuseFailAlloc_3579_, 4, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
v___jp_3582_:
{
lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3584_ = lean_nat_add(v___x_3581_, v___y_3583_);
lean_dec(v___y_3583_);
lean_dec(v___x_3581_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 4, v_l_3560_);
lean_ctor_set(v___x_3534_, 3, v_l_3543_);
lean_ctor_set(v___x_3534_, 2, v_v_3542_);
lean_ctor_set(v___x_3534_, 1, v_k_3541_);
lean_ctor_set(v___x_3534_, 0, v___x_3584_);
v___x_3586_ = v___x_3534_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3584_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_k_3541_);
lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_v_3542_);
lean_ctor_set(v_reuseFailAlloc_3590_, 3, v_l_3543_);
lean_ctor_set(v_reuseFailAlloc_3590_, 4, v_l_3560_);
v___x_3586_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3587_; 
v___x_3587_ = lean_nat_add(v___x_3538_, v_size_3539_);
if (lean_obj_tag(v_r_3561_) == 0)
{
lean_object* v_size_3588_; 
v_size_3588_ = lean_ctor_get(v_r_3561_, 0);
lean_inc(v_size_3588_);
v___y_3571_ = v___x_3586_;
v___y_3572_ = v___x_3587_;
v___y_3573_ = v_size_3588_;
goto v___jp_3570_;
}
else
{
lean_object* v___x_3589_; 
v___x_3589_ = lean_unsigned_to_nat(0u);
v___y_3571_ = v___x_3586_;
v___y_3572_ = v___x_3587_;
v___y_3573_ = v___x_3589_;
goto v___jp_3570_;
}
}
}
}
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3604_; 
lean_del_object(v___x_3534_);
v___x_3599_ = lean_nat_add(v___x_3538_, v_size_3540_);
lean_dec(v_size_3540_);
v___x_3600_ = lean_nat_add(v___x_3599_, v_size_3539_);
lean_dec(v___x_3599_);
v___x_3601_ = lean_nat_add(v___x_3538_, v_size_3539_);
v___x_3602_ = lean_nat_add(v___x_3601_, v_size_3557_);
lean_dec(v___x_3601_);
lean_inc_ref(v_r_3532_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 4, v_r_3532_);
lean_ctor_set(v___x_3554_, 3, v_r_3544_);
lean_ctor_set(v___x_3554_, 2, v_v_3530_);
lean_ctor_set(v___x_3554_, 1, v_k_3529_);
lean_ctor_set(v___x_3554_, 0, v___x_3602_);
v___x_3604_ = v___x_3554_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_k_3529_);
lean_ctor_set(v_reuseFailAlloc_3617_, 2, v_v_3530_);
lean_ctor_set(v_reuseFailAlloc_3617_, 3, v_r_3544_);
lean_ctor_set(v_reuseFailAlloc_3617_, 4, v_r_3532_);
v___x_3604_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
v_isSharedCheck_3611_ = !lean_is_exclusive(v_r_3532_);
if (v_isSharedCheck_3611_ == 0)
{
lean_object* v_unused_3612_; lean_object* v_unused_3613_; lean_object* v_unused_3614_; lean_object* v_unused_3615_; lean_object* v_unused_3616_; 
v_unused_3612_ = lean_ctor_get(v_r_3532_, 4);
lean_dec(v_unused_3612_);
v_unused_3613_ = lean_ctor_get(v_r_3532_, 3);
lean_dec(v_unused_3613_);
v_unused_3614_ = lean_ctor_get(v_r_3532_, 2);
lean_dec(v_unused_3614_);
v_unused_3615_ = lean_ctor_get(v_r_3532_, 1);
lean_dec(v_unused_3615_);
v_unused_3616_ = lean_ctor_get(v_r_3532_, 0);
lean_dec(v_unused_3616_);
v___x_3606_ = v_r_3532_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_dec(v_r_3532_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 4, v___x_3604_);
lean_ctor_set(v___x_3606_, 3, v_l_3543_);
lean_ctor_set(v___x_3606_, 2, v_v_3542_);
lean_ctor_set(v___x_3606_, 1, v_k_3541_);
lean_ctor_set(v___x_3606_, 0, v___x_3600_);
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3600_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_k_3541_);
lean_ctor_set(v_reuseFailAlloc_3610_, 2, v_v_3542_);
lean_ctor_set(v_reuseFailAlloc_3610_, 3, v_l_3543_);
lean_ctor_set(v_reuseFailAlloc_3610_, 4, v___x_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3624_; 
v_l_3624_ = lean_ctor_get(v_impl_3537_, 3);
lean_inc(v_l_3624_);
if (lean_obj_tag(v_l_3624_) == 0)
{
lean_object* v_r_3625_; lean_object* v_k_3626_; lean_object* v_v_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3638_; 
v_r_3625_ = lean_ctor_get(v_impl_3537_, 4);
v_k_3626_ = lean_ctor_get(v_impl_3537_, 1);
v_v_3627_ = lean_ctor_get(v_impl_3537_, 2);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_impl_3537_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; lean_object* v_unused_3640_; 
v_unused_3639_ = lean_ctor_get(v_impl_3537_, 3);
lean_dec(v_unused_3639_);
v_unused_3640_ = lean_ctor_get(v_impl_3537_, 0);
lean_dec(v_unused_3640_);
v___x_3629_ = v_impl_3537_;
v_isShared_3630_ = v_isSharedCheck_3638_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_r_3625_);
lean_inc(v_v_3627_);
lean_inc(v_k_3626_);
lean_dec(v_impl_3537_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3638_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; lean_object* v___x_3633_; 
v___x_3631_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3625_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 3, v_r_3625_);
lean_ctor_set(v___x_3629_, 2, v_v_3530_);
lean_ctor_set(v___x_3629_, 1, v_k_3529_);
lean_ctor_set(v___x_3629_, 0, v___x_3538_);
v___x_3633_ = v___x_3629_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_k_3529_);
lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_v_3530_);
lean_ctor_set(v_reuseFailAlloc_3637_, 3, v_r_3625_);
lean_ctor_set(v_reuseFailAlloc_3637_, 4, v_r_3625_);
v___x_3633_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3635_; 
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 4, v___x_3633_);
lean_ctor_set(v___x_3534_, 3, v_l_3624_);
lean_ctor_set(v___x_3534_, 2, v_v_3627_);
lean_ctor_set(v___x_3534_, 1, v_k_3626_);
lean_ctor_set(v___x_3534_, 0, v___x_3631_);
v___x_3635_ = v___x_3534_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3631_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_k_3626_);
lean_ctor_set(v_reuseFailAlloc_3636_, 2, v_v_3627_);
lean_ctor_set(v_reuseFailAlloc_3636_, 3, v_l_3624_);
lean_ctor_set(v_reuseFailAlloc_3636_, 4, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
else
{
lean_object* v_r_3641_; 
v_r_3641_ = lean_ctor_get(v_impl_3537_, 4);
lean_inc(v_r_3641_);
if (lean_obj_tag(v_r_3641_) == 0)
{
lean_object* v_k_3642_; lean_object* v_v_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3666_; 
v_k_3642_ = lean_ctor_get(v_impl_3537_, 1);
v_v_3643_ = lean_ctor_get(v_impl_3537_, 2);
v_isSharedCheck_3666_ = !lean_is_exclusive(v_impl_3537_);
if (v_isSharedCheck_3666_ == 0)
{
lean_object* v_unused_3667_; lean_object* v_unused_3668_; lean_object* v_unused_3669_; 
v_unused_3667_ = lean_ctor_get(v_impl_3537_, 4);
lean_dec(v_unused_3667_);
v_unused_3668_ = lean_ctor_get(v_impl_3537_, 3);
lean_dec(v_unused_3668_);
v_unused_3669_ = lean_ctor_get(v_impl_3537_, 0);
lean_dec(v_unused_3669_);
v___x_3645_ = v_impl_3537_;
v_isShared_3646_ = v_isSharedCheck_3666_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_v_3643_);
lean_inc(v_k_3642_);
lean_dec(v_impl_3537_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3666_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v_k_3647_; lean_object* v_v_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3662_; 
v_k_3647_ = lean_ctor_get(v_r_3641_, 1);
v_v_3648_ = lean_ctor_get(v_r_3641_, 2);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_r_3641_);
if (v_isSharedCheck_3662_ == 0)
{
lean_object* v_unused_3663_; lean_object* v_unused_3664_; lean_object* v_unused_3665_; 
v_unused_3663_ = lean_ctor_get(v_r_3641_, 4);
lean_dec(v_unused_3663_);
v_unused_3664_ = lean_ctor_get(v_r_3641_, 3);
lean_dec(v_unused_3664_);
v_unused_3665_ = lean_ctor_get(v_r_3641_, 0);
lean_dec(v_unused_3665_);
v___x_3650_ = v_r_3641_;
v_isShared_3651_ = v_isSharedCheck_3662_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_v_3648_);
lean_inc(v_k_3647_);
lean_dec(v_r_3641_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3662_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3652_; lean_object* v___x_3654_; 
v___x_3652_ = lean_unsigned_to_nat(3u);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 4, v_l_3624_);
lean_ctor_set(v___x_3650_, 3, v_l_3624_);
lean_ctor_set(v___x_3650_, 2, v_v_3643_);
lean_ctor_set(v___x_3650_, 1, v_k_3642_);
lean_ctor_set(v___x_3650_, 0, v___x_3538_);
v___x_3654_ = v___x_3650_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_k_3642_);
lean_ctor_set(v_reuseFailAlloc_3661_, 2, v_v_3643_);
lean_ctor_set(v_reuseFailAlloc_3661_, 3, v_l_3624_);
lean_ctor_set(v_reuseFailAlloc_3661_, 4, v_l_3624_);
v___x_3654_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3656_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 4, v_l_3624_);
lean_ctor_set(v___x_3645_, 2, v_v_3530_);
lean_ctor_set(v___x_3645_, 1, v_k_3529_);
lean_ctor_set(v___x_3645_, 0, v___x_3538_);
v___x_3656_ = v___x_3645_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_k_3529_);
lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_v_3530_);
lean_ctor_set(v_reuseFailAlloc_3660_, 3, v_l_3624_);
lean_ctor_set(v_reuseFailAlloc_3660_, 4, v_l_3624_);
v___x_3656_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3658_; 
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 4, v___x_3656_);
lean_ctor_set(v___x_3534_, 3, v___x_3654_);
lean_ctor_set(v___x_3534_, 2, v_v_3648_);
lean_ctor_set(v___x_3534_, 1, v_k_3647_);
lean_ctor_set(v___x_3534_, 0, v___x_3652_);
v___x_3658_ = v___x_3534_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_k_3647_);
lean_ctor_set(v_reuseFailAlloc_3659_, 2, v_v_3648_);
lean_ctor_set(v_reuseFailAlloc_3659_, 3, v___x_3654_);
lean_ctor_set(v_reuseFailAlloc_3659_, 4, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
}
}
else
{
lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3670_ = lean_unsigned_to_nat(2u);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 4, v_r_3641_);
lean_ctor_set(v___x_3534_, 3, v_impl_3537_);
lean_ctor_set(v___x_3534_, 0, v___x_3670_);
v___x_3672_ = v___x_3534_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3670_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_k_3529_);
lean_ctor_set(v_reuseFailAlloc_3673_, 2, v_v_3530_);
lean_ctor_set(v_reuseFailAlloc_3673_, 3, v_impl_3537_);
lean_ctor_set(v_reuseFailAlloc_3673_, 4, v_r_3641_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3675_; 
lean_dec(v_v_3530_);
lean_dec(v_k_3529_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 2, v_v_3526_);
lean_ctor_set(v___x_3534_, 1, v_k_3525_);
v___x_3675_ = v___x_3534_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_size_3528_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_k_3525_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_v_3526_);
lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_l_3531_);
lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_r_3532_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
default: 
{
lean_object* v_impl_3677_; lean_object* v___x_3678_; 
lean_dec(v_size_3528_);
v_impl_3677_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3525_, v_v_3526_, v_r_3532_);
v___x_3678_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3531_) == 0)
{
lean_object* v_size_3679_; lean_object* v_size_3680_; lean_object* v_k_3681_; lean_object* v_v_3682_; lean_object* v_l_3683_; lean_object* v_r_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; uint8_t v___x_3687_; 
v_size_3679_ = lean_ctor_get(v_l_3531_, 0);
v_size_3680_ = lean_ctor_get(v_impl_3677_, 0);
lean_inc(v_size_3680_);
v_k_3681_ = lean_ctor_get(v_impl_3677_, 1);
lean_inc(v_k_3681_);
v_v_3682_ = lean_ctor_get(v_impl_3677_, 2);
lean_inc(v_v_3682_);
v_l_3683_ = lean_ctor_get(v_impl_3677_, 3);
lean_inc(v_l_3683_);
v_r_3684_ = lean_ctor_get(v_impl_3677_, 4);
lean_inc(v_r_3684_);
v___x_3685_ = lean_unsigned_to_nat(3u);
v___x_3686_ = lean_nat_mul(v___x_3685_, v_size_3679_);
v___x_3687_ = lean_nat_dec_lt(v___x_3686_, v_size_3680_);
lean_dec(v___x_3686_);
if (v___x_3687_ == 0)
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3691_; 
lean_dec(v_r_3684_);
lean_dec(v_l_3683_);
lean_dec(v_v_3682_);
lean_dec(v_k_3681_);
v___x_3688_ = lean_nat_add(v___x_3678_, v_size_3679_);
v___x_3689_ = lean_nat_add(v___x_3688_, v_size_3680_);
lean_dec(v_size_3680_);
lean_dec(v___x_3688_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 4, v_impl_3677_);
lean_ctor_set(v___x_3534_, 0, v___x_3689_);
v___x_3691_ = v___x_3534_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_k_3529_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v_v_3530_);
lean_ctor_set(v_reuseFailAlloc_3692_, 3, v_l_3531_);
lean_ctor_set(v_reuseFailAlloc_3692_, 4, v_impl_3677_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
else
{
lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3756_; 
v_isSharedCheck_3756_ = !lean_is_exclusive(v_impl_3677_);
if (v_isSharedCheck_3756_ == 0)
{
lean_object* v_unused_3757_; lean_object* v_unused_3758_; lean_object* v_unused_3759_; lean_object* v_unused_3760_; lean_object* v_unused_3761_; 
v_unused_3757_ = lean_ctor_get(v_impl_3677_, 4);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_impl_3677_, 3);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_impl_3677_, 2);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_impl_3677_, 1);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_impl_3677_, 0);
lean_dec(v_unused_3761_);
v___x_3694_ = v_impl_3677_;
v_isShared_3695_ = v_isSharedCheck_3756_;
goto v_resetjp_3693_;
}
else
{
lean_dec(v_impl_3677_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3756_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v_size_3696_; lean_object* v_k_3697_; lean_object* v_v_3698_; lean_object* v_l_3699_; lean_object* v_r_3700_; lean_object* v_size_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; 
v_size_3696_ = lean_ctor_get(v_l_3683_, 0);
v_k_3697_ = lean_ctor_get(v_l_3683_, 1);
v_v_3698_ = lean_ctor_get(v_l_3683_, 2);
v_l_3699_ = lean_ctor_get(v_l_3683_, 3);
v_r_3700_ = lean_ctor_get(v_l_3683_, 4);
v_size_3701_ = lean_ctor_get(v_r_3684_, 0);
v___x_3702_ = lean_unsigned_to_nat(2u);
v___x_3703_ = lean_nat_mul(v___x_3702_, v_size_3701_);
v___x_3704_ = lean_nat_dec_lt(v_size_3696_, v___x_3703_);
lean_dec(v___x_3703_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3732_; 
lean_inc(v_r_3700_);
lean_inc(v_l_3699_);
lean_inc(v_v_3698_);
lean_inc(v_k_3697_);
v_isSharedCheck_3732_ = !lean_is_exclusive(v_l_3683_);
if (v_isSharedCheck_3732_ == 0)
{
lean_object* v_unused_3733_; lean_object* v_unused_3734_; lean_object* v_unused_3735_; lean_object* v_unused_3736_; lean_object* v_unused_3737_; 
v_unused_3733_ = lean_ctor_get(v_l_3683_, 4);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_l_3683_, 3);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_l_3683_, 2);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_l_3683_, 1);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_l_3683_, 0);
lean_dec(v_unused_3737_);
v___x_3706_ = v_l_3683_;
v_isShared_3707_ = v_isSharedCheck_3732_;
goto v_resetjp_3705_;
}
else
{
lean_dec(v_l_3683_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3732_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3722_; 
v___x_3708_ = lean_nat_add(v___x_3678_, v_size_3679_);
v___x_3709_ = lean_nat_add(v___x_3708_, v_size_3680_);
lean_dec(v_size_3680_);
if (lean_obj_tag(v_l_3699_) == 0)
{
lean_object* v_size_3730_; 
v_size_3730_ = lean_ctor_get(v_l_3699_, 0);
lean_inc(v_size_3730_);
v___y_3722_ = v_size_3730_;
goto v___jp_3721_;
}
else
{
lean_object* v___x_3731_; 
v___x_3731_ = lean_unsigned_to_nat(0u);
v___y_3722_ = v___x_3731_;
goto v___jp_3721_;
}
v___jp_3710_:
{
lean_object* v___x_3714_; lean_object* v___x_3716_; 
v___x_3714_ = lean_nat_add(v___y_3712_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec(v___y_3712_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 4, v_r_3684_);
lean_ctor_set(v___x_3706_, 3, v_r_3700_);
lean_ctor_set(v___x_3706_, 2, v_v_3682_);
lean_ctor_set(v___x_3706_, 1, v_k_3681_);
lean_ctor_set(v___x_3706_, 0, v___x_3714_);
v___x_3716_ = v___x_3706_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3714_);
lean_ctor_set(v_reuseFailAlloc_3720_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3720_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3720_, 3, v_r_3700_);
lean_ctor_set(v_reuseFailAlloc_3720_, 4, v_r_3684_);
v___x_3716_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
lean_object* v___x_3718_; 
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 4, v___x_3716_);
lean_ctor_set(v___x_3694_, 3, v___y_3711_);
lean_ctor_set(v___x_3694_, 2, v_v_3698_);
lean_ctor_set(v___x_3694_, 1, v_k_3697_);
lean_ctor_set(v___x_3694_, 0, v___x_3709_);
v___x_3718_ = v___x_3694_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3709_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_k_3697_);
lean_ctor_set(v_reuseFailAlloc_3719_, 2, v_v_3698_);
lean_ctor_set(v_reuseFailAlloc_3719_, 3, v___y_3711_);
lean_ctor_set(v_reuseFailAlloc_3719_, 4, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
v___jp_3721_:
{
lean_object* v___x_3723_; lean_object* v___x_3725_; 
v___x_3723_ = lean_nat_add(v___x_3708_, v___y_3722_);
lean_dec(v___y_3722_);
lean_dec(v___x_3708_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 4, v_l_3699_);
lean_ctor_set(v___x_3534_, 0, v___x_3723_);
v___x_3725_ = v___x_3534_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_k_3529_);
lean_ctor_set(v_reuseFailAlloc_3729_, 2, v_v_3530_);
lean_ctor_set(v_reuseFailAlloc_3729_, 3, v_l_3531_);
lean_ctor_set(v_reuseFailAlloc_3729_, 4, v_l_3699_);
v___x_3725_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3726_; 
v___x_3726_ = lean_nat_add(v___x_3678_, v_size_3701_);
if (lean_obj_tag(v_r_3700_) == 0)
{
lean_object* v_size_3727_; 
v_size_3727_ = lean_ctor_get(v_r_3700_, 0);
lean_inc(v_size_3727_);
v___y_3711_ = v___x_3725_;
v___y_3712_ = v___x_3726_;
v___y_3713_ = v_size_3727_;
goto v___jp_3710_;
}
else
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_unsigned_to_nat(0u);
v___y_3711_ = v___x_3725_;
v___y_3712_ = v___x_3726_;
v___y_3713_ = v___x_3728_;
goto v___jp_3710_;
}
}
}
}
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3742_; 
lean_del_object(v___x_3534_);
v___x_3738_ = lean_nat_add(v___x_3678_, v_size_3679_);
v___x_3739_ = lean_nat_add(v___x_3738_, v_size_3680_);
lean_dec(v_size_3680_);
v___x_3740_ = lean_nat_add(v___x_3738_, v_size_3696_);
lean_dec(v___x_3738_);
lean_inc_ref(v_l_3531_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 4, v_l_3683_);
lean_ctor_set(v___x_3694_, 3, v_l_3531_);
lean_ctor_set(v___x_3694_, 2, v_v_3530_);
lean_ctor_set(v___x_3694_, 1, v_k_3529_);
lean_ctor_set(v___x_3694_, 0, v___x_3740_);
v___x_3742_ = v___x_3694_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3740_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_k_3529_);
lean_ctor_set(v_reuseFailAlloc_3755_, 2, v_v_3530_);
lean_ctor_set(v_reuseFailAlloc_3755_, 3, v_l_3531_);
lean_ctor_set(v_reuseFailAlloc_3755_, 4, v_l_3683_);
v___x_3742_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
v_isSharedCheck_3749_ = !lean_is_exclusive(v_l_3531_);
if (v_isSharedCheck_3749_ == 0)
{
lean_object* v_unused_3750_; lean_object* v_unused_3751_; lean_object* v_unused_3752_; lean_object* v_unused_3753_; lean_object* v_unused_3754_; 
v_unused_3750_ = lean_ctor_get(v_l_3531_, 4);
lean_dec(v_unused_3750_);
v_unused_3751_ = lean_ctor_get(v_l_3531_, 3);
lean_dec(v_unused_3751_);
v_unused_3752_ = lean_ctor_get(v_l_3531_, 2);
lean_dec(v_unused_3752_);
v_unused_3753_ = lean_ctor_get(v_l_3531_, 1);
lean_dec(v_unused_3753_);
v_unused_3754_ = lean_ctor_get(v_l_3531_, 0);
lean_dec(v_unused_3754_);
v___x_3744_ = v_l_3531_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_dec(v_l_3531_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 4, v_r_3684_);
lean_ctor_set(v___x_3744_, 3, v___x_3742_);
lean_ctor_set(v___x_3744_, 2, v_v_3682_);
lean_ctor_set(v___x_3744_, 1, v_k_3681_);
lean_ctor_set(v___x_3744_, 0, v___x_3739_);
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3748_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3748_, 3, v___x_3742_);
lean_ctor_set(v_reuseFailAlloc_3748_, 4, v_r_3684_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3762_; 
v_l_3762_ = lean_ctor_get(v_impl_3677_, 3);
lean_inc(v_l_3762_);
if (lean_obj_tag(v_l_3762_) == 0)
{
lean_object* v_r_3763_; lean_object* v_k_3764_; lean_object* v_v_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3788_; 
v_r_3763_ = lean_ctor_get(v_impl_3677_, 4);
v_k_3764_ = lean_ctor_get(v_impl_3677_, 1);
v_v_3765_ = lean_ctor_get(v_impl_3677_, 2);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_impl_3677_);
if (v_isSharedCheck_3788_ == 0)
{
lean_object* v_unused_3789_; lean_object* v_unused_3790_; 
v_unused_3789_ = lean_ctor_get(v_impl_3677_, 3);
lean_dec(v_unused_3789_);
v_unused_3790_ = lean_ctor_get(v_impl_3677_, 0);
lean_dec(v_unused_3790_);
v___x_3767_ = v_impl_3677_;
v_isShared_3768_ = v_isSharedCheck_3788_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_r_3763_);
lean_inc(v_v_3765_);
lean_inc(v_k_3764_);
lean_dec(v_impl_3677_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3788_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v_k_3769_; lean_object* v_v_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3784_; 
v_k_3769_ = lean_ctor_get(v_l_3762_, 1);
v_v_3770_ = lean_ctor_get(v_l_3762_, 2);
v_isSharedCheck_3784_ = !lean_is_exclusive(v_l_3762_);
if (v_isSharedCheck_3784_ == 0)
{
lean_object* v_unused_3785_; lean_object* v_unused_3786_; lean_object* v_unused_3787_; 
v_unused_3785_ = lean_ctor_get(v_l_3762_, 4);
lean_dec(v_unused_3785_);
v_unused_3786_ = lean_ctor_get(v_l_3762_, 3);
lean_dec(v_unused_3786_);
v_unused_3787_ = lean_ctor_get(v_l_3762_, 0);
lean_dec(v_unused_3787_);
v___x_3772_ = v_l_3762_;
v_isShared_3773_ = v_isSharedCheck_3784_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_v_3770_);
lean_inc(v_k_3769_);
lean_dec(v_l_3762_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3784_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
v___x_3774_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3763_, 2);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 4, v_r_3763_);
lean_ctor_set(v___x_3772_, 3, v_r_3763_);
lean_ctor_set(v___x_3772_, 2, v_v_3530_);
lean_ctor_set(v___x_3772_, 1, v_k_3529_);
lean_ctor_set(v___x_3772_, 0, v___x_3678_);
v___x_3776_ = v___x_3772_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3678_);
lean_ctor_set(v_reuseFailAlloc_3783_, 1, v_k_3529_);
lean_ctor_set(v_reuseFailAlloc_3783_, 2, v_v_3530_);
lean_ctor_set(v_reuseFailAlloc_3783_, 3, v_r_3763_);
lean_ctor_set(v_reuseFailAlloc_3783_, 4, v_r_3763_);
v___x_3776_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
lean_object* v___x_3778_; 
lean_inc(v_r_3763_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 3, v_r_3763_);
lean_ctor_set(v___x_3767_, 0, v___x_3678_);
v___x_3778_ = v___x_3767_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3678_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_k_3764_);
lean_ctor_set(v_reuseFailAlloc_3782_, 2, v_v_3765_);
lean_ctor_set(v_reuseFailAlloc_3782_, 3, v_r_3763_);
lean_ctor_set(v_reuseFailAlloc_3782_, 4, v_r_3763_);
v___x_3778_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3780_; 
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 4, v___x_3778_);
lean_ctor_set(v___x_3534_, 3, v___x_3776_);
lean_ctor_set(v___x_3534_, 2, v_v_3770_);
lean_ctor_set(v___x_3534_, 1, v_k_3769_);
lean_ctor_set(v___x_3534_, 0, v___x_3774_);
v___x_3780_ = v___x_3534_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_k_3769_);
lean_ctor_set(v_reuseFailAlloc_3781_, 2, v_v_3770_);
lean_ctor_set(v_reuseFailAlloc_3781_, 3, v___x_3776_);
lean_ctor_set(v_reuseFailAlloc_3781_, 4, v___x_3778_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
}
}
else
{
lean_object* v_r_3791_; 
v_r_3791_ = lean_ctor_get(v_impl_3677_, 4);
lean_inc(v_r_3791_);
if (lean_obj_tag(v_r_3791_) == 0)
{
lean_object* v_k_3792_; lean_object* v_v_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3804_; 
v_k_3792_ = lean_ctor_get(v_impl_3677_, 1);
v_v_3793_ = lean_ctor_get(v_impl_3677_, 2);
v_isSharedCheck_3804_ = !lean_is_exclusive(v_impl_3677_);
if (v_isSharedCheck_3804_ == 0)
{
lean_object* v_unused_3805_; lean_object* v_unused_3806_; lean_object* v_unused_3807_; 
v_unused_3805_ = lean_ctor_get(v_impl_3677_, 4);
lean_dec(v_unused_3805_);
v_unused_3806_ = lean_ctor_get(v_impl_3677_, 3);
lean_dec(v_unused_3806_);
v_unused_3807_ = lean_ctor_get(v_impl_3677_, 0);
lean_dec(v_unused_3807_);
v___x_3795_ = v_impl_3677_;
v_isShared_3796_ = v_isSharedCheck_3804_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_v_3793_);
lean_inc(v_k_3792_);
lean_dec(v_impl_3677_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3804_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3797_; lean_object* v___x_3799_; 
v___x_3797_ = lean_unsigned_to_nat(3u);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 4, v_l_3762_);
lean_ctor_set(v___x_3795_, 2, v_v_3530_);
lean_ctor_set(v___x_3795_, 1, v_k_3529_);
lean_ctor_set(v___x_3795_, 0, v___x_3678_);
v___x_3799_ = v___x_3795_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3678_);
lean_ctor_set(v_reuseFailAlloc_3803_, 1, v_k_3529_);
lean_ctor_set(v_reuseFailAlloc_3803_, 2, v_v_3530_);
lean_ctor_set(v_reuseFailAlloc_3803_, 3, v_l_3762_);
lean_ctor_set(v_reuseFailAlloc_3803_, 4, v_l_3762_);
v___x_3799_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
lean_object* v___x_3801_; 
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 4, v_r_3791_);
lean_ctor_set(v___x_3534_, 3, v___x_3799_);
lean_ctor_set(v___x_3534_, 2, v_v_3793_);
lean_ctor_set(v___x_3534_, 1, v_k_3792_);
lean_ctor_set(v___x_3534_, 0, v___x_3797_);
v___x_3801_ = v___x_3534_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3797_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_k_3792_);
lean_ctor_set(v_reuseFailAlloc_3802_, 2, v_v_3793_);
lean_ctor_set(v_reuseFailAlloc_3802_, 3, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3802_, 4, v_r_3791_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
else
{
lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3808_ = lean_unsigned_to_nat(2u);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 4, v_impl_3677_);
lean_ctor_set(v___x_3534_, 3, v_r_3791_);
lean_ctor_set(v___x_3534_, 0, v___x_3808_);
v___x_3810_ = v___x_3534_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v_k_3529_);
lean_ctor_set(v_reuseFailAlloc_3811_, 2, v_v_3530_);
lean_ctor_set(v_reuseFailAlloc_3811_, 3, v_r_3791_);
lean_ctor_set(v_reuseFailAlloc_3811_, 4, v_impl_3677_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
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
lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3813_ = lean_unsigned_to_nat(1u);
v___x_3814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set(v___x_3814_, 1, v_k_3525_);
lean_ctor_set(v___x_3814_, 2, v_v_3526_);
lean_ctor_set(v___x_3814_, 3, v_t_3527_);
lean_ctor_set(v___x_3814_, 4, v_t_3527_);
return v___x_3814_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3815_ = lean_box(1);
v___x_3816_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_3817_ = l_Lake_LeanLib_defaultFacet;
v___x_3818_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3817_, v___x_3816_, v___x_3815_);
return v___x_3818_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3819_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_3820_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_3821_ = l_Lake_LeanLib_modulesFacet;
v___x_3822_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3821_, v___x_3820_, v___x_3819_);
return v___x_3822_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3823_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_3824_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_3825_ = l_Lake_LeanLib_leanArtsFacet;
v___x_3826_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3825_, v___x_3824_, v___x_3823_);
return v___x_3826_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3827_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_3828_ = l_Lake_LeanLib_staticFacetConfig;
v___x_3829_ = l_Lake_LeanLib_staticFacet;
v___x_3830_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3829_, v___x_3828_, v___x_3827_);
return v___x_3830_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3831_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_3832_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_3833_ = l_Lake_LeanLib_staticExportFacet;
v___x_3834_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3833_, v___x_3832_, v___x_3831_);
return v___x_3834_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3835_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_3836_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_3837_ = l_Lake_LeanLib_sharedFacet;
v___x_3838_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3837_, v___x_3836_, v___x_3835_);
return v___x_3838_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3839_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_3840_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_3841_ = l_Lake_LeanLib_extraDepFacet;
v___x_3842_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3841_, v___x_3840_, v___x_3839_);
return v___x_3842_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3844_, lean_object* v_k_3845_, lean_object* v_v_3846_, lean_object* v_t_3847_, lean_object* v_hl_3848_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3845_, v_v_3846_, v_t_3847_);
return v___x_3849_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_3850_;
}
}
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Targets(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Target_Fetch(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
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
res = runtime_initialize_Lake_Util_Proc(builtin);
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
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
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
res = initialize_Lake_Util_Proc(builtin);
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
